#!/usr/bin/env python3
"""
Single-Writer state controller for research-harness (flock-protected).
Only the Orchestrator on `main` should invoke this script to mutate `state/backlog.json`
and `state/dead_ends.md`.
"""

import argparse
import datetime
import fcntl
import json
import os
import sys
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent.parent
STATE_DIR = ROOT_DIR / "state"
BACKLOG_PATH = STATE_DIR / "backlog.json"
DEAD_ENDS_PATH = STATE_DIR / "dead_ends.md"
LOCK_PATH = STATE_DIR / ".state.lock"

DEFAULT_BACKLOG = {
    "schema_version": 1,
    "portfolio_ratio": {"A": 0.70, "B": 0.20, "C": 0.10},
    "stop_loss": {
        "max_consecutive_empty_rounds": 3,
        "max_iterations_without_progress": 15,
    },
    "problems": [],
}


def utc_now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


class StateLock:
    def __enter__(self):
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        self._fp = open(LOCK_PATH, "w")
        fcntl.flock(self._fp.fileno(), fcntl.LOCK_EX)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        fcntl.flock(self._fp.fileno(), fcntl.LOCK_UN)
        self._fp.close()


def load_backlog() -> dict:
    if not BACKLOG_PATH.exists():
        return json.loads(json.dumps(DEFAULT_BACKLOG))
    with open(BACKLOG_PATH, "r", encoding="utf-8") as f:
        return json.load(f)


def save_backlog(data: dict) -> None:
    tmp = BACKLOG_PATH.with_suffix(".json.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.write("\n")
    os.replace(tmp, BACKLOG_PATH)


def append_dead_end(prob_id: str, reason: str, approach: str = "") -> None:
    if not DEAD_ENDS_PATH.exists():
        DEAD_ENDS_PATH.write_text("# Dead Ends & Failed Approaches Log\n\n", encoding="utf-8")
    entry = f"## [{utc_now()}] {prob_id}\n"
    if approach:
        entry += f"- **Approach**: {approach}\n"
    entry += f"- **Barrier / Reason**: {reason}\n\n"
    with open(DEAD_ENDS_PATH, "a", encoding="utf-8") as f:
        f.write(entry)


def cmd_init(_args) -> None:
    with StateLock():
        (STATE_DIR / "locks").mkdir(parents=True, exist_ok=True)
        if not BACKLOG_PATH.exists():
            save_backlog(DEFAULT_BACKLOG)
        if not DEAD_ENDS_PATH.exists():
            DEAD_ENDS_PATH.write_text(
                "# Dead Ends & Failed Approaches Log\n\n"
                "Orchestrator によって記録された失敗アプローチ・障壁・反証仮説ログ（ワーカーは読取専用）。\n\n",
                encoding="utf-8",
            )
    print("[OK] Initialized state/backlog.json and state/dead_ends.md")


def cmd_status(_args) -> None:
    with StateLock():
        data = load_backlog()
    problems = data.get("problems", [])
    counts = {}
    tier_counts = {"A": 0, "B": 0, "C": 0}
    for p in problems:
        st = p.get("status", "queued")
        counts[st] = counts.get(st, 0) + 1
        t = p.get("tier", "A")
        tier_counts[t] = tier_counts.get(t, 0) + 1
    print(json.dumps({
        "total_problems": len(problems),
        "by_status": counts,
        "by_tier": tier_counts,
        "portfolio_ratio": data.get("portfolio_ratio"),
        "stop_loss": data.get("stop_loss"),
    }, ensure_ascii=False, indent=2))


def cmd_add_problem(args) -> None:
    with StateLock():
        data = load_backlog()
        for p in data["problems"]:
            if p["id"] == args.id:
                print(f"[Error] Problem {args.id} already exists.", file=sys.stderr)
                sys.exit(1)
        data["problems"].append({
            "id": args.id,
            "title": args.title,
            "tier": args.tier,
            "source_url": args.source_url or "",
            "status": "queued",
            "statement_audited": args.audited,
            "rounds_attempted": 0,
            "consecutive_empty_rounds": 0,
            "lemmas_proven": [],
            "created_at": utc_now(),
            "updated_at": utc_now(),
        })
        save_backlog(data)
    print(f"[OK] Added problem {args.id} (Tier {args.tier})")


def cmd_record_round(args) -> None:
    report_path = Path(args.report)
    if not report_path.exists():
        print(f"[Error] Report file not found: {report_path}", file=sys.stderr)
        sys.exit(1)
    report = json.loads(report_path.read_text(encoding="utf-8"))

    with StateLock():
        data = load_backlog()
        max_empty = data.get("stop_loss", {}).get("max_consecutive_empty_rounds", 3)
        target = next((p for p in data["problems"] if p["id"] == args.id), None)
        if target is None:
            print(f"[Error] Problem {args.id} not found in backlog.", file=sys.stderr)
            sys.exit(1)

        target["rounds_attempted"] += 1
        new_lemmas = report.get("new_lemmas") or []
        status = report.get("status", "stalled")

        for de in report.get("dead_ends") or []:
            append_dead_end(args.id, str(de))

        if status == "counterexample_found":
            target["status"] = "counterexample_found"
            target["consecutive_empty_rounds"] = 0
        elif new_lemmas:
            target["lemmas_proven"].extend(new_lemmas)
            target["consecutive_empty_rounds"] = 0
            if target["status"] == "queued":
                target["status"] = "in_progress"
        elif status == "solved":
            target["status"] = "pending_verification"
            target["consecutive_empty_rounds"] = 0
        else:
            target["consecutive_empty_rounds"] += 1
            if target["consecutive_empty_rounds"] >= max_empty:
                target["status"] = "stalled"
                append_dead_end(
                    args.id,
                    f"Stop-Loss triggered: {target['consecutive_empty_rounds']} consecutive rounds without new non-trivial lemmas or counterexample.",
                )

        target["updated_at"] = utc_now()
        save_backlog(data)
        print(json.dumps(target, ensure_ascii=False, indent=2))


def cmd_mark_solved(args) -> None:
    with StateLock():
        data = load_backlog()
        target = next((p for p in data["problems"] if p["id"] == args.id), None)
        if target is None:
            print(f"[Error] Problem {args.id} not found in backlog.", file=sys.stderr)
            sys.exit(1)
        target["status"] = "solved"
        target["verified_at"] = utc_now()
        target["updated_at"] = utc_now()
        save_backlog(data)
    print(f"[OK] Marked {args.id} as solved (verified).")


def cmd_log_dead_end(args) -> None:
    with StateLock():
        append_dead_end(args.id, args.reason, args.approach or "")
    print(f"[OK] Logged dead end for {args.id}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Orchestrator state controller (flock-locked)")
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser("init", help="Initialize state directory and files").set_defaults(func=cmd_init)
    sub.add_parser("status", help="Show backlog summary").set_defaults(func=cmd_status)

    p_add = sub.add_parser("add-problem", help="Add a problem to backlog.json")
    p_add.add_argument("--id", required=True)
    p_add.add_argument("--title", required=True)
    p_add.add_argument("--tier", choices=["A", "B", "C"], required=True)
    p_add.add_argument("--source-url", default="")
    p_add.add_argument("--audited", action="store_true")
    p_add.set_defaults(func=cmd_add_problem)

    p_rec = sub.add_parser("record-round", help="Ingest worker_report.json and enforce Stop-Loss")
    p_rec.add_argument("--id", required=True)
    p_rec.add_argument("--report", required=True)
    p_rec.set_defaults(func=cmd_record_round)

    p_sol = sub.add_parser("mark-solved", help="Mark problem solved after verify_gate.sh passes")
    p_sol.add_argument("--id", required=True)
    p_sol.set_defaults(func=cmd_mark_solved)

    p_de = sub.add_parser("log-dead-end", help="Append an entry to state/dead_ends.md")
    p_de.add_argument("--id", required=True)
    p_de.add_argument("--reason", required=True)
    p_de.add_argument("--approach", default="")
    p_de.set_defaults(func=cmd_log_dead_end)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
