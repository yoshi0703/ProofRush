#!/usr/bin/env python3
"""Rebuild local Lean sources and check their exported proof with the Rust nanoda kernel."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile

MATHLIB = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
LEAN = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
GRAPH_TARGETS = {
    "RegularCliqueCover.refutes_5ed263d5": "CliqueCoverStatement.Pastorek5ed263d5",
    "RegularCliqueCover.refutes_5ed263d5_on_domain": "CliqueCoverStatement.Pastorek5ed263d5OnDomain",
}
GRAPH_STATEMENT_SHA256 = "eb5ced058e066d2584d0721aaf9972a7936ec375486c6b3381308bf62487d33a"


def run(args, **kwargs):
    try:
        return subprocess.run(args, check=True, text=True, **kwargs)
    except subprocess.CalledProcessError as exc:
        for captured in (exc.stdout, exc.stderr):
            if captured:
                print(captured, file=sys.stderr)
        raise


def digest(path):
    with path.open("rb") as stream:
        h = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def inspect_export(path, targets):
    names = {0: ""}
    theorems, axioms = set(), set()
    for line in path.open(encoding="utf-8"):
        obj = json.loads(line)
        if "in" in obj:
            part = obj.get("str", obj.get("num"))
            prefix = names[part["pre"]]
            component = str(part.get("str", part.get("i")))
            names[obj["in"]] = f"{prefix}.{component}" if prefix else component
        elif "thm" in obj:
            theorems.add(names[obj["thm"]["name"]])
        elif "axiom" in obj:
            axioms.add(names[obj["axiom"]["name"]])
    missing = set(targets) - theorems
    if missing or (axioms - AXIOMS):
        raise ValueError(f"Missing targets {missing}, unexpected axioms {axioms - AXIOMS}")
    return sorted(axioms)


def external_command(nanoda, excluded, verifier, docker_image):
    if docker_image:
        docker = shutil.which("docker")
        if not docker:
            raise RuntimeError("--docker-image requires the Docker CLI")
        return [
            docker, "run", "--rm", "--pull=never", "--network=none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges", "--user=65534:65534",
            "--mount", f"type=bind,src={nanoda},dst=/usr/local/bin/nanoda,readonly",
            "--mount", f"type=bind,src={verifier},dst=/proof,readonly",
            "--workdir=/proof", docker_image, "/usr/local/bin/nanoda", "check.json",
        ], "Docker without network, read-only proof and checker mounts"
    if platform.system() == "Darwin":
        paths = " ".join(f"(subpath {json.dumps(str(p))})" for p in excluded)
        rules = f"(version 1)(allow default)(deny network*)(deny file-write*)(deny file-read* {paths})"
        return ["/usr/bin/sandbox-exec", "-p", rules, nanoda, "check.json"], "macOS Seatbelt"
    if platform.system() == "Linux" and shutil.which("bwrap"):
        cmd = ["bwrap", "--die-with-parent", "--unshare-net", "--ro-bind", "/", "/"]
        for p in excluded:
            cmd += ["--tmpfs", str(p)]
        return cmd + [nanoda, "check.json"], "Linux bubblewrap"
    return [nanoda, "check.json"], "separate process with a clean environment"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--mathlib", required=True, type=Path, help="checkout with the pinned Mathlib cache")
    ap.add_argument("--sources", type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument("--module", action="append", dest="modules", help="source module, in build order; repeat")
    ap.add_argument("--target", action="append", dest="targets", help="theorem in the last module's environment")
    ap.add_argument("--nanoda", type=Path, help="external Rust kernel; default is the Lean release's binary")
    ap.add_argument("--docker-image", help="use an already pulled Linux image for the Rust kernel")
    ap.add_argument("--run-dir", type=Path, help="create a fresh directory here and retain the transcript and export")
    args = ap.parse_args()
    mathlib, sources = args.mathlib.resolve(), args.sources.resolve()
    modules = args.modules or ["CliqueCoverStatement", "RegularCliqueCover"]
    targets = args.targets or list(GRAPH_TARGETS)
    if any(not re.fullmatch(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", n) for n in modules + targets):
        ap.error("Invalid Lean module or theorem name")
    root = args.run_dir.resolve() if args.run_dir else Path(tempfile.mkdtemp(prefix="proofrush-"))
    if args.run_dir:
        root.mkdir(parents=True, exist_ok=False)
    build, verifier = root / "build", root / "independent"
    build.mkdir()
    verifier.mkdir()
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    observed_mathlib = run(["git", "rev-parse", "HEAD"], cwd=mathlib, capture_output=True).stdout.strip()
    if observed_mathlib != MATHLIB:
        raise ValueError(f"Expected Mathlib {MATHLIB}, got {observed_mathlib}")
    prefix = Path(run(["lake", "env", "lean", "--print-prefix"], cwd=mathlib, env=env,
                      capture_output=True).stdout.strip()).resolve()
    lean = prefix / "bin" / "lean"
    version = run([lean, "--version"], capture_output=True).stdout.strip()
    if LEAN not in version:
        raise ValueError(f"Unexpected Lean version: {version}")
    dependency_path = run(["lake", "env", "printenv", "LEAN_PATH"], cwd=mathlib, env=env,
                          capture_output=True).stdout.strip()
    env["LEAN_PATH"] = str(build) + os.pathsep + dependency_path
    report = {"lean": version, "mathlib": observed_mathlib, "targets": targets, "sources_sha256": {}}
    log = []
    for module in modules:
        relative = Path(*module.split(".")).with_suffix(".lean")
        copied = build / relative
        copied.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(sources / relative, copied)
        report["sources_sha256"][str(relative)] = digest(copied)
        if module == "CliqueCoverStatement" and report["sources_sha256"][str(relative)] != GRAPH_STATEMENT_SHA256:
            raise ValueError("The source of the frozen graph claim has changed")
        log.append(run([lean, "-DwarningAsError=true", "-o", copied.with_suffix(".olean"), relative],
                       cwd=build, env=env, capture_output=True).stdout)
    audit = build / "ProofRushAudit.lean"
    checks = [f"import {modules[-1]}"]
    for target in targets:
        if target in GRAPH_TARGETS:
            checks.append(f"example : ¬ {GRAPH_TARGETS[target]} := {target}")
    checks.extend(f"#check {n}\n#print axioms {n}" for n in targets)
    audit.write_text("\n".join(checks) + "\n")
    log.append(run([lean, audit.name], cwd=build, env=env, capture_output=True).stdout)
    (root / "lean.txt").write_text("".join(log))
    for module in modules:
        run([prefix / "bin" / "leanchecker", module], cwd=build, env=env, capture_output=True)
    export = verifier / "proof.ndjson"
    with export.open("w") as out:
        run([prefix / "bin" / "leanexport", modules[-1], "--", *targets], cwd=build, env=env, stdout=out)
    report["export_sha256"] = digest(export)
    report["exported_axioms"] = inspect_export(export, targets)
    nanoda = (args.nanoda or prefix / "bin" / "nanoda_bin").resolve()
    report["nanoda_sha256"] = digest(nanoda)
    cmd, isolation = external_command(nanoda, [sources, build, mathlib], verifier, args.docker_image)
    report["isolation"] = isolation
    if args.docker_image:
        report["docker_image"] = args.docker_image
    cfg = {"export_file_path": "proof.ndjson", "num_threads": 2, "permitted_axioms": sorted(AXIOMS),
           "unpermitted_axiom_hard_error": True, "nat_extension": True, "string_extension": True,
           "pp_to_stdout": True, "print_success_message": True}
    (verifier / "check.json").write_text(json.dumps(cfg, indent=2) + "\n")
    verdict = run(cmd, cwd=verifier, env={"PATH": os.defpath}, capture_output=True)
    if not re.search(r"Checked \d+ declarations with no errors", verdict.stdout):
        raise RuntimeError(verdict.stdout + verdict.stderr)
    (root / "nanoda.txt").write_text(verdict.stdout)
    report["independent_verdict"] = verdict.stdout.strip().splitlines()[-1]
    (root / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    print(f"Verification files: {root}")


if __name__ == "__main__":
    main()
