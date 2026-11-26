"""Run both field reconstructions, the random audit, and the Italian rounding sensitivity."""

import argparse
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from urllib.request import Request, urlopen

from adriatic import compare, get_rows
from random_audit import observations, summary


HERE = Path(__file__).resolve().parent
STUDY = HERE.parent


def sources(directory, live):
    manifest = json.loads((STUDY / "data/manifest.json").read_text())
    for filename, entry in manifest.items():
        if live:
            request = Request(
                entry["url"], headers={"User-Agent": "ProofRush research replay"}
            )
            with urlopen(request, timeout=45) as response:
                data = response.read()
        else:
            data = gzip.decompress((STUDY / "data" / (filename + ".gz")).read_bytes())
        if (
            hashlib.sha256(data).hexdigest() != entry["sha256"]
            or len(data) != entry["bytes"]
        ):
            raise ValueError(f"Source snapshot differs for {filename}")
        (directory / filename).write_bytes(data)


def joint_results(site_stats):
    probabilities = {}
    for site, record in site_stats.items():
        probabilities[site] = {
            k: Fraction(*v["within_pct"]["20"]) for k, v in record["audit"].items()
        }
    by_allocation = {
        (a, b): p * q
        for a, p in probabilities["Amanzimtoti"].items()
        for b, q in probabilities["Umhlanga"].items()
    }
    best_eight = max(p for (a, b), p in by_allocation.items() if a + b <= 8)
    qualified = {
        f"{a}+{b}": str(p)
        for (a, b), p in by_allocation.items()
        if a + b <= 9 and p >= Fraction(95, 100)
    }
    assert best_eight == Fraction(2783, 3024)
    assert qualified == {"3+6": "23/24", "4+5": "25289/26460"}
    return {
        "best_at_eight_or_fewer": str(best_eight),
        "qualified_at_nine_or_fewer": qualified,
    }


def replay(directory):
    independent = json.loads(
        subprocess.check_output(
            [sys.executable, "-B", str(HERE / "tide_zone_coverage.py"), str(directory)],
            text=True,
        )
    )
    field = {}
    for key, method, subtotals in (
        ("items", "item_rows", False),
        ("material_subtotals", "reported_material_subtotals", True),
    ):
        site_stats = {
            site: summary(rows)
            for site, rows in observations(directory, subtotals).items()
        }
        for site, data in site_stats.items():
            other = independent[method][site]
            assert (other["upper_items"], other["whole_items"]) == (
                data["upper"],
                data["whole"],
            )
            assert (
                other["fixed_multiplier"]["exact_worst_error"] == data["minimax_error"]
            )
            assert [r["dates"] for r in other["adjacent_sign_reversals"]] == data[
                "sign_reversals"
            ]
        assert sum(len(v["sign_reversals"]) for v in site_stats.values()) == 5
        field[key] = {"sites": site_stats, "joint_design": joint_results(site_stats)}
    item = field["items"]["sites"]
    assert [r[2] for r in item["Amanzimtoti"]["days"]] == [
        92,
        57,
        97,
        119,
        105,
        259,
        392,
        225,
        314,
        271,
    ]
    assert [r[2] for r in item["Umhlanga"]["days"]] == [
        5,
        20,
        62,
        27,
        245,
        223,
        69,
        153,
        305,
    ]
    assert item["Umhlanga"]["minimax_error"] == "605/1047"
    assert independent["daily_zone_totals_disagreeing"] == 15
    rows = get_rows(directory / "water-17-02173.xml")
    pairs = compare(rows)
    reversed_changes = [p for p in pairs if p["robust_sign_reversal"]]
    assert len(pairs) == 8 and len(reversed_changes) == 1
    spina = reversed_changes[0]
    assert spina["site"] == "Spina" and spina["whole_delta"] == [74]
    assert spina["inland_change_range"] == [-47, -41]
    return {
        "south_africa": field,
        "italy": {"tables": rows, "comparisons": pairs},
        "category_reconstruction": independent,
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--live",
        action="store_true",
        help="download and hash-check all three sources again",
    )
    ap.add_argument(
        "--out",
        type=Path,
        help="write the complete daily, seasonal and allocation tables",
    )
    args = ap.parse_args()
    with TemporaryDirectory() as tmp:
        directory = Path(tmp)
        sources(directory, args.live)
        result = replay(directory)
    if args.out:
        args.out.write_text(
            json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
        )
    print(
        "19 daily removals, 5/17 reversals; best eight audits 2783/3024; nine at 3+6 or 4+5."
    )
    print("8 seasonal comparisons, Spina +74 across the beach, -47 to -41 inland.")
