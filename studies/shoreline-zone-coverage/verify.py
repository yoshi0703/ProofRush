"""Check the finite research claims against the pinned Lean and independent Rust kernels."""

from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
TARGETS = (
    "number_of_picks",
    "exact_a",
    "exact_b",
    "threshold_nine",
    "multiplier_floor",
    "multiplier_attains",
    "spina_direction",
)

if __name__ == "__main__":
    command = [
        sys.executable,
        str(HERE.parents[1] / "lean" / "verify.py"),
        "--sources",
        str(HERE / "lean"),
        "--module",
        "SurveyAudit",
    ]
    for target in TARGETS:
        command.extend(("--target", "TideZoneAudit." + target))
    subprocess.run(command + sys.argv[1:], check=True)
