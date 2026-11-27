"""Rebuild the Shiota reduction, then check its proof export with nanoda."""
import argparse
from pathlib import Path
import subprocess
import sys

STUDY = Path(__file__).resolve().parent
SOURCES = STUDY / "lean"
TARGETS = (
    "GridCover.Shiota.distinct_reduction",
    "GridCover.Shiota.repeat_reduction",
    "GridCover.Shiota.atMost_reduction",
    "GridCover.Shiota.size_bound",
    "AxisGridSource.Drawing.output_centers",
    "GridCover.distinct_verifier_spec",
    "GridCover.repeated_verifier_spec",
    "GridCover.legal_square_iff_induced",
    "GridCover.boundary_eight",
)


def module_order():
    catalog = {path.stem: path for path in SOURCES.glob("*.lean")}
    ordered = []
    seen = set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        for line in catalog[module].read_text().splitlines():
            if line.startswith("import "):
                for dependency in line.split()[1:]:
                    if dependency in catalog:
                        visit(dependency)
        ordered.append(module)

    visit("ShiotaQuestionFour")
    return ordered


if __name__ == "__main__":
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--driver", type=Path, default=STUDY.parents[1] / "lean" / "verify.py")
    known, options = parser.parse_known_args()
    command = [sys.executable, "-B", str(known.driver), "--sources", str(SOURCES)]
    for module in module_order():
        command.extend(("--module", module))
    for target in TARGETS:
        command.extend(("--target", target))
    subprocess.run(command + options, check=True)
