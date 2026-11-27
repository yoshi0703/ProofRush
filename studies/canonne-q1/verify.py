"""Rebuild each local module and check the exported Canonne Q1 proof with nanoda."""
from pathlib import Path
import re
import subprocess
import sys

STUDY = Path(__file__).resolve().parent
SOURCES = STUDY / "lean"
TARGETS = [
    "CanonneQuestionOne.uniform_characterization",
    "CanonneQuantile.finiteRate_eq_explicit_of_rational_input",
    "CanonneHeadEnvelope.CanonicalSplit.tail_root_eq_finite_formula",
    "CanonneCountable.good_test_iff_all_finite_prefix_tests",
    "CanonneQuantile.finite_rate_characterization",
]


def dependency_order(root):
    catalog = {path.stem: path for path in SOURCES.glob("*.lean")}
    ordered = []
    visited = set()

    def visit(name):
        if name in visited:
            return
        visited.add(name)
        for line in catalog[name].read_text().splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+([\w.]+)", line)
            if match and match[1] in catalog:
                visit(match[1])
        ordered.append(name)

    visit(root)
    return ordered


if __name__ == "__main__":
    args = [sys.executable, "-B", str(STUDY.parents[1] / "lean" / "verify.py"),
            "--sources", str(SOURCES)]
    for module in dependency_order("QuestionOne"):
        args.extend(["--module", module])
    for target in TARGETS:
        args.extend(["--target", target])
    subprocess.run(args + sys.argv[1:], check=True)
