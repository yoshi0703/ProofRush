#!/usr/bin/env python3
"""Rebuild the countable-law comparison or its extremal examples."""

import argparse
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
COMPARISON_MODULES = (
    "Model", "Peetre", "Level", "Lower", "Upper", "Cutoff", "Results",
    "Source", "Comparison",
)
BUNDLES = {
    "comparison": (COMPARISON_MODULES, (
        "inverse_attained", "peetre_level_iff", "retainedLength_discardedTail",
        "canonical_two_radius", "source_equation_four", "source_equation_four_positive",
        "point_atom_example",
    )),
    "sharpness": (("Model", "Peetre", "Sharp"), (
        "halfFlat_law", "halfFlat_cut", "halfFlat_phi", "halfFlat_inverse_lower",
        "halfFlat_coefficient_constraint", "universal_coefficient_lower",
    )),
    "uniform": (("Model", "Peetre", "Uniform"), (
        "uniformLaw_law", "uniformLaw_cut", "uniformLaw_phi",
        "uniformLaw_inverse_upper", "universal_lower_coefficient_optimal",
    )),
    "extremal": (("Model", "Peetre", "Cutoff", "Sharp", "Uniform", "SameRadius", "Extremal"), (
        "cutIndex_eq_of_cut", "canonical_lower_optimal",
        "canonical_upper_optimal", "same_radius_unbounded",
    )),
}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--bundle", choices=BUNDLES, required=True)
    options, remaining = parser.parse_known_args()
    modules, targets = BUNDLES[options.bundle]
    command = [sys.executable, str(HERE.parents[1] / "lean" / "verify.py"),
               "--sources", str(HERE / "lean")]
    for module in modules:
        command.extend(("--module", module))
    for name in targets:
        command.extend(("--target", "Canonne." + name))
    subprocess.run([*command, *remaining], check=True)
