"""Rebuild the chosen Lean result and check its proof in a separate Rust kernel."""

import argparse
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
BUNDLES = {
    "endpoint": ("EndpointOne", "CanonneEndpoint", (
        "tv_eq_mass_difference", "one_sample_endpoint", "positive_null_with_boundary_alternative",
    )),
    "diffuse": ("DiffuseTV", "CanonneDiffuse", (
        "totalVariation_eq_suffix_mass_add_deficit_sub_overlap",
        "complement_deficit_le_coarse_tv",
        "suffix_overlap_lt_of_coarse_tv_le",
        "totalVariation_le_suffix_mass_add_offset",
        "warm_set_bounds_of_coarse_tv_le",
    )),
}


if __name__ == "__main__":
    selector = argparse.ArgumentParser(add_help=False)
    selector.add_argument("--bundle", choices=BUNDLES, required=True)
    options, remaining = selector.parse_known_args()
    module, namespace, theorems = BUNDLES[options.bundle]
    command = [sys.executable, str(HERE.parents[1] / "lean" / "verify.py"),
               "--sources", str(HERE / "lean"), "--module", module]
    for theorem in theorems:
        command.extend(("--target", f"{namespace}.{theorem}"))
    subprocess.run([*command, *remaining], check=True)
