#!/usr/bin/env python3
"""Rebuild bounded game strategies and replay the requested export in nanoda."""

import argparse
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
TWO_PLY = ("loses_in_two_iff_families", "explicit_starts", "strictMono_starts")
BUNDLES = {
    "moves": (("GameTwo",), ("move_unique", "move_exists", *TWO_PLY)),
    "seeds": (("GameTwo", "Seeds"), (
        "seed_period_coefficient", "seed_period_multiple", "seed_congruence",
        "seed_density_witness", "seed_density",
    )),
    "words": (("GameTwo", "Diamonds", "Seeds", "Words"), (
        "InversePath.lifts_loss", "inverse_word_density", "inverse_word_win_density",
    )),
    "diamonds": (("GameTwo", "Diamonds"), (
        *TWO_PLY, "losesBy_two_iff", "horizons_disjoint", "forced_outcomes_disjoint",
        "diamond_eight", "diamond_sixteen", "win_from_loss", "forced_loss_diamond_eight",
        "forced_loss_diamond_sixteen", "forced_win_from_loss",
    )),
}


if __name__ == "__main__":
    selector = argparse.ArgumentParser(add_help=False)
    selector.add_argument("--bundle", choices=BUNDLES, required=True)
    options, remaining = selector.parse_known_args()
    modules, targets = BUNDLES[options.bundle]
    command = [sys.executable, str(HERE.parents[1] / "lean" / "verify.py"),
               "--sources", str(HERE / "lean")]
    for module in modules:
        command.extend(("--module", module))
    for theorem in targets:
        command.extend(("--target", "Althofer." + theorem))
    subprocess.run([*command, *remaining], check=True)
