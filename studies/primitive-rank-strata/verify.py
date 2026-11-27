#!/usr/bin/env python3
"""Replay the theorem on printed page 328 and the separate product-grid lemmas."""

from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
MODULES = (
    "CyclicBoxes",
    "Stratum105",
    "IntegerScales",
    "GapWords",
    "PublishedConjecture",
    "GridSupport",
    "StratumStudy",
)
TARGETS = (
    "Kasonyi105.page328_intersection",
    "Kasonyi105.existential_rank_refutation",
    "Kasonyi105.prime_factors_105",
    "Kasonyi105.exponent_mem_iff",
    "Kasonyi105.no_twoSparse_cover_of_ray",
    "Kasonyi105.topZero_twoSparse_eq_zero",
    "Kasonyi105.ray_word_primitive",
    "KasonyiGrid.minimum_support_from_boxes",
    "KasonyiGrid.minimum_box_support_iff_fiber",
    "KasonyiGrid.minimum_box_support_attained",
)

if __name__ == "__main__":
    runner = HERE.parents[1] / "lean" / "verify.py"
    command = [sys.executable, str(runner), "--sources", str(HERE / "lean")]
    for module in MODULES:
        command.extend(("--module", module))
    for target in TARGETS:
        command.extend(("--target", target))
    raise SystemExit(subprocess.call([*command, *sys.argv[1:]]))
