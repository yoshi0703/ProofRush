#!/usr/bin/env python3
"""Rebuild independent theorem bundles and run their exported proofs through nanoda."""
import argparse
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BUNDLES = {
    "core": (["CFGFinite", "CFGClock", "CFGOrdering"], [
        "CFGOrdering.refutes_private_weight_ordering", "CFGOrdering.integrated_terminal",
        "CFGClock.guided_score", "CFGClock.chart_rate_product", "CFGClock.chart_tendsto",
        "CFGClock.chart_toOperational", "CFGClock.terminal2_shared", "CFGClock.terminal3_shared",
        "CFGFinite.rate2_progress", "CFGFinite.rate3_progress"]),
    "limit": (["CFGFinite", "CFGLimit2"], [
        "CFGLimit2.not_proposition33_overlap_vanishes", "CFGLimit2.terminal_exact",
        "CFGLimit2.shared_mass_tends_to_one"]),
    "paths": (["CFGSelection", "CFGConstruct"], [
        "CFGSelection.tendsto_normalized_rpow", "CFGSelection.endpoint_limit",
        "CFGSelection.minimumCost_eq_zero_iff", "CFGSelection.reveal_order_leakage",
        "CFGConstruct.subset_step"]),
    "product": (["CFGRare", "CFGRareEvent"], [
        "CFGRare.normalized_classes", "CFGRare.class_nonnegative", "CFGRare.rare_initial_witness",
        "CFGRare.real_first_marker_limit", "CFGRareEvent.support_shared",
        "CFGRareEvent.rare_terminal_finite", "CFGRareEvent.rare_amplification"]),
}
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--nanoda", type=Path, required=True)
    parser.add_argument("--run-dir", type=Path, required=True)
    parser.add_argument("--docker-image")
    parser.add_argument("--bundle", choices=list(BUNDLES), action="append")
    args = parser.parse_args()
    for name in args.bundle or BUNDLES:
        modules, targets = BUNDLES[name]
        command = [sys.executable, str(HERE.parents[1] / "lean/verify.py"),
                   "--sources", str(HERE / "lean"), "--mathlib", str(args.mathlib),
                   "--nanoda", str(args.nanoda), "--run-dir", str(args.run_dir / name)]
        for module in modules:
            command += ["--module", module]
        for target in targets:
            command += ["--target", target]
        if args.docker_image:
            command += ["--docker-image", args.docker_image]
        subprocess.run(command, check=True)

if __name__ == "__main__":
    main()
