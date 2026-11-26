#!/usr/bin/env python3
"""Replay the four-strip design and bias bounds from their Lean sources."""

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile


STUDY = Path(__file__).resolve().parent
TARGETS = (
    "rounding_multiplicities", "probabilities", "no_common_unbiased",
    "endpoint_probabilities", "signed_lower", "nonnegative_lower",
    "monotone_lower", "sharp_calibrations",
)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", required=True)
    parser.add_argument("--nanoda")
    parser.add_argument("--docker-image")
    parser.add_argument("--run-dir", type=Path, help="fresh output directory")
    settings = parser.parse_args()
    if settings.run_dir is None:
        root = Path(tempfile.mkdtemp(prefix="shoreline-verification-"))
    else:
        root = settings.run_dir
        root.mkdir(parents=True, exist_ok=False)
    base = [sys.executable, str(STUDY.parents[1] / "lean" / "verify.py"),
            "--mathlib", settings.mathlib, "--sources", str(STUDY / "lean")]
    if settings.nanoda:
        base.extend(("--nanoda", settings.nanoda))
    if settings.docker_image:
        base.extend(("--docker-image", settings.docker_image))
    concrete = ["--module", "Shoreline", "--module", "EndpointBias"]
    for target in TARGETS:
        concrete.extend(("--target", f"Shoreline.{target}"))
    subprocess.run([*base, *concrete, "--run-dir", root / "shoreline"], check=True)
    subprocess.run([*base, "--module", "LinearEstimator", "--target",
                    "LinearEstimator.simultaneous_calibration", "--run-dir", root / "calibration"],
                   check=True)
