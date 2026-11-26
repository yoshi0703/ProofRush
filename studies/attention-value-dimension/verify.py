#!/usr/bin/env python3
"""Rebuild the full attention theorem and replay the exported proof in nanoda."""

from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MODULES = (
    "Dimension", "GridSigns", "Softmax", "Chart", "Enumeration", "Bridge",
    "RootWindows", "RationalWindows", "ChartWindows", "GridBarrier", "ReadoutBarrier",
    "AttentionLower", "ParameterBounds", "HeadInterpolation", "Readout", "Radix",
    "ConstructiveUpper", "GroupedRoots", "ProfileRoots", "Symmetry", "JointDimension",
)
TARGETS = (
    "AttentionJoint.joint_dimension", "AttentionJoint.logarithmic_dimension",
    "AttentionJoint.universal_exists", "AttentionWindows.insufficient_dimension",
    "AttentionSymmetry.exists_grid_sign", "AttentionProfileRoots.threshold_attention",
    "AttentionUpper.radix_shared_attention_bits",
)

if __name__ == "__main__":
    args = [sys.executable, str(HERE.parents[1] / "lean" / "verify.py"), "--sources", str(HERE / "lean")]
    for module in MODULES:
        args.extend(["--module", module])
    for target in TARGETS:
        args.extend(["--target", target])
    subprocess.run([*args, *sys.argv[1:]], check=True)
