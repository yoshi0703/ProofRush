#!/usr/bin/env python3
"""Rebuild the bounded-gap result for the four-symbol Shallit sequence."""

from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
MODULES = ("Word", "NormalIndex", "FactorCode")
TARGETS = (
    "ShallitWord.overlap_free",
    "ShallitFactorCode.factorCode_linear",
    "ShallitFactorCode.numeric_nonsingular_interval",
    "ShallitFactorCode.rational_nonsingular_interval",
)


if __name__ == "__main__":
    command = [sys.executable, str(HERE.parents[1] / "lean" / "verify.py"),
               "--sources", str(HERE / "lean")]
    for module in MODULES:
        command.extend(("--module", module))
    for name in TARGETS:
        command.extend(("--target", name))
    subprocess.run([*command, *sys.argv[1:]], check=True)
