#!/usr/bin/env python3
"""Check legacy entry points against the maintained Paper 21 package.

From High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean/:
    lake env python3 ../../lean-backlog/check.py

Optional positional module names check only those modules; their dependencies
must already have been checked. Outputs stay in the package's ignored .lake.
"""
import os
from pathlib import Path
import subprocess
import sys

SOURCE = Path(__file__).resolve().parent
PACKAGE = SOURCE.parent / "Tape-Transposition-and-the-Matrix-Coding-Conjecture" / "lean"
LEGACY_PACKAGE = SOURCE.parent / "High-Rate-Separated-Storage-Codes-and-Tape-Transposition" / "lean"
CACHE = LEGACY_PACKAGE / ".lake" / "build" / "lean-backlog"
MODULES = [
    "StatementsRowSpread", "ConeCodeTransfer", "WindowAmortization", "WindowLabels",
    "WindowCounting", "WindowGuards", "WindowRows", "WindowConeWindows",
    "WindowWorkCounting", "WindowBudgets", "WindowRowCover", "WindowSpread", "RowSpreadCrux",
    "TwoSidedCodeTransfer", "NormalizedCodeTransfer", "NormalizedRateTransfer",
    "ClosureBarriers", "RectangleBarrier", "EntropyConsolidation",
    "DecoderSelection", "DecoderEntropy", "SubcodeSelection", "ConditionalSubcode",
    "ShannonCertificate", "SubcubicReuse", "FanoCertificate",
    "FanoFull", "FanoOrder", "FanoAttainment", "MacroProjection", "FanoLift",
    "GridCertificate", "GridFull", "GridOrder", "WholeRowAcyclic",
    "WindowPages", "FarClebsch", "PaleyTournament", "SameTable", "LocalRecordViews",
    "BlockIntervalWalk", "BlockCut", "BlockCodeLocal", "BlockCutPrice",
    "BlockRowGrouping", "BlockEndRows", "BlockCodeTransfer", "BlockCodeInvoice",
    "WholeRowTCC", "WeakWholeRowTCC", "FiniteWholeRowPayments", "Wall",
    "WallFarCells", "WallFarShannon", "WallBipartite", "WallPermutation",
]


def main():
    selected = sys.argv[1:] or MODULES
    unknown = set(selected) - set(MODULES)
    if unknown:
        raise SystemExit("Unknown module(s): " + ", ".join(sorted(unknown)))
    if os.environ.get("MATRIX_BACKLOG_ENV") != str(PACKAGE):
        # Re-enter Lake's current environment even when invoked from an older
        # paper's `lake env`. No dependency pin or package cache is changed.
        env = os.environ.copy()
        env.pop("LEAN_PATH", None)
        env["MATRIX_BACKLOG_ENV"] = str(PACKAGE)
        subprocess.run(["lake", "build", "MatrixCoding"], cwd=PACKAGE, env=env, check=True)
        subprocess.run(["lake", "env", sys.executable, str(Path(__file__).resolve()), *selected],
                       cwd=PACKAGE, env=env, check=True)
        return
    CACHE.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(CACHE) + os.pathsep + env.get("LEAN_PATH", "")
    def check(module, root, output_root=CACHE):
        print(f"Checking {module}", flush=True)
        output = output_root.joinpath(*module.split('.')).with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["lean", f"--root={root}", "-o", str(output),
             str(root.joinpath(*module.split('.')).with_suffix('.lean'))],
            cwd=PACKAGE, env=env, check=True,
        )
    if {"FarClebsch", "PaleyTournament"}.intersection(selected):
        # Keep the existing namespace intact: a partial namespace in CACHE
        # would shadow Paper 4's other compiled modules on LEAN_PATH.
        paper4 = SOURCE.parent / (
            "Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes"
        ) / "lean"
        check("MotionDepthCodes.Clebsch", paper4, paper4 / ".lake" / "build" / "lib" / "lean")
    for module in selected:
        check(module, SOURCE)


if __name__ == "__main__":
    main()
