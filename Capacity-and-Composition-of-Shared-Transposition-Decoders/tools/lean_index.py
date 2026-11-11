#!/usr/bin/env python3
"""Regenerate this paper's imports, Lean declaration index and axiom audit."""
from pathlib import Path
import sys

PAPER_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PAPER_ROOT.parent / "tools"))
from lean_paper_index import generate

if __name__ == "__main__":
    generate(PAPER_ROOT, "SharedDecoders")
