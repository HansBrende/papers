#!/usr/bin/env python3
"""Regenerate the Lean index and axiom checks. Pass --check to verify them without writing."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    earlier = root.parent / "Storage-Codes-above-Half-Rate-under-Paired-Distance-Separation"
    spec = spec_from_file_location("storage_code_lean_index", earlier / "tools" / "lean_index.py")
    if spec is None or spec.loader is None:
        raise ImportError("Cannot load the earlier paper's Lean index generator")
    indexer = module_from_spec(spec)
    spec.loader.exec_module(indexer)
    indexer.ROOT = root
    indexer.PAPER = root / "paper"
    indexer.SECTIONS = indexer.PAPER / "sections"
    indexer.INDEX = indexer.SECTIONS / "leanindex.tex"
    indexer.LEAN = root / "lean"
    indexer.AXIOMS = indexer.LEAN / "PaperAxioms.lean"
    indexer.LIBRARY = "TapeStorageRates"
    merge_depth = root.parent / "Merge-Depth-Input-Steering-and-the-Coding-Core-of-Matrix-Transposition-on-Tapes"
    indexer.LIBRARIES = [
        (indexer.LEAN / indexer.LIBRARY, "this paper's library"),
        (merge_depth / "lean" / "MergeDepth", "Paper 11's library"),
    ]
    indexer.main()


if __name__ == "__main__":
    main()
