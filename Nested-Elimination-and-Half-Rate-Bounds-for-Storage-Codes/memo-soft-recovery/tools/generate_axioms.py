#!/usr/bin/env python3
"""Compatibility entry point: regenerate the Lean index and full axiom audit.

Usage from any directory: python3 tools/generate_axioms.py [--check]
"""

from lean_index import main

if __name__ == "__main__":
    main()
