# Tools of the memo

Both scripts need only the Python standard library (tested with Python 3.12) and can be run from any directory.

- `gen_rational_data.py` writes `../lean/ClassUniformMemo/RationalData.lean`, the integer data of the two rational
  codes of dimension 25, from the certificates `data/rational_a.json` and `data/rational_b.json`. It re-checks the
  data from the definition before writing. `python3 tools/gen_rational_data.py --check` writes nothing and fails if
  the Lean file is out of date. The Lean kernel checks every property of the data, so the script is not trusted.
- `lean_index.py` writes `../paper/sections/leanindex.tex` and `../lean/PaperAxioms.lean` from the memo's LaTeX
  sources. `python3 tools/lean_index.py --check` fails if a cited name does not resolve or a generated file is stale.

The certificates in `data/` are class-uniform rules over the rationals for the classes {0, 1, 3} and {2, 4, 5} of
Z/6, in the format of the parent paper's certificate with rational entries written as strings: `a[J][r]` lists the
coefficients of the decoder of class `J` for output coordinate `r`, the entry `(i, j)` at position `i * 6 + j`.
