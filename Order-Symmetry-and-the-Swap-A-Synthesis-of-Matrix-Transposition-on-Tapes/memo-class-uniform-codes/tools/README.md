# Tools of the memo

All scripts need only the Python standard library (tested with Python 3.12) and can be run from any directory.

- `gen_rational_data.py` writes `../lean/ClassUniformMemo/RationalData.lean`, the integer data of the two rational
  codes of dimension 25, from the certificates `data/rational_a.json` and `data/rational_b.json`. It re-checks the
  data from the definition before writing. `python3 tools/gen_rational_data.py --check` writes nothing and fails if
  the Lean file is out of date. The Lean kernel checks every property of the data, so the script is not trusted.
- `gen_parity_coset_data.py` writes `../lean/ClassUniformMemo/ParityCosetData.lean`, the sparse integer data of the
  parity-coset codes at d = 8, 12 and 16, from `data/parity_coset_d8.json`, `data/parity_coset_d12.json` and
  `data/parity_coset_d16.json`. It orders the variables with the entries of the two representative rows last, which
  keeps every denominator a power of 2, and re-checks the data before writing; `--check` writes nothing and fails if
  the Lean file is out of date.
- `check_certificates.py` checks the certificates in `data/` and `data/numerical/` (or the files given): that the classes partition
  Z/n, and the dimension of the code, by exact elimination over the rationals; it prints the exact excess over
  (n² + Mn)/2 and whether every decoder reads one anti-diagonal. With `--translates` it computes the intersections of
  each code with its translates and the shifts where they are smallest; with `--structure` it checks, for the
  parity-coset certificates, the values of r_s and the main rank statements in the proof of the theorem on the
  parity-coset codes. Together with
  `parity_coset_rule.py` it reproduces the numerical remark of the section on two classes, but not the searches that
  found the certificates. Each option adds about a minute for all certificates.
- `parity_coset_rule.py` builds the parity-coset rule of the section on two classes in closed form for any d = 4k,
  checks that the parity-coset certificates have exactly its decoders, and computes the dimension of its code exactly
  over the rationals, anti-diagonal by anti-diagonal, for every d = 4k with 8 ≤ d ≤ 100 (or the sizes given); with
  `--structure` it checks the values of r_s and the main rank statements in the proof of the theorem on the
  parity-coset codes. It imports
  `check_certificates.py`.
- `lean_index.py` writes `../paper/sections/leanindex.tex` and `../lean/PaperAxioms.lean` from the memo's LaTeX
  sources. `python3 tools/lean_index.py --check` fails if a cited name does not resolve or a generated file is stale.

The certificates in `data/` and `data/numerical/` are class-uniform rules over the rationals, in the format of the
parent paper's certificate with rational entries written as strings: `n` is the side length, `classes` the two classes,
`a[J][r]` the coefficients of the decoder of class `J` for output coordinate `r` (the entry `(i, j)` at position
`i * n + j`), and `dimension` the dimension of the code. `rational_a.json` and `rational_b.json` are for the classes
{0, 1, 3} and {2, 4, 5} of Z/6; `parity_coset_d*.json` for the parity-coset classes; `numerical/` holds the certificates
of the numerical remark.
