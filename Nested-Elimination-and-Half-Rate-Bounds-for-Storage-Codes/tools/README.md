# Tools

Scripts that regenerate generated material and check the computations reported in the paper. Run them from the
paper's directory (the parent of `paper/`, `lean/` and `tools/`). Each script documents its usage at its top.

## `lean_index.py`

Generates the index of Lean declarations, `paper/sections/leanindex.tex`, and the axiom check `lean/PaperAxioms.lean`
from the `\formal`, `\partformal` and `\lean` references in `paper/sections/*.tex`. Declarations are relative to the
namespace `HalfRate` and files to `lean/HalfRate/`; names from the earlier libraries (`Transpose`, `MotionDepthCodes`,
`CircularMemo`, `DirectedRecovery`) are skipped.

```sh
python3 tools/lean_index.py               # writes both files
python3 tools/lean_index.py --index-only  # writes only paper/sections/leanindex.tex
```

## `verify_remarks.py`

Exact checks, in plain Python 3 (standard library only, deterministic, a few seconds), of the computational remarks of
the section on the limits of the method and of its statements about `Cay(Z_9, {1, -1, 3})`. Every output line ends in
`OK`, and the last line gives the running time. None of the checks is used in a proof, and the Lean library does not
depend on them. Many of the checked facts are also Lean-verified (the paper says which); the script checks them
independently, on the same data as the Lean definitions.

```sh
python3 tools/verify_remarks.py
```

What it checks, by remark of the paper:

- The relation of `Cay(Z_9, {1, -1, 3})` (Proposition 7.1 and Example 7.2): no set `H` with `{} != H != Z_9` has
  properties (a) and (b) of Proposition 7.1, by exhaustion over the `2^9` subsets (the proposition is also
  Lean-verified, `no_private_piece`); the piece certificate of Example 7.2 satisfies conditions (C1) and (C2) of the definition of piece
  certificates step by step, with the stated outside parents `8`, `4`, `7`, each co-supplied; the pieces `{4}` and
  `{7,8}` complete the decomposition; the three-record global elimination certificate printed after Proposition 7.1 is
  valid.
- The relation X15 (Remark 7.3): loopless, in- and out-degrees at most three, no transitive triangle, strongly
  connected, not 2-dicolourable; its unique minimum nonempty core is the hexagon `{0,...,5}`, so no nonempty core has
  fewer than six vertices; the hexagon has no piece certificate in context `{}` with at most seven records, by an
  exhaustive search over record partitions, elimination orders and supplying records, with the steps of each outside
  parent only required to be nested (co-supplied outside parents are a special case); the three-record global
  elimination certificate printed in the paper is valid. Control: the 7-vertex piece `{0,1,2,3,6,12,14}` has a
  certificate with three records.
- The twelve chorded digon cycles of lengths 13, 15 and 16 (Remark 7.4): loopless, with the digons `v <-> v+1 (mod L)`,
  one-way chords, at most one chord into and one chord out of every vertex, no transitive triangle, no valid sweep among
  the `2L` sweeps, and a three-record elimination certificate each; the first cycle and its certificate are the ones
  printed in the paper.
- The Petersen graph (Remark 7.5): no global elimination certificate with any number of records, by an exhaustive
  search over all elimination orders that keeps the forced equalities of records in a union-find structure and prunes
  an order as soon as a forced inequality fails; the number of search nodes is printed. Control: the same search finds a
  global certificate of X15.
- The folded cubes (Remark 7.6): the binary kernel of `I + A` has dimension `N/2 + 2^(k-1)` for `k = 2, 3`, a numerical
  check of the cited formula.

## `degree_four.py`

Generates the data of `lean/HalfRate/DegreeFour.lean` (Example 7.8 of the paper): the neighbour lists of the
13-vertex graph G₁₃ (graph6 ``L?`@F@wlEcBoBo``, vertices numbered by networkx), the generator of the F₄-linear code
[I₇ | D(ω)] with symbols written as bit pairs, and the 2 × 2 recovery blocks. It checks every identity that the Lean
proof uses in exact arithmetic and prints the Lean definitions. It needs `networkx`.

```sh
python3 tools/degree_four.py
```
