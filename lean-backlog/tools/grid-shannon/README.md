# Triangle-free grid Shannon certificate

The [proof note](../../notes/triangle-free-shannon-gap.md) gives residual
upper **114/5 < 23** on the 9-row, 6-column grid host. The full-host bound
is **204/5 < 41**, with a known lower code of size q³⁹. The exact Shannon
value and exact capacity are **not** determined. The paid scalar-error inequality,
residual/full upper bounds, residual triangle-freeness and exact row-order values are
**Lean-verified**. The lower code, joint-column-error price 8/15, general acyclic/order
adapter and square balancing remain written with exact checks where applicable.

## Small proof replay

Use Python 3.10 or later (the checker uses integer bit counts), without
`-O`. From the repository root:

```sh
python3 lean-backlog/tools/grid-shannon/verify_certificate.py
```

It reconstructs the grid, its 72 directed-helper automorphisms, all 18
inequalities and the integer identity `5 h(W) <= 114`. The only purchases
are three individual cells and an explicit 18-cell generator of a cross
closure. No solver, discovery generator or general row-budget DP is used.
It also checks the exact lower code, order value, absence of residual
mutual triangles and the paid coefficients 19/30, 11/30 and 8/15.

The separate [symbolic code check](../host-probe/grid_code_check.py)
verifies every recovery and parameter-extraction identity over the
integers. The formulas therefore work over every finite abelian group,
including a cyclic group of any prescribed alphabet size.

## Lean verification

```sh
python3 lean-backlog/tools/grid-shannon/generate_lean.py --check
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py \
  ShannonCertificate GridCertificate GridFull GridOrder
```

Omit `--check` to regenerate the committed certificate. The generator uses no solver;
Lean checks the actual incidences, required automorphisms, helper containments, paid
steps and integer combination. The Fano and grid modules share their generic purchase,
recovery and averaging proofs in [ShannonCertificate](../../ShannonCertificate.lean).
The full-host adapter proves |C|⁵≤|A|²⁰⁴, while the order adapter checks 512 point
subsets and one attaining order. All declarations use only standard axioms.

## Discovery replay

The generator was adapted from the preceding Fano pipeline. The full
initial grid family exceeded its 100,000-mask limit before any solve.
The one solved family is explicitly smaller: line-union row closures,
singleton point rows, their intersections, and one auxiliary meet/join
round. It has 872 orbit variables and 14,613 inequalities.

The standard-library replay reconstructs that family and verifies both
the saved rational primal and dual:

```sh
python3 lean-backlog/tools/grid-shannon/closure_relaxation.py \
  --verify lean-backlog/tools/grid-shannon/search-receipt.json
```

It checks the full saved relaxation, not the full Shannon cone. To
regenerate its one solve with SciPy installed:

```sh
python3 lean-backlog/tools/grid-shannon/closure_relaxation.py \
  --solve --output grid-reproduction.json
```

The recorded solve used SciPy 1.18.1 and NumPy 2.5.4. The generator caps
stored masks at 100,000, orbit variables at 20,000, and inequalities at
250,000. It uses a POSIX 300-second build alarm and a 300-second solver
limit. A cap, timeout or failed exact reconstruction gives no result.
`--family all-rows` reproduces the initial cap failure, without increasing
these limits. No solve or refinement followed the saved positive result.

No optimizer is needed to check the mathematical upper certificate.
