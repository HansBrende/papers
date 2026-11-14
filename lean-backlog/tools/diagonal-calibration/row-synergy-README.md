# Exact row-synergy controls

These checks support [row spread §18](../../notes/row-spread-of-cones.md#18-signed-row-synergy-and-recovery-budgets).
They calculate entropies of the existing binary codes, not new codes or
optimal decoders. They do not perform a search or Lean verification.

From the repository root, with standard Python 3 and assertions enabled:

```sh
python3 lean-backlog/tools/diagonal-calibration/row_synergy.py --verify lean-backlog/tools/diagonal-calibration/row-synergy-receipt.json
```

The script reuses `controls.py`'s exact binary rank routine and reads
`receipt.json`'s saved fitting matrices. It constructs kernel generators,
checks their equations and independence, and compares two calculations
for every row set J of a code C = ker H:

- Row entropy: generator-projection rank, independently checked against
  `|J| − rank(H) + rank(H restricted to the complementary columns)`.
- Residual entropy: kernel dimension minus complementary projection rank,
  checked against `|J| − rank(H restricted to columns J)`.

It then checks both the increasing-row chain-rule sum and the identity
`S = 2 dim(C) − sum(row entropies) − sum(residual entropies)`, as well as
additivity over the explicitly independent displacement diagonals.
Distances are computed in the actual bipartite row-incidence graph.
The folded cubes use the same fitting operators as the existing rank
controls, at odd lengths 1, 3, 5, 7 and 9.

The compact receipt records all aggregate values, near/far contributions,
and the SHA-256 of its input certificate. Per-row and per-diagonal checks
run even though their intermediate arrays are not copied into the receipt.
Run without `--verify` to print a fresh summary; `--output PATH` writes it.

The full Clebsch code has total synergy 84: 80 from near K4 factors and
4 from its distance-five, triangle-free diagonal. This refutes a
near-clique explanation of every known contribution; it does not refute
an asymptotic bound of order d at fixed window. Independent b-lane copies
multiply the bit entropies by b; coupled vector codes are not tested here.
