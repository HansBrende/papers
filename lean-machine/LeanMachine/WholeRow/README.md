# Whole-row recovery codes

Formalization of [backlog C1–C2](../../../lean-backlog/C-second-rule.md), over every field,
including zero-dimensional matrices. The original C2 statement follows directly with its
original definitions and hypotheses.

- [`Basic.lean`](Basic.lean): the recovery code, known rows, completed columns, frontier
  columns, and the necessary constraints on a row after all earlier rows vanish.
- [`Bounds.lean`](Bounds.lean): the original C2 theorem, `finrank_rowCode_le`, and
  `finrank_rowCode_le_local`. The latter applies the second rule whenever at least one
  current frontier block is invertible, while permitting all other blocks to be singular.
- [`Rank.lean`](Rank.lean): the actual stacked frontier matrix and C1,
  `finrank_rowCode_le_rank`, which retains the joint rank without invertibility assumptions.

For row order σ, let A_t be the preceding rows, B_t the completed columns, and F_t the frontier.
The stacked matrix has entries `Y_t((r,i),j) = (M_{r,σ(t)})_{ij}` for r ∈ F_t, i ∈ A_t and
j ∉ B_t. C1 gives

$$
\dim C\le\sum_t(d-|B_t|-\operatorname{rank}Y_t).
$$

For C2, an invertible frontier block gives an independent bound of d − |A_t| on the current
row's conditional dimension. Combine it with d − |B_t|. The local version uses
`invertibleFrontier` in place of the entire frontier; all-invertible blocks recover C2 exactly.

The common dimension argument is
[`SequentialDimension.finrank_le_sum_of_prefix`](../SequentialDimension.lean): local constraints
need hold only when preceding coordinates vanish. Linear projections onto the conditional
spaces give an injective record. This is a dimension argument, with no runtime assertion.
The coordinate bounds reuse
[`FiniteProjection.finrank_le_compl_of_injective`](../FiniteProjection.lean); C1 then uses
Mathlib's rank–nullity identity. The rank and local-invertibility results allow arbitrary finite
ordered index types, as well as `Fin d`.

These results constrain the stated class of linear whole-row decoders. The code does not
assert that arbitrary tape transposers yield such decoders.

From `lean-machine/`:

```sh
lake build LeanMachine.WholeRow.Rank
lake build
lake env lean Axioms.lean
```

Every exported theorem is included in `Axioms.lean` and depends only on the standard axioms.
Both C1 and C2 are fully formalized.
