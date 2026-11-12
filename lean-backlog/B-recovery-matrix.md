# B. Codes with a recovery matrix

## Setting

N ≥ 1 and M is an N × N matrix. A linear code C ⊆ F^N *has recovery matrix M* if M x = x for all
x in C; row p of M is then a recovery vector for the coordinate p. So C ⊆ ker(1 − M), and the three
statements bound dim ker(1 − M).

## Statements

**Theorem B1 (complex, contraction).** If ‖M x‖ ≤ ‖x‖ for all x (Euclidean norm), then
2 dim ker(1 − M) ≤ N + Re tr M.

**Theorem B2 (complex).** For every N × N complex matrix Z, |tr Z|² ≤ rank(Z) · Σ_{i,j} |Z_{ij}|².
Applied to Z = 1 − M: dim ker(1 − M) ≤ N − |N − tr M|² / ‖1 − M‖_F².

**Proposition B3 (any field in which 2 ≠ 0).** If D is a diagonal matrix with entries ±1 and
D M D = −M, then 2 dim ker(1 − M) ≤ N.

## Proofs

*B1.* Let C = ker(1 − M), D = dim C, and e_1, …, e_N an orthonormal basis whose first D vectors span
C. Then tr M = Σ_i ⟨e_i, M e_i⟩ = D + Σ_{i > D} ⟨e_i, M e_i⟩, and |⟨e_i, M e_i⟩| ≤ 1. So
Re tr M ≥ D − (N − D). ∎

*B2.* Let P be the orthogonal projector on the range of Z; it has rank r = rank Z, so
Σ_{i,j} |P_{ij}|² = tr(P*P) = tr P = r. Since P Z = Z, tr Z = tr(P Z) = Σ_{i,j} P_{ij} Z_{ji}, and by
the Cauchy–Schwarz inequality |tr Z|² ≤ r Σ_{i,j} |Z_{ij}|². ∎

*B3.* D² = 1, so D M = −M D. If M x = x then M D x = −D M x = −D x, so D maps ker(1 − M)
injectively into ker(1 + M). The two kernels meet in 0, because x = M x = −x gives 2x = 0. ∎

## Suggested route in Lean

- B1: an orthonormal basis extending one of a subspace, and the trace of a linear map as
  Σ_i ⟨e_i, M e_i⟩ over an orthonormal basis.
- B2: can also be proved without the projector: choose an orthonormal basis u_1, …, u_r of the
  range of Z; then tr Z = Σ_{k ≤ r} ⟨u_k, Z u_k⟩ and Σ_k ‖Z u_k‖² ≤ ‖Z‖_F².
- B3: pure linear algebra; `Matrix.diagonal`, `LinearMap.ker`, `Submodule.finrank_add_inf_finrank_le`
  or disjointness of the two kernels.
- These pointers to Mathlib are from memory and unchecked.

## What it is for

In a storage code on any helper relation, position p is recovered from its helpers by a recovery
vector. B1 and B2 say that a real or complex linear code whose recovery vectors are small (operator
norm at most one, or mean squared Euclidean norm at most one) has rate at most one half plus the
share of positions that recover themselves; B2 gives rate at most τ/(1 + τ) for mean squared norm
τ, with equality for pairing codes and for the single-parity codes on cliques. B3 is the exact form
of "no odd cycle in the support" and holds over finite fields of odd characteristic.
