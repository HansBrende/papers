# A. Decoders of bounded weight

## Setting

- d ≥ 1. A position is a pair (i, j) with i, j < d; a d × d complex matrix X is a vector indexed by
  positions.
- swap is the map X ↦ Xᵀ. For d × d matrices A, B the Kronecker product A ⊗ B acts on positions by
  X ↦ A X Bᵀ (in Lean `A ⊗ₖ B`, with entries `A i k * B j l`).
- A *contraction* is a matrix A with ‖Ax‖ ≤ ‖x‖ for all x in the Euclidean norm; equivalently
  1 − A*A is positive semidefinite, which is the Lean definition `IsContraction`.
- A d² × d² matrix K *has weight γ* (`HasWeight K γ`) if K = Σ_a c_a (A_a ⊗ B_a) for finitely many
  contractions A_a, B_a and weights c_a ≥ 0 with Σ_a c_a = γ.
- The *code* of K is C(K) = {X : Xᵀ = K X} = ker(swap − K). Put T = swap ∘ K, so that C(K) is the fixed
  space of T, and H = (T + T*)/2.

## Statements

**Lemma A1 (odd words).** Let K have weight γ and let W be a product of k matrices, each T or T*,
with k odd. Then |tr W| ≤ γ^k d.

**Theorem A2.** If K has weight γ, then (1 + γ) dim C(K) ≤ γ (d² + d). If moreover γ ≤ 1, then
2 dim C(K) ≤ d² + γ d.

**Theorem A3.** Let n₊ be the number of eigenvalues of H, with multiplicity, that are at least 1.
(i) dim C(K) ≤ n₊, for every K.
(ii) If K has weight γ and q is a real polynomial with q(−x) = −q(x) and |q(x) − clip(x)| ≤ η for
all x in [−γ, γ], where clip(x) = max(−1, min(1, x)), then
2 n₊ ≤ (1 + η) d² + (Σ_k |q_k| γ^k) d.

**Corollary A4.** For all γ ≥ 0 and η > 0 there is C such that dim C(K) ≤ (½ + η) d² + C d for
every d and every K of weight γ.

## Proofs

Facts used throughout.
- (F1) swap is a real symmetric permutation matrix and swap² = 1.
- (F2) swap (A ⊗ B) = (B ⊗ A) swap.
- (F3) tr(swap (P ⊗ Q)) = tr(PQ). Indeed the entry of swap (P ⊗ Q) at ((i, j), (i, j)) is
  P_{ji} Q_{ij}.
- (F4) (A ⊗ B)* = A* ⊗ B*, (A ⊗ B)(A′ ⊗ B′) = AA′ ⊗ BB′; products and adjoints of contractions
  are contractions; a Kronecker product of contractions is a contraction.
- (F5) |tr P| ≤ d for a d × d contraction P, because |P_{ii}| = |⟨e_i, P e_i⟩| ≤ 1.

*Proof of A1.* Say that a matrix has weight at most w if it is a nonnegative combination, with
weights of sum at most w, of Kronecker products of contractions. By (F4) this property is closed
under products (weights multiply) and adjoints, and by (F2) under conjugation by swap, which
exchanges the two factors. T = swap K and T* = K* swap = swap (swap K* swap), so each letter is swap
times a matrix of weight at most γ. Moving every swap to the left with (F2) shows that a word of
length k equals swap^k W′ with W′ of weight at most γ^k. For odd k, swap^k = swap by (F1), and by
(F3), (F4), (F5) each term c (P ⊗ Q) of W′ contributes c tr(PQ), of absolute value at most c d. ∎

*Proof of A2.* Let D = dim C(K) and let e_1, …, e_{d²} be an orthonormal basis whose first D vectors
span C(K). For i ≤ D, T e_i = e_i, so D = Σ_{i ≤ D} ⟨e_i, T e_i⟩ = Σ_a c_a Σ_{i ≤ D} ⟨e_i, Y_a e_i⟩ with
Y_a = swap (A_a ⊗ B_a), a contraction with |tr Y_a| = |tr(A_a B_a)| ≤ d. For each a,
Σ_{i ≤ D} ⟨e_i, Y_a e_i⟩ = tr Y_a − Σ_{i > D} ⟨e_i, Y_a e_i⟩ has absolute value at most d + (d² − D).
Hence D ≤ γ (d² + d − D).
If γ ≤ 1, then T is a contraction and Theorem B1 of item B gives 2D ≤ d² + Re tr T, and
tr T = Σ_a c_a tr(A_a B_a) has absolute value at most γ d. ∎

*Proof of A3.* (i) Let v_1, …, v_{d²} be an orthonormal eigenbasis of H with eigenvalues λ_i, and V
the span of the v_i with λ_i < 1; dim V = d² − n₊. A non-zero x in V has ⟨x, Hx⟩ < ‖x‖². A vector x of
C(K) has ⟨x, Hx⟩ = Re ⟨x, Tx⟩ = ‖x‖². So C(K) ∩ V = 0 and dim C(K) ≤ n₊.
(ii) T is a matrix of weight at most γ times a unitary, so ‖H‖ ≤ ‖T‖ ≤ γ and every λ_i lies in
[−γ, γ]. Since clip(λ) = 1 for λ ≥ 1 and clip ≥ −1,
tr q(H) = Σ_i q(λ_i) ≥ Σ_i clip(λ_i) − η d² ≥ n₊ − (d² − n₊) − η d².
An odd polynomial over ℝ has only odd powers. For odd k, H^k is 2^{−k} times the sum of the 2^k
words of length k in T and T*, so |tr H^k| ≤ γ^k d by A1, and tr q(H) ≤ (Σ_k |q_k| γ^k) d. ∎

*Proof of A4.* clip is continuous and odd. By the Weierstrass theorem there is a polynomial p
within 2η of clip on [−γ, γ]; its odd part q(x) = (p(x) − p(−x))/2 is within 2η of clip as well.
By A3, 2 dim C(K) ≤ 2 n₊ ≤ (1 + 2η) d² + (Σ_k |q_k| γ^k) d, and q depends on γ and η only. ∎

## Suggested route in Lean

- Prove B1 first (item B); A2 uses it.
- For A1 it may be simplest to define the predicate "weight at most w" on matrices over
  `Fin d × Fin d` and prove closure under products, adjoints and conjugation by `swapMat`, then a
  single lemma `‖trace (swapMat d * W)‖ ≤ w * d`. The word then is `swapMat ^ k * W′` by induction
  on the list.
- A2 needs an orthonormal basis adapted to a subspace and the trace as a sum of ⟨e_i, · e_i⟩ over an
  orthonormal basis. Working with `EuclideanSpace ℂ (Idx d)` and `Matrix.toEuclideanLin` may be
  easier than with `Idx d → ℂ`.
- A3 uses the spectral theorem for Hermitian matrices (`Matrix.IsHermitian.eigenvalues`,
  `Matrix.IsHermitian.spectral_theorem`); no min-max principle is needed for (i). The trace of
  `H ^ k` as the sum of the k-th powers of the eigenvalues may have to be derived from the
  diagonalization.
- A4 uses the Weierstrass theorem on an interval (`exists_polynomial_near_of_continuousOn`).
- These pointers to Mathlib are from memory and unchecked.

## What it is for

A decoder assembled from a bounded number of row and column operations of bounded norm has bounded
weight, whatever the arrangement of the operations. A4 says that such a decoder transposes at most
about half of the matrix space, on every helper relation, with no hypothesis of the kind used by
order arguments. The swap itself has weight d. The partial transposes on a tensor factor of size m
have weight m and codes of dimension (d² + m d)/2, so A3 cannot be improved to d(d+1)/2.

Numerical checks (not proofs): the identity tr T³ = Σ_{a,b,c} tr(A_c B_a A_b B_c A_a B_b); the bound
of A1 on all words of length 1, 3, 5 for random operators; A3(i) on random operators and on partial
transposes, where it holds with equality.
