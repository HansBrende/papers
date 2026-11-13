# D. Comparison bounds over every field, a Frobenius form of A4, and the fixed-term problem

**Status:** open (added 12 November 2026, evening). Statements typecheck in
[`StatementsD.lean`](StatementsD.lean) with seven `sorry` obligations (D0–D6). The proofs below are
complete and short. Exact checks over GF(101) and GF(2) were run on all of D0–D4. Nothing here is
refereed. The two problems at the end are open research questions, not backlog obligations.

## Setting

A decoder is a d² × d² matrix K acting on d × d matrices; a Kronecker product A ⊗ B acts by
X ↦ A X Bᵀ. The code of K is C(K) = {X : Xᵀ = K X} and D(K) is its dimension. Everything in D0–D4 and D6
holds over an arbitrary field, characteristic two included.

## Statements and proofs

**D0 (two base changes).** For invertible P, Q: D((Q ⊗ P) K (P⁻¹ ⊗ Q⁻¹)) = D(K).
For K = Σ_a A_a ⊗ B_a the new operator is Σ_a Q A_a P⁻¹ ⊗ P B_a Q⁻¹.

*Proof.* Write K′ for the new operator. If Xᵀ = K X then Y = (P ⊗ Q) X, that is Y = P X Qᵀ, satisfies
Yᵀ = Q Xᵀ Pᵀ = (Q ⊗ P)(K X) = K′ Y. The map X ↦ Y is invertible and the argument is symmetric. ∎

**D1 (two codes).** D(K) + D(K′) ≤ d² + dim ker(K − K′).

*Proof.* On C(K) ∩ C(K′) we have K X = Xᵀ = K′ X, so the intersection lies in ker(K − K′), and
dim(U ∩ V) ≥ dim U + dim V − d². ∎

**D2 (against a pairing operator).** For invertible G: 2 D(K) ≤ d(d + 1) + 2 dim ker(K + G ⊗ G⁻¹).

*Proof.* Let K′ = −(G ⊗ G⁻¹). Its code is {X : Xᵀ = −G X G⁻ᵀ} = {X : (G X)ᵀ = −G X}, the image under G⁻¹ of the
matrices Y with Yᵀ = −Y. That space has dimension at least d(d − 1)/2 over every field (it contains the
alternating matrices; in characteristic two it is the symmetric matrices). Apply D1. ∎

**D3 (triangle).** 2 D(K) ≤ d(d − 1) + 2 dim{X upper triangular : (K X)_{ij} = δ_{ij} X_{ii} for all i ≤ j}.
In Lean the space on the right is the kernel of `triangleMat K`.

*Proof.* The upper triangular matrices (diagonal included) have codimension d(d − 1)/2, so the upper
triangular codewords have dimension at least D(K) − d(d − 1)/2. For such X, K X = Xᵀ is lower triangular
with the same diagonal, which is the displayed condition. ∎

By D0 the bound may be applied after any two base changes.

**D4 (compression).** For every d × d matrix E: D(K) ≤ D((1 ⊗ E) K (E ⊗ 1)) + d · rank(1 − E).
For K = Σ_a A_a ⊗ B_a the compressed operator is Σ_a A_a E ⊗ E B_a.

*Proof.* The matrices X with E X = X form the kernel of (1 − E) ⊗ 1, of codimension d · rank(1 − E). For a
codeword X with E X = X: (1 ⊗ E) K (E ⊗ 1) X = (1 ⊗ E)(K X) = (1 ⊗ E) Xᵀ = Xᵀ Eᵀ = (E X)ᵀ = Xᵀ. ∎

**D5 (Frobenius form of A4; ℂ).** For every M, κ ≥ 0 and η > 0 there is C such that for every d and all
A_a, B_a (a < M) with Σ_a (‖A_a‖_F² + ‖B_a‖_F²) ≤ κ d: D(Σ_a A_a ⊗ B_a) ≤ (1/2 + η) d² + C d.

*Proof.* Let Q = Σ_a (A_aᴴ A_a + B_a B_aᴴ), positive semidefinite of trace at most κ d, and Λ = 2κ/η. Let E be the
orthogonal projector onto the span of the eigenvectors of Q with eigenvalue at most Λ; then
rank(1 − E) ≤ κ d/Λ = η d/2. For every a, (A_a E)ᴴ(A_a E) = E A_aᴴ A_a E ≤ E Q E ≤ Λ, and (E B_a)(E B_a)ᴴ ≤ E Q E ≤ Λ, so
A_a E/√Λ and E B_a/√Λ are contractions and the compressed operator has weight MΛ in the sense of item A.
By D4 and A4 (`exists_linear_excess` with η/2): D ≤ (1/2 + η/2) d² + C′ d + η d²/2. ∎

*Suggested route.* Avoid the spectral theorem if convenient: any orthogonal projector E with
E Q E ≤ Λ and rank(1 − E) ≤ tr(Q)/Λ will do, and A4's own proof already has the Hermitian eigenbasis
lemmas (`HermitianSpectrum`).

**D6.** Problem S for M terms over F implies Problem R for M terms over F (definitions below; by D2).

## What D5 adds

Item A needs operator norms. A whole-row decoder that uses boundedly many distinct blocks N of
bounded norm, on a row relation of bounded window w, is K = Σ_N P_N ⊗ N with P_N the 0/1 pattern of the
pairs (column, helper row) that use N. The operator norm of P_N is unbounded when one row helps many
columns; its Frobenius norm is at most √(w d) always, and ‖N‖_F² ≤ ‖N‖² d. So D5 gives rate 1/2 + o(1) for
every such decoder, with no condition on the relation.

## The open problem

Over a finite field "weight" has no meaning (a bounded-weight rational lift can be rescaled without
changing its reduction). What survives is a bound on the number of terms.

**Problem R.** For fixed M and a field F: is D(Σ_{a<M} A_a ⊗ B_a) ≤ (1/2 + η) d² + C(η) d for all d and all
factors? (`ProblemR F M`.)

**Problem S.** For fixed M and F: is there C such that every K = Σ_{a<M} A_a ⊗ B_a has an invertible G with
dim ker(K + G ⊗ G⁻¹) ≤ C d? (`ProblemS F M`; over a small field G may be taken over an extension, since D
does not change.)

What is known to me:

- R is open over ℂ as well; item A is its slice of bounded norm and D5 its slice of bounded mean
  square norm. A counterexample over ℂ reduces to one over a finite extension of GF(p) for almost
  all p.
- M ≤ 2: D ≤ d(d + 1)/2 over every field (paper 17, two terms). For every M: D ≤ (1 − 1/(2M)) d² + d/2 by the
  order bound (the term d/2 was missing here until 13 November 2026; noted by GPT-6 Astra). Three real terms exceed d(d + 1)/2 at d = 4 and d = 6 (11 and 24, numerical).
- Reported by the formalizing agent, written but not yet in this repository: D ≤ (d² + d√a)/2 when one
  factor family generates an algebra of dimension a; and a smallest counterexample to R expands
  every subspace on all four sides (the A_a, the B_a and their transposes). When those notes are
  added here they belong to this item.
- A variant of the first: by D0 and semisimplification, if the representation (A_a : W₁ → W₂,
  B_a : W₂ → W₁) has simple composition factors of dimensions (p_i, q_i), then D ≤ (d² + Σ_i p_i q_i)/2. So only
  a single simple representation of dimension (d, d) is hard.
- D2 and D3 are tight, for a random G or a random pair of bases, on every operator above the pairing
  value that I know: the pairing itself, the partial transposes (d² + m d)/2 up to d = 10, and
  swap − tr(·)1 at d ≤ 5, over GF(101) and (D3) over GF(2). Random operators with two to four terms
  have ker(K + G ⊗ G⁻¹) = 0.
- S is a statement about ordinary sums of M + 1 tensor products, with no transpose. I have no proof
  for M ≥ 3 and no proof that R implies S.

First open instance of R: M = 3, d = 4 over GF(2) or GF(3). The value 11 is attained there by the padded example of
paper 17 (noted by GPT-6 Astra, 13 November 2026), so the question is whether 11 is the maximum.
