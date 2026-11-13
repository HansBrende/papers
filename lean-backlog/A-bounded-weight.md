# A. Decoders of bounded weight

**Status:** A1–A4 are proved in Lean, together with the strengthenings below. The definitions
and decoder results live in `LeanMachine.BoundedWeight`; this item has no remaining
formalization obligations.

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

**Formalized generalization of A1.** Let K₁, …, Kₖ be decoders on the same d × d matrix space,
with weights γ₁, …, γₖ. Independently choose each Lᵢ to be swap Kᵢ or its adjoint. For odd k,

$$
|\operatorname{tr}(L_1\cdots L_k)|\le d\prod_{i=1}^k\gamma_i.
$$

The decoders need not coincide or commute. The original A1 is the constant-decoder,
constant-weight case, with its original hypotheses unchanged. Both statements allow d = 0.

**Theorem A2.** If K has weight γ, then (1 + γ) dim C(K) ≤ γ (d² + d). If moreover γ ≤ 1, then
2 dim C(K) ≤ d² + γ d.

**Formalized refinements of A2.** The first bound holds with the actual trace retained:

$$
(1+\gamma)\dim C(K)\le\gamma d^2+\operatorname{Re}\operatorname{tr}(T).
$$

Also, **γ < 1 implies C(K) = {0}**. Thus a decoder with a nonzero code must have weight at
least one. The formalization permits d = 0 as well as positive d. Neither original A2 statement
has been weakened.

**Theorem A3.** Let n₊ be the number of eigenvalues of H, with multiplicity, that are at least 1.
(i) dim C(K) ≤ n₊, for every K.
(ii) If K has weight γ and q is a real polynomial with q(−x) = −q(x) and |q(x) − clip(x)| ≤ η for
all x in [−γ, γ], where clip(x) = max(−1, min(1, x)), then
2 n₊ ≤ (1 + η) d² + (Σ_k |q_k| γ^k) d.

**Formalized refinement of A3.** Part (ii) needs only
q(λᵢ) ≥ clip(λᵢ) − η at the actual eigenvalues of H. No upper approximation bound, nor any
approximation between eigenvalues, is needed. The original interval version follows directly.
Both parts retain all original hypotheses and also allow d = 0.

The shared spectral lemma is more general: for any complex Hermitian matrix H, real threshold t,
and subspace U such that Re ⟨x, Hx⟩ ≥ t‖x‖² for every x ∈ U, the dimension of U is at most the
number of eigenvalues of H at least t. The subspace need not be invariant under H.

**Corollary A4.** For all γ ≥ 0 and η > 0 there is C such that dim C(K) ≤ (½ + η) d² + C d for
every d and every K of weight γ.

**Formalized refinement of A4.** For every Γ ≥ 0 and η > 0 there is a nonnegative constant
C = C(Γ, η), independent of the dimension and decoder, such that

$$
\dim C(K)\le n_+(K)\le (\tfrac12+\eta)d^2+C d
$$

whenever K has any weight γ ≤ Γ. In particular, the weight may vary with d while staying
bounded by Γ. The original A4 statement follows with γ = Γ, with no weakened hypotheses.
The formalization includes d = 0. This gives a uniform asymptotic half-rate bound; it does
not claim a bound of d²/2 + C d with C independent of η.

## Proofs

**Field scope.** The swap and tensor identities used below are algebraic and also hold over
arbitrary fields. The bounds use additional structure: nonnegative real weights, Euclidean
contractions, ordered Hermitian eigenvalues, and real polynomial approximation. If a decoder
over F is embedded into ℂ and its image has the required bounded weight, the same code-dimension
bound follows over F: apply `MatrixRankCertificate.finrank_ker_map_field` to swap − K.
In particular this covers real and rational decoders with such a certificate. It does not
give a finite-field version of A4. A bounded number of arbitrary tensor summands is a different
hypothesis from bounded analytic weight. See [B's field-scope analysis](B-recovery-matrix.md#field-extensions-and-algebraic-alternatives)
for the trace obstruction and an arbitrary-field rank certificate that could replace the
analytic argument if suitable witnesses can be constructed.

Facts used throughout.
- (F1) swap is a real symmetric permutation matrix and swap² = 1.
- (F2) swap (A ⊗ B) = (B ⊗ A) swap.
- (F3) tr(swap (P ⊗ Q)) = tr(PQ). Indeed the entry of swap (P ⊗ Q) at ((i, j), (i, j)) is
  P_{ji} Q_{ij}.
- (F4) (A ⊗ B)* = A* ⊗ B*, (A ⊗ B)(A′ ⊗ B′) = AA′ ⊗ BB′; products and adjoints of contractions
  are contractions; a Kronecker product of contractions is a contraction.
- (F5) |tr P| ≤ d for a d × d contraction P, because |P_{ii}| = |⟨e_i, P e_i⟩| ≤ 1.

*Outline of the formal proof of A1.* Write S = swap. Contractions are closed under multiplication
and adjoints by their operator-norm characterization. Taking products of finite tensor sums
multiplies their coefficient sums; adjoints preserve them because the coefficients are real.
Conjugation by S exchanges the tensor factors, preserving the weight.

Consequently each chosen letter Lᵢ is S Rᵢ with Rᵢ of weight γᵢ: use Rᵢ = Kᵢ for a plain letter
and Rᵢ = S Kᵢ* S for an adjoint. Induction in pairs of letters reduces an odd product to S Q,
where Q has weight ∏ᵢ γᵢ. The singleton case is immediate, and the induction step is

$$
(S R_1)(S R_2)(S Q)=S\bigl(R_1(SR_2S)Q\bigr).
$$

The single-swapped-combination trace bound already proved for A2 gives
|tr(S Q)| ≤ d ∏ᵢ γᵢ. Specializing all Kᵢ and γᵢ proves the original A1. ∎

*Outline of the formal proof of A2.* Let D = dim C(K). The positive-semidefinite identity

$$
I-(A\otimes B)^*(A\otimes B)
=(I-A^*A)\otimes I+(A^*A)\otimes(I-B^*B)
$$

shows that each tensor summand is a contraction. Transposition preserves Euclidean norm, so
the triangle inequality gives ‖T x‖ ≤ γ‖x‖. The trace identity (F3), the contraction bounds for
A and B, and the trace bound from B1's library give |tr T| ≤ γd.
Since C(K) = ker(1 − T), weighted B1 gives
(1 + γ)D ≤ γd² + Re tr T ≤ γ(d² + d).
For γ ≤ 1, add (1 − γ)D ≤ (1 − γ)d² to obtain the second A2 bound.
For γ < 1, a fixed vector satisfies ‖x‖ = ‖Tx‖ ≤ γ‖x‖, forcing x = 0. ∎

*Outline of the formal proof of A3.* (i) In an orthonormal eigenbasis, retain only the coordinates
whose eigenvalues are at least t. This coordinate map is injective on any subspace U with
Re ⟨x, Hx⟩ ≥ t‖x‖². Indeed, a vector in its kernel has

$$
\sum_i(t-\lambda_i)|x_i|^2\le 0.
$$

Every nonzero coordinate lies below t, where its coefficient is strictly positive. Hence all
coordinates vanish. The injective map bounds dim U by the number of retained coordinates.
For code vectors Tx = x, the adjoint identity gives Re ⟨x, Hx⟩ = ‖x‖². Apply the general result
with t = 1, transporting the code between ordinary coordinates and Euclidean space.

(ii) Write S = swap and L = (K + S K* S)/2. Closure under addition, nonnegative rescaling,
adjoints and conjugation by S shows that L has the same weight γ as K, and H = S L.
Consequently ‖Hx‖ ≤ γ‖x‖ and every eigenvalue lies in [−γ, γ]. Applying A1 to powers of S L
gives |tr H^k| ≤ γ^k d for odd k, without expanding words in T and T*.

The spectral theorem identifies tr H^k with Σᵢ λᵢ^k. An odd real polynomial has nonzero
coefficients only in odd degrees, so the triangle inequality yields
|Σᵢ q(λᵢ)| ≤ (Σₖ |qₖ| γ^k) d. Meanwhile, the one-sided approximation at the eigenvalues gives

$$
\sum_i q(\lambda_i)\ge\sum_i\operatorname{clip}(\lambda_i)-\eta d^2
\ge 2n_+-(1+\eta)d^2.
$$

Combine the two bounds. Uniform approximation on [−γ, γ] implies the required one-sided
inequalities, proving the original statement. ∎

*Outline of the formal proof of A4.* clip is continuous and odd. Mathlib's Weierstrass theorem
gives a polynomial p within 2η of clip on [−Γ, Γ]. Its odd part
q(x) = (p(x) − p(−x))/2 is odd on all of ℝ and remains within 2η of clip on that interval.
The shared approximation lemma proves this for every continuous odd function on a symmetric
interval, including the singleton case Γ = 0.

If K has weight γ ≤ Γ, append a zero tensor summand with coefficient Γ − γ. This changes its
weight representation to Γ without changing K. Apply A3 to obtain

$$
2n_+(K)\le(1+2\eta)d^2+\left(\sum_k |q_k|\Gamma^k\right)d.
$$

Take C = (Σₖ |qₖ| Γ^k)/2 ≥ 0. The polynomial, hence C, was chosen using Γ and η only, before
d or K. Finally dim C(K) ≤ n₊(K) gives the original statement. ∎

## Shared proof dependencies

- B1 and A1–A4 are complete. A2 reuses `RecoveryTrace.weighted_finrank_fixed_le` directly;
  A1 reuses A2's single-swapped-combination trace bound and preserves the exact coefficient sum.
- The shared implementation supplies `HasWeight.norm_apply_le`, `HasWeight.norm_T_apply_le`,
  `trace_swapMat_kronecker`, `HasWeight.norm_trace_T_le` (the length-one trace bound), and
  `code_eq_ker`, as well as `HasWeight.mul`, `.conjTranspose`, `.swap_conj` and the general
  `norm_trace_mixedWord_le`. Reuse these for later items.
- A3 uses the shared `HermitianSpectrum` and `SpectralCounting` modules. They reuse Mathlib's
  Hermitian eigenbasis, spectral theorem, Parseval identity and polynomial coefficient API.
  Symmetrization and the odd-moment bounds are in `BoundedWeight.Hermitian`; the polynomial
  certificate and its direct code-dimension corollary are in `BoundedWeight.Polynomial`.
- A4 reuses Mathlib's `exists_polynomial_near_of_continuousOn` through the shared
  `LeanMachine.exists_odd_polynomial_near`. Weight padding is `HasWeight.mono`; the
  final bound and its uniform spectral refinement are in `BoundedWeight.Asymptotic`.

## Verified A1–A4 declarations

All names below have prefix `LeanMachine.BoundedWeight`.

| Statement | Declaration | Module |
|---|---|---|
| A1, original odd-word bound | `norm_trace_word_le` | [`Words`](../lean-machine/LeanMachine/BoundedWeight/Words.lean) |
| Different decoders and weights | `norm_trace_mixedWord_le` | `Words` |
| Representation of odd products | `exists_odd_product_core` | `Words` |
| A2, general weight | `finrank_code_le` | [`Bounds`](../lean-machine/LeanMachine/BoundedWeight/Bounds.lean) |
| A2, weight at most one | `two_mul_finrank_code_le_of_le_one` | `Bounds` |
| Actual-trace refinement | `finrank_code_le_trace` | `Bounds` |
| Zero code below weight one | `code_eq_bot_of_lt_one` | `Bounds` |
| A3(i), spectral dimension bound | `finrank_code_le_nPlus` | [`Hermitian`](../lean-machine/LeanMachine/BoundedWeight/Hermitian.lean) |
| Symmetrization preserves the weight | `HasWeight.hermCore` | `Hermitian` |
| Odd eigenvalue moments | `abs_sum_eigenvalues_pow_le` | `Hermitian` |
| A3(ii), original polynomial bound | `two_mul_nPlus_le` | [`Polynomial`](../lean-machine/LeanMachine/BoundedWeight/Polynomial.lean) |
| One-sided approximation on the spectrum | `two_mul_nPlus_le_of_lower_bound` | `Polynomial` |
| Direct polynomial bound on the code | `two_mul_finrank_code_le_polynomial` | `Polynomial` |
| A4, original asymptotic half-rate bound | `exists_linear_excess` | [`Asymptotic`](../lean-machine/LeanMachine/BoundedWeight/Asymptotic.lean) |
| Uniform spectral bound for all weights at most Γ | `exists_uniform_spectral_excess` | `Asymptotic` |
| Padding to any larger weight | `HasWeight.mono` | [`Closure`](../lean-machine/LeanMachine/BoundedWeight/Closure.lean) |

The original Lean statements follow directly from the new declarations, using the original
definitions. The proofs use only `propext`, `Classical.choice` and `Quot.sound`.
See the [module guide](../lean-machine/LeanMachine/BoundedWeight/README.md) for the shared
lemmas and verification commands.

## What it is for

A decoder assembled from a bounded number of row and column operations of bounded norm has bounded
weight, whatever the arrangement of the operations. A4 says that such a decoder transposes at most
about half of the matrix space, on every helper relation, with no hypothesis of the kind used by
order arguments. The swap itself has weight d. The partial transposes on a tensor factor of size m
have weight m and codes of dimension (d² + m d)/2, so A3 cannot be improved to d(d+1)/2.

Numerical checks (not proofs): the identity tr T³ = Σ_{a,b,c} tr(A_c B_a A_b B_c A_a B_b); the bound
of A1 on all words of length 1, 3, 5 for random operators; A3(i) on random operators and on partial
transposes, where it holds with equality.
