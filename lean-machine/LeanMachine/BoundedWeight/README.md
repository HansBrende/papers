# Bounded-weight transposition decoders

Formalization of [backlog A1–A4](../../../lean-backlog/A-bounded-weight.md), including odd products
with different decoders and weights, an actual-trace refinement of A2, zero code below weight
one, a one-sided spectral approximation refinement of A3, and a uniform spectral refinement
of A4. The definitions agree with the original backlog.

- [`Basic.lean`](Basic.lean): Euclidean contractions and their Kronecker products; the swap
  matrix; decoder weight and code; transpose as an isometry; the fixed-space identification;
  and `tr(swap (A ⊗ B)) = tr(AB)`.
- [`Bounds.lean`](Bounds.lean): operator-norm and trace bounds from the coefficient sum;
  `finrank_code_le_trace`, `finrank_code_le`, `two_mul_finrank_code_le_of_le_one`, and
  `code_eq_bot_of_lt_one`.
- [`Closure.lean`](Closure.lean): operator-norm characterization of complex contractions;
  closure of `HasWeight` under sums, nonnegative scaling, products, adjoints and conjugation
  by transpose; padding to any larger weight; and arbitrary finite indexing of tensor summands.
- [`Words.lean`](Words.lean): reduction of odd products to a swapped tensor combination;
  `norm_trace_mixedWord_le` for distinct decoders and weights; and the original A1 statement,
  `norm_trace_word_le`, as a corollary.
- [`Hermitian.lean`](Hermitian.lean): symmetrization at the same weight, odd spectral moments,
  eigenvalue bounds, and A3(i), `finrank_code_le_nPlus`, without a weight hypothesis.
- [`Polynomial.lean`](Polynomial.lean): A3(ii), `two_mul_nPlus_le`; its refinement requiring
  only `q(λᵢ) ≥ clip(λᵢ) − η` at the actual eigenvalues; and a direct code-dimension corollary.
- [`Asymptotic.lean`](Asymptotic.lean): A4, `exists_linear_excess`; and
  `exists_uniform_spectral_excess`, giving a nonnegative constant C(Γ, η) such that
  `dim C(K) ≤ n₊(K) ≤ (1/2 + η)d² + C d` uniformly for every weight at most Γ.

The code lives in namespace `LeanMachine.BoundedWeight`. Decoder bounds are over ℂ and allow
every natural side length `d`, including zero. The Kronecker-contraction lemma also works over ℝ
and permits the two factors to have different sizes.

The proofs reuse Mathlib's positive-semidefinite Kronecker-product theorem, operator-norm
facts, list induction, and [`RecoveryTrace.weighted_finrank_fixed_le`](../RecoveryTrace.lean).
The general spectral and polynomial arguments live in
[`HermitianSpectrum.lean`](../HermitianSpectrum.lean) and
[`SpectralCounting.lean`](../SpectralCounting.lean). The former gives a dimension bound at any
real threshold for any complex Hermitian matrix and subspace with the requisite Rayleigh
quotient bound, without an invariance hypothesis. The latter applies to arbitrary finite lists
of real numbers. These reuse Mathlib's spectral theorem, orthonormal coordinates and polynomial
API. [`OddPolynomialApproximation.lean`](../OddPolynomialApproximation.lean) symmetrizes
Mathlib's Weierstrass approximant for any continuous odd function on a symmetric interval.
The results provide sufficient obstructions for this decoder class; they do not assert
that all tape transposers admit such decoders.

From `lean-machine/`:

```sh
lake build LeanMachine.BoundedWeight.Asymptotic
```

For the shared-library build and its axiom audit:

```sh
lake build
lake env lean Axioms.lean
```

All exported theorems are included in `Axioms.lean` and use only the standard axioms.
All original A1–A4 statements are verified, without weakened hypotheses.
