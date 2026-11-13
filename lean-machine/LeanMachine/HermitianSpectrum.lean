import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Trace

/-! Spectral moments and dimension bounds for Hermitian matrices. -/

noncomputable section

open scoped Matrix ComplexConjugate InnerProductSpace

namespace LeanMachine.HermitianSpectrum

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℂ} (hA : A.IsHermitian)

/-- The matrix eigenvector identity transported to Euclidean space. -/
theorem apply_eigenvector (i : n) :
    A.toEuclideanLin (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
  simpa only [Matrix.toLpLin_apply, WithLp.toLp_smul, WithLp.toLp_ofLp,
    RCLike.real_smul_eq_coe_smul (K := ℂ)] using!
    congrArg (WithLp.toLp 2) (hA.mulVec_eigenvectorBasis i)

/-- In eigenbasis coordinates the operator acts diagonally. -/
theorem repr_apply (x : EuclideanSpace ℂ n) (i : n) :
    hA.eigenvectorBasis.repr (A.toEuclideanLin x) i =
      (hA.eigenvalues i : ℂ) * hA.eigenvectorBasis.repr x i := by
  rw [hA.eigenvectorBasis.repr_apply_apply,
    ← (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) _ _, apply_eigenvector]
  simp only [inner_smul_left, Complex.conj_ofReal, hA.eigenvectorBasis.repr_apply_apply]

/-- The quadratic form is the eigenvalue-weighted sum of squared coordinates. -/
theorem re_inner_eq_sum (x : EuclideanSpace ℂ n) :
    (inner ℂ x (A.toEuclideanLin x)).re =
      ∑ i, hA.eigenvalues i * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
  rw [← hA.eigenvectorBasis.repr.inner_map_map x (A.toEuclideanLin x),
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, repr_apply, Pi.star_apply, RCLike.star_def, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.re_sum,
    Complex.ofReal_re]

/-- An operator bound controls each eigenvalue, also for empty index types. -/
theorem eigenvalues_abs_le {γ : ℝ}
    (h : ∀ x : EuclideanSpace ℂ n, ‖A.toEuclideanLin x‖ ≤ γ * ‖x‖) (i : n) :
    |hA.eigenvalues i| ≤ γ := by
  have hi := h (hA.eigenvectorBasis i)
  simpa only [apply_eigenvector, norm_smul, hA.eigenvectorBasis.norm_eq_one,
    mul_one, Complex.norm_real, Real.norm_eq_abs] using hi

/-- Trace moments can be computed from the chosen real eigenvalues. -/
theorem trace_pow_eq_sum (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i : ℂ) ^ k := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow, Matrix.trace_map']
  simp [Matrix.diagonal_pow, Matrix.trace_diagonal]

/-- A subspace whose Rayleigh quotients are at least `t` has dimension no
larger than the number of eigenvalues at least `t`. No invariance is required. -/
theorem finrank_le_card_eigenvalues_ge (C : Submodule ℂ (EuclideanSpace ℂ n)) (t : ℝ)
    (hC : ∀ x ∈ C, t * ‖x‖ ^ 2 ≤ (inner ℂ x (A.toEuclideanLin x)).re) :
    Module.finrank ℂ C ≤ Fintype.card {i : n // t ≤ hA.eigenvalues i} := by
  classical
  let b := hA.eigenvectorBasis
  let f : C →ₗ[ℂ] ({i : n // t ≤ hA.eigenvalues i} → ℂ) :=
    { toFun := fun x i => b.repr x.val i.val
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro a x; ext i; simp }
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hz (i : n) (hi : t ≤ hA.eigenvalues i) : b.repr x.val i = 0 :=
      congrFun hx ⟨i, hi⟩
    have hn : ∑ i, ‖b.repr x.val i‖ ^ 2 = ‖x.val‖ ^ 2 := by
      rw [← EuclideanSpace.norm_sq_eq, b.repr.norm_map]
    have hs : ∑ i, (t - hA.eigenvalues i) * ‖b.repr x.val i‖ ^ 2 ≤ 0 := by
      have hh := hC x.val x.property
      rw [re_inner_eq_sum hA] at hh
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hn]
      exact sub_nonpos.mpr hh
    have hp (i : n) : 0 ≤ (t - hA.eigenvalues i) * ‖b.repr x.val i‖ ^ 2 := by
      by_cases hi : t ≤ hA.eigenvalues i
      · simp [hz i hi]
      · exact mul_nonneg (sub_nonneg.mpr (le_of_not_ge hi)) (sq_nonneg _)
    have he : ∑ i, (t - hA.eigenvalues i) * ‖b.repr x.val i‖ ^ 2 = 0 :=
      le_antisymm hs (Finset.sum_nonneg fun i _ => hp i)
    have hcoord (i : n) : b.repr x.val i = 0 := by
      by_cases hi : t ≤ hA.eigenvalues i
      · exact hz i hi
      · have heq := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).mp he i (Finset.mem_univ i)
        have hnz : t - hA.eigenvalues i ≠ 0 := ne_of_gt (sub_pos.mpr (lt_of_not_ge hi))
        have hnorm : ‖b.repr x.val i‖ = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp heq).resolve_left hnz)
        exact norm_eq_zero.mp hnorm
    apply Subtype.ext
    apply b.repr.injective
    ext i
    simpa using hcoord i
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one] using
    LinearMap.finrank_le_finrank_of_injective (f := f) hinj

end LeanMachine.HermitianSpectrum
