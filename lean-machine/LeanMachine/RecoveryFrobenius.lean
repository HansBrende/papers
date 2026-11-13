import LeanMachine.RecoveryTrace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Trace, rank and squared Frobenius-norm bounds for recovery matrices. -/

namespace LeanMachine.RecoveryFrobenius

open Module
open scoped Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

/-- Cauchy--Schwarz for the trace of a rectangular matrix product. -/
theorem norm_trace_mul_sq_le (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) :
    ‖(A * B).trace‖ ^ 2 ≤
      (∑ i, ∑ j, ‖A i j‖ ^ 2) * ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  classical
  have ht : (A * B).trace = ∑ p : m × n, A p.1 p.2 * B p.2 p.1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  have hn : ‖(A * B).trace‖ ≤ ∑ p : m × n, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ := by
    rw [ht]
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun p : m × n => A p.1 p.2 * B p.2 p.1)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : m × n => ‖A p.1 p.2‖) (fun p : m × n => ‖B p.2 p.1‖)
  have hb : (∑ p : m × n, ‖B p.2 p.1‖ ^ 2) = ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hb] at hs
  simpa only [Fintype.sum_prod_type] using (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

/-- Squared Frobenius norm as the real part of a Gram-matrix trace. -/
theorem sum_norm_sq_eq_re_trace (A : Matrix m n 𝕜) :
    (∑ i, ∑ j, ‖A i j‖ ^ 2) = RCLike.re (Aᴴ * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, RCLike.conj_mul, map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  exact Finset.sum_comm

variable [DecidableEq n]

/-- Backlog B2: the trace--rank--Frobenius bound, over either `ℝ` or `ℂ`. -/
theorem norm_trace_sq_le_rank_mul (Z : Matrix n n 𝕜) :
    ‖Z.trace‖ ^ 2 ≤ (Z.rank : ℝ) * ∑ i, ∑ j, ‖Z i j‖ ^ 2 := by
  let C := LinearMap.range Z.toEuclideanLin
  let p := C.starProjection.toLinearMap
  let P : Matrix n n 𝕜 := Matrix.toEuclideanLin.symm p
  have hp : LinearMap.IsProj C p :=
    ⟨fun x => (C.orthogonalProjectionOnto x).property,
      fun x hx => C.starProjection_eq_self_iff.mpr hx⟩
  have hP : P.toEuclideanLin = p := Matrix.toEuclideanLin.apply_symm_apply p
  have hmul : P * Z = Z := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hP]
    apply LinearMap.ext
    intro x
    exact C.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
  have hid : P * P = P := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hP]
    exact hp.isIdempotentElem
  have hstar : Pᴴ = P := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    rw [hP]
    exact C.starProjection_isSymmetric
  have htr : P.trace = (Z.rank : 𝕜) := by
    rw [← Matrix.trace_toLin_eq P (EuclideanSpace.basisFun n 𝕜).toBasis]
    change LinearMap.trace 𝕜 _ P.toEuclideanLin = _
    rw [hP]
    rw [Z.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun n 𝕜).toBasis
      (EuclideanSpace.basisFun n 𝕜).toBasis]
    exact hp.trace
  have hsq : (∑ i, ∑ j, ‖P i j‖ ^ 2) = (Z.rank : ℝ) := by
    rw [sum_norm_sq_eq_re_trace, hstar, hid, htr, RCLike.natCast_re]
  simpa only [hmul, hsq] using norm_trace_mul_sq_le P Z

/-- The recovery-code consequence in a form valid even when `M = 1`.
The second term pays for every dimension of the fixed space. -/
theorem norm_trace_sub_sq_add_finrank_mul_le (M : Matrix n n 𝕜) :
    ‖(Fintype.card n : 𝕜) - M.trace‖ ^ 2 +
      (finrank 𝕜 (LinearMap.ker (1 - M).mulVecLin) : ℝ) *
        (∑ i, ∑ j, ‖(1 - M) i j‖ ^ 2) ≤
      (Fintype.card n : ℝ) * ∑ i, ∑ j, ‖(1 - M) i j‖ ^ 2 := by
  have h := norm_trace_sq_le_rank_mul (1 - M)
  simp only [Matrix.trace_sub, Matrix.trace_one] at h
  have hd : ((1 - M).rank : ℝ) +
      (finrank 𝕜 (LinearMap.ker (1 - M).mulVecLin) : ℝ) = Fintype.card n := by
    have hd := (1 - M).mulVecLin.finrank_range_add_finrank_ker
    simp only [Module.finrank_pi] at hd
    exact_mod_cast hd
  calc
    _ ≤ ((1 - M).rank : ℝ) * (∑ i, ∑ j, ‖(1 - M) i j‖ ^ 2) +
        (finrank 𝕜 (LinearMap.ker (1 - M).mulVecLin) : ℝ) *
          (∑ i, ∑ j, ‖(1 - M) i j‖ ^ 2) := add_le_add h le_rfl
    _ = _ := by rw [← add_mul, hd]

/-- The divided form of the recovery-code bound requires positive squared
Frobenius norm; the preceding theorem covers the degenerate case as well. -/
theorem finrank_fixed_le_sub_div (M : Matrix n n 𝕜)
    (hM : 0 < ∑ i, ∑ j, ‖(1 - M) i j‖ ^ 2) :
    (finrank 𝕜 (LinearMap.ker (1 - M).mulVecLin) : ℝ) ≤
      Fintype.card n - ‖(Fintype.card n : 𝕜) - M.trace‖ ^ 2 /
        (∑ i, ∑ j, ‖(1 - M) i j‖ ^ 2) := by
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hM, sub_mul]
  linarith only [norm_trace_sub_sq_add_finrank_mul_le M]

end LeanMachine.RecoveryFrobenius
