import LeanMachine.MatrixRankCertificate
import LeanMachine.RecoveryFrobenius

/-!
# Analytic recovery certificates through field embeddings

Dimensions are computed over the source field. Norms and positivity are tested
after a specified embedding into `ℝ` or `ℂ`; an embedding alone supplies none of
these hypotheses. In particular these transfers do not apply to finite fields.
-/

namespace LeanMachine.RecoveryTransfer

open Module
open scoped Matrix ComplexOrder

variable {F 𝕜 n : Type*} [Field F] [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The weighted trace bound for a matrix over any field with a specified
real or complex embedding and norm bound on the mapped matrix. -/
theorem weighted_finrank_fixed_le (f : F →+* 𝕜) (M : Matrix n n F) (γ : ℝ)
    (hM : ∀ x, ‖(M.map f).toEuclideanLin x‖ ≤ γ * ‖x‖) :
    (1 + γ) * (finrank F (LinearMap.ker (1 - M).mulVecLin) : ℝ) ≤
      γ * Fintype.card n + RCLike.re (M.map f).trace := by
  simpa only [MatrixRankCertificate.finrank_fixed_map_field] using
    RecoveryTrace.weighted_finrank_fixed_le (M.map f) γ hM

/-- The contraction form of B1, transferred without any loss of dimension. -/
theorem two_mul_finrank_fixed_le_of_contraction (f : F →+* 𝕜) (M : Matrix n n F)
    (hM : (1 - (M.map f)ᴴ * M.map f).PosSemidef) :
    2 * (finrank F (LinearMap.ker (1 - M).mulVecLin) : ℝ) ≤
      Fintype.card n + RCLike.re (M.map f).trace := by
  simpa only [MatrixRankCertificate.finrank_fixed_map_field] using
    RecoveryTrace.two_mul_finrank_fixed_le_of_contraction (M.map f) hM

/-- The trace--Frobenius bound with rank taken over the original field. -/
theorem norm_trace_sq_le_rank_mul (f : F →+* 𝕜) (Z : Matrix n n F) :
    ‖(Z.map f).trace‖ ^ 2 ≤
      (Z.rank : ℝ) * ∑ i, ∑ j, ‖f (Z i j)‖ ^ 2 := by
  simpa only [MatrixRankCertificate.rank_map_field, Matrix.map_apply] using
    RecoveryFrobenius.norm_trace_sq_le_rank_mul (Z.map f)

/-- B2's division-free recovery bound, including the identity matrix. -/
theorem norm_trace_sub_sq_add_finrank_mul_le (f : F →+* 𝕜) (M : Matrix n n F) :
    ‖(Fintype.card n : 𝕜) - (M.map f).trace‖ ^ 2 +
      (finrank F (LinearMap.ker (1 - M).mulVecLin) : ℝ) *
        (∑ i, ∑ j, ‖(1 - M.map f) i j‖ ^ 2) ≤
      (Fintype.card n : ℝ) * ∑ i, ∑ j, ‖(1 - M.map f) i j‖ ^ 2 := by
  simpa only [MatrixRankCertificate.finrank_fixed_map_field] using
    RecoveryFrobenius.norm_trace_sub_sq_add_finrank_mul_le (M.map f)

end LeanMachine.RecoveryTransfer
