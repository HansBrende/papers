import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! Dyadic power lower bounds for symmetric linear maps, proved directly
from Cauchy–Schwarz. Boundedness and contraction are not needed. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem symmetric_norm_sq_le_double_action (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (f : E) (hf : ‖f‖ = 1) : ‖T f‖ ^ 2 ≤ ‖T (T f)‖ := by
  calc
    _ = inner ℝ (T (T f)) f := by rw [hT, real_inner_self_eq_norm_sq]
    _ ≤ ‖T (T f)‖ * ‖f‖ := real_inner_le_norm _ _
    _ = _ := by rw [hf, mul_one]

theorem symmetric_dyadic_power_norm_lower (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (f : E) (hf : ‖f‖ = 1) {r : ℝ} (hr : 0 ≤ r) (hlarge : r ≤ ‖T f‖) (m : ℕ) :
    r ^ (2 ^ m) ≤ ‖(T ^ (2 ^ m)) f‖ := by
  induction m with
  | zero => simpa using hlarge
  | succ m ih =>
    calc
      _ = (r ^ (2 ^ m)) ^ 2 := by rw [pow_succ (2 : ℕ) m, pow_mul]
      _ ≤ ‖(T ^ (2 ^ m)) f‖ ^ 2 := pow_le_pow_left₀ (pow_nonneg hr _) ih 2
      _ ≤ ‖(T ^ (2 ^ m)) ((T ^ (2 ^ m)) f)‖ :=
        symmetric_norm_sq_le_double_action _ (hT.pow _) f hf
      _ = _ := by
        rw [← Module.End.mul_apply, ← pow_add, pow_succ (2 : ℕ) m, mul_two]

theorem symmetric_dyadic_iterate_norm_lower (T : E →L[ℝ] E)
    (hT : ∀ f h, inner ℝ (T f) h = inner ℝ f (T h))
    (f : E) (hf : ‖f‖ = 1) {r : ℝ} (hr : 0 ≤ r) (hlarge : r ≤ ‖T f‖) (m : ℕ) :
    r ^ (2 ^ m) ≤ ‖(T : E → E)^[2 ^ m] f‖ := by
  have hs : T.toLinearMap.IsSymmetric := hT
  simpa only [Module.End.pow_apply, ContinuousLinearMap.coe_coe] using
    symmetric_dyadic_power_norm_lower T.toLinearMap hs f hf hr hlarge m

end TransposeFollowup
