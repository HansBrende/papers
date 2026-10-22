import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact nonnegative change-of-variables formulas for the affine
parameters s=a² and t=a²b. All functions may take the value infinity. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem lintegral_positive_mul_parameter (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    (∫⁻ b : ℝ, f (c * b)) = ENNReal.ofReal c⁻¹ * ∫⁻ t : ℝ, f t := by
  have himage : (fun x : ℝ => c * x) '' univ = univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨y / c, mem_univ _, ?_⟩
      field_simp
  have hder : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun y : ℝ => c * y) c univ x := by
    intro x _
    simpa using (hasDerivAt_id x).const_mul c
  have hinj : InjOn (fun x : ℝ => c * x) univ := fun _ _ _ _ he => mul_left_cancel₀ hc.ne' he
  have he := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hder hinj f
  rw [himage] at he
  simp only [setLIntegral_univ, abs_of_pos hc,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at he
  calc
    _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) * ∫⁻ b : ℝ, f (c * b) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), inv_mul_cancel₀ hc.ne',
        ENNReal.ofReal_one, one_mul]
    _ = _ := by rw [mul_assoc, ← he]

theorem lintegral_positive_square_parameter (f : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioi (0 : ℝ), f s) =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (2 * a) * f (a ^ 2) := by
  have himage : (fun x : ℝ => x ^ 2) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 0 < x ^ 2
      exact sq_pos_of_pos (show 0 < x from hx)
    · intro hy
      exact ⟨Real.sqrt y, Real.sqrt_pos.mpr hy, Real.sq_sqrt hy.le⟩
  have hder : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun y : ℝ => y ^ 2) (2 * x) (Ioi 0) x := by
    intro x _
    simpa using
      (hasDerivAt_pow 2 x).hasDerivWithinAt (s := Ioi 0)
  have hinj : InjOn (fun x : ℝ => x ^ 2) (Ioi 0) :=
    fun _ hx _ hy he => (sq_eq_sq₀ hx.le hy.le).mp he
  have he := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj f
  rw [himage] at he
  rw [he]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro a ha
  dsimp only
  rw [abs_of_pos (mul_pos (by norm_num) ha)]

theorem lintegral_affine_parameter_change (f : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (2 / a) * ∫⁻ b : ℝ, f (a ^ 2) (a ^ 2 * b)) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (1 / s ^ 2) * ∫⁻ t : ℝ, f s t := by
  conv_rhs => rw [lintegral_positive_square_parameter]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro a ha
  dsimp only
  rw [lintegral_positive_mul_parameter _ (sq_pos_of_pos ha), ← mul_assoc]
  have ha' : 0 < a := ha
  have hw : ENNReal.ofReal (2 / a) * ENNReal.ofReal (a ^ 2)⁻¹ =
      ENNReal.ofReal (2 * a) * ENNReal.ofReal (1 / (a ^ 2) ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hw, mul_assoc]

end TransposeFollowup
