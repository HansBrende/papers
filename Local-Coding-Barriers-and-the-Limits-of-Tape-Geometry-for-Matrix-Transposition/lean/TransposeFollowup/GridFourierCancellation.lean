import TransposeFollowup.GridCancellation
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Explicit low-frequency cancellation for the classical Fourier integral,
using Mathlib's exp(-2*pi*i*x*frequency) convention. No identification with
the L2 Fourier transform is asserted in this file. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped BigOperators FourierTransform
set_option autoImplicit false

theorem norm_exp_imaginary_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
  calc
    _ = ‖Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * (a - b)) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    _ = ‖Complex.exp (Complex.I * (a - b)) - 1‖ := by
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    _ ≤ |a - b| := by
      simpa only [Complex.ofReal_sub, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

noncomputable def fourierPhase (ξ x : ℝ) : ℂ :=
  Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I)

theorem fourierPhase_norm (ξ x : ℝ) : ‖fourierPhase ξ x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem fourierPhase_continuous (ξ : ℝ) : Continuous (fourierPhase ξ) := by
  unfold fourierPhase
  fun_prop

theorem fourierPhase_difference (ξ x y : ℝ) :
    ‖fourierPhase ξ x - fourierPhase ξ y‖ ≤ 2 * Real.pi * |ξ| * |x - y| := by
  have h := norm_exp_imaginary_sub_le (-2 * Real.pi * x * ξ) (-2 * Real.pi * y * ξ)
  have he : -2 * Real.pi * x * ξ - (-2 * Real.pi * y * ξ) =
      (-2 * Real.pi * ξ) * (x - y) := by ring
  simpa only [fourierPhase, mul_comm Complex.I, he, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2), abs_of_nonneg Real.pi_pos.le] using h

theorem integrable_mul_fourierPhase {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x => f x * fourierPhase ξ x) :=
  hf.mul_bdd (fourierPhase_continuous ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (fourierPhase_norm ξ x).le))

theorem fourier_eq_pairing (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x, f x * fourierPhase ξ x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [fourierPhase, smul_eq_mul, mul_comm]

/-- Exact zero cell means give a linear gain in frequency divided by K. -/
theorem norm_fourier_le_grid {K : ℕ} (hK : 0 < K) {f : ℝ → ℂ}
    (hf : Integrable f)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in gridCell i, f x) = 0) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ (2 * Real.pi * |ξ| / K) * ∫ x, ‖f x‖ := by
  rw [fourier_eq_pairing]
  exact norm_pairing_le_lipschitz_grid hK hf (integrable_mul_fourierPhase hf ξ)
    hsupport hzero _ (by positivity) (fourierPhase_difference ξ)

theorem classical_fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-- A deliberately conservative explicit constant; this concerns the
classical Fourier integral on the actual frequency interval [-R,R]. -/
theorem integral_low_fourier_sq_le_grid {K : ℕ} (hK : 0 < K) {f : ℝ → ℂ}
    (hf : Integrable f)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in gridCell i, f x) = 0)
    (R : ℝ) (hR : 0 ≤ R) :
    (∫ ξ in Icc (-R) R, ‖𝓕 f ξ‖ ^ 2) ≤
      (8 * Real.pi ^ 2 * R ^ 3 / (K : ℝ) ^ 2) * (∫ x, ‖f x‖) ^ 2 := by
  let C : ℝ := (2 * Real.pi * R / K) * ∫ x, ‖f x‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ ξ ∈ Icc (-R) R, ‖𝓕 f ξ‖ ^ 2 ≤ C ^ 2 := by
    intro ξ hξ
    apply (sq_le_sq₀ (norm_nonneg _) hC).mpr
    apply (norm_fourier_le_grid hK hf hsupport hzero ξ).trans
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun _ => norm_nonneg _))
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg K)
    exact mul_le_mul_of_nonneg_left (abs_le.mpr hξ) (by positivity)
  have hint : IntegrableOn (fun ξ => ‖𝓕 f ξ‖ ^ 2) (Icc (-R) R) :=
    ((classical_fourier_continuous hf).norm.pow 2).integrableOn_Icc
  calc
    _ ≤ ∫ _ξ in Icc (-R) R, C ^ 2 := by
      apply integral_mono_ae hint (integrableOn_const (by simp))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with ξ hξ using hbound ξ hξ
    _ = (R - (-R)) * C ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]
    _ = _ := by dsimp [C]; ring

end TransposeFollowup
