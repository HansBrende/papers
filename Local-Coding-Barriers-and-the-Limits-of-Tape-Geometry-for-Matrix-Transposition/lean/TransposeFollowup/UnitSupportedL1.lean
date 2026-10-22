import TransposeFollowup.GridCancellation
import Mathlib.MeasureTheory.Function.L2Space

/-! Unit-supported L2 functions are L1, with the sharp L1-to-L2 bound.
The proof expands the nonnegative variance of the pointwise norm on [0,1]. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
set_option autoImplicit false

theorem integrable_of_unit_supported_L2 {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : MemLp f 2 volume)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) : Integrable f := by
  have hi : IntegrableOn f (Icc (0 : ℝ) 1) :=
    MemLp.integrable (by norm_num) (hf.restrict _)
  exact hi.integrable_of_ae_notMem_eq_zero hsupport

theorem integral_norm_sq_le_of_unit_supported_L2 {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : MemLp f 2 volume)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    (∫ x, ‖f x‖) ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 := by
  let m : ℝ := ∫ x, ‖f x‖
  have hn := (integrable_of_unit_supported_L2 hf hsupport).norm.integrableOn
    (s := Icc (0 : ℝ) 1)
  have hsq := ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf).integrableOn
    (s := Icc (0 : ℝ) 1)
  have hc : IntegrableOn (fun _ : ℝ => m ^ 2) (Icc (0 : ℝ) 1) :=
    integrableOn_const (by simp)
  have hsub : IntegrableOn (fun x => ‖f x‖ ^ 2 - (2 * m) * ‖f x‖) (Icc (0 : ℝ) 1) := by
    exact Integrable.sub hsq (hn.const_mul (2 * m))
  have hnSupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → ‖f x‖ = 0 := by
    filter_upwards [hsupport] with x hx hu
    rw [hx hu, norm_zero]
  have hsSupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → ‖f x‖ ^ 2 = 0 := by
    filter_upwards [hnSupport] with x hx hu
    rw [hx hu, zero_pow (by decide : 2 ≠ 0)]
  have hpos : 0 ≤ ∫ x in Icc (0 : ℝ) 1, ‖f x‖ ^ 2 - (2 * m) * ‖f x‖ + m ^ 2 :=
    integral_nonneg (fun x => by
      change (0 : ℝ) ≤ ‖f x‖ ^ 2 - (2 * m) * ‖f x‖ + m ^ 2
      nlinarith [sq_nonneg (‖f x‖ - m)])
  rw [integral_add (f := fun x => ‖f x‖ ^ 2 - (2 * m) * ‖f x‖)
      (g := fun _ => m ^ 2) hsub hc,
    integral_sub (f := fun x => ‖f x‖ ^ 2) (g := fun x => (2 * m) * ‖f x‖)
      hsq (hn.const_mul (2 * m)), integral_const_mul, setIntegral_const,
    setIntegral_eq_integral_of_ae_compl_eq_zero hnSupport,
    setIntegral_eq_integral_of_ae_compl_eq_zero hsSupport] at hpos
  norm_num [smul_eq_mul, Real.volume_real_Icc] at hpos
  dsimp [m] at hpos
  nlinarith

theorem integral_norm_le_one_of_unit_normalized {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : MemLp f 2 volume)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hnorm : (∫ x, ‖f x‖ ^ 2) = 1) : (∫ x, ‖f x‖) ≤ 1 := by
  have h := integral_norm_sq_le_of_unit_supported_L2 hf hsupport
  rw [hnorm] at h
  nlinarith

end TransposeFollowup
