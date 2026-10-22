import TransposeFollowup.UnitSupportedMoments
import TransposeFollowup.FrequencyCutoff

/-! Quantitative L2 bounds for all frequency derivatives of a unit-supported
input. The constant is (2*pi)^n, with no regularity assumption on the input. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped FourierTransform ContDiff
set_option autoImplicit false

noncomputable def fourierSpatialMoment (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (-2 * Real.pi * Complex.I * x) ^ n * f x

theorem fourierSpatialMoment_factor (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    fourierSpatialMoment f n x = (-2 * (Real.pi : ℂ) * Complex.I) ^ n • (x ^ n • f x) := by
  simp only [fourierSpatialMoment, mul_pow, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_pow, mul_assoc]

theorem fourierSpatialMoment_integrable {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    Integrable (fourierSpatialMoment f n) := by
  have he : fourierSpatialMoment f n = (-2 * (Real.pi : ℂ) * Complex.I) ^ n •
      (fun x : ℝ => x ^ n • f x) := funext (fourierSpatialMoment_factor f n)
  rw [he]
  exact (unit_supported_moment_integrable hf hs n).smul _

theorem fourierSpatialMoment_memLp {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    MemLp (fourierSpatialMoment f n) 2 volume := by
  have he : fourierSpatialMoment f n = (-2 * (Real.pi : ℂ) * Complex.I) ^ n •
      (fun x : ℝ => x ^ n • f x) := funext (fourierSpatialMoment_factor f n)
  rw [he]
  exact (unit_supported_moment_memLp hf hs n).const_smul _

theorem fourierSpatialMoment_norm (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    ‖fourierSpatialMoment f n x‖ = (2 * Real.pi) ^ n * ‖x ^ n • f x‖ := by
  rw [fourierSpatialMoment_factor, norm_smul, norm_pow]
  have hc : ‖(-2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    norm_num [norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc]

theorem fourierSpatialMoment_toLp_norm_le {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    ‖(fourierSpatialMoment_memLp hf hs n).toLp (fourierSpatialMoment f n)‖ ≤
      (2 * Real.pi) ^ n * ‖hf.toLp f‖ := by
  have hn : 0 ≤ (2 * Real.pi) ^ n := by positivity
  have h : ‖(fourierSpatialMoment_memLp hf hs n).toLp (fourierSpatialMoment f n)‖ ≤
      ‖((2 * Real.pi) ^ n : ℝ) • hf.toLp f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(fourierSpatialMoment_memLp hf hs n).coeFn_toLp,
      Lp.coeFn_smul ((2 * Real.pi) ^ n : ℝ) (hf.toLp f), hf.coeFn_toLp,
      unit_supported_moment_norm_le hs n] with x hm hc hx hbound
    rw [hm, hc]
    change ‖fourierSpatialMoment f n x‖ ≤ ‖((2 * Real.pi) ^ n : ℝ) • hf.toLp f x‖
    rw [hx, fourierSpatialMoment_norm]
    conv_rhs => rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left hbound hn
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn] using h

theorem unit_supported_iteratedDeriv_fourier {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    iteratedDeriv n (𝓕 f) = 𝓕 (fourierSpatialMoment f n) := by
  change iteratedDeriv n (𝓕 f) = 𝓕 (fun x : ℝ => (-2 * Real.pi * Complex.I * x) ^ n * f x)
  exact Real.iteratedDeriv_fourier (N := ⊤)
    (fun k _ => unit_supported_moment_integrable hf hs k) (n := n) (by simp)

theorem unit_supported_fourier_derivative_coe {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    ⇑(𝓕 ((fourierSpatialMoment_memLp hf hs n).toLp (fourierSpatialMoment f n)) : ComplexL2)
      =ᵐ[volume] iteratedDeriv n (𝓕 f) := by
  rw [unit_supported_iteratedDeriv_fourier hf hs n]
  exact toLp_fourier_coe_ae (fourierSpatialMoment_integrable hf hs n)
    (fourierSpatialMoment_memLp hf hs n)

theorem unit_supported_fourier_derivative_memLp {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    MemLp (iteratedDeriv n (𝓕 f)) 2 volume :=
  (memLp_congr_ae (unit_supported_fourier_derivative_coe hf hs n)).mp (Lp.memLp _)

theorem unit_supported_fourier_derivative_energy_le {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    (∫ ξ, ‖iteratedDeriv n (𝓕 f) ξ‖ ^ 2) ≤ (2 * Real.pi) ^ (2 * n) * ‖hf.toLp f‖ ^ 2 := by
  let m := (fourierSpatialMoment_memLp hf hs n).toLp (fourierSpatialMoment f n)
  have he : (∫ ξ, ‖iteratedDeriv n (𝓕 f) ξ‖ ^ 2) = ‖m‖ ^ 2 := by
    rw [← Lp.norm_fourier_eq m, complexL2_norm_sq]
    exact integral_congr_ae ((unit_supported_fourier_derivative_coe hf hs n).symm.mono
      (fun _ hx => congrArg (fun z => ‖z‖ ^ 2) hx))
  rw [he]
  have h := pow_le_pow_left₀ (norm_nonneg m) (fourierSpatialMoment_toLp_norm_le hf hs n) 2
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm n 2] using h

end TransposeFollowup
