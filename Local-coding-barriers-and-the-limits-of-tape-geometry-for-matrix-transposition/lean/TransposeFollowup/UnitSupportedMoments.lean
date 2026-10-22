import TransposeFollowup.UnitSupportedL1
import TransposeFollowup.FourierL2Bridge

/-! All polynomial spatial moments of a unit-supported L2 input are in
L1 and L2. Their L2 norms do not exceed the original norm. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped FourierTransform ContDiff
set_option autoImplicit false

theorem unit_supported_moment_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    ∀ᵐ x ∂volume, ‖x ^ n • f x‖ ≤ ‖f x‖ := by
  filter_upwards [hs] with x hx
  by_cases hmem : x ∈ Icc (0 : ℝ) 1
  · rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hmem.1]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hmem.1 hmem.2) (norm_nonneg _)).trans_eq
      (one_mul _)
  · simp only [hx hmem, smul_zero, norm_zero, le_refl]

theorem unit_supported_moment_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    MemLp (fun x : ℝ => x ^ n • f x) 2 volume :=
  hf.of_le ((show Continuous (fun x : ℝ => x ^ n) by fun_prop).aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (unit_supported_moment_norm_le hs n)

theorem unit_supported_moment_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → x ^ n • f x = 0 := by
  filter_upwards [hs] with x hx hmem
  simp only [hx hmem, smul_zero]

theorem unit_supported_moment_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n • f x) :=
  integrable_of_unit_supported_L2 (unit_supported_moment_memLp hf hs n)
    (unit_supported_moment_support hs n)

theorem unit_supported_norm_moment_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ n * ‖f x‖) := by
  simpa only [norm_smul, Real.norm_eq_abs, abs_pow] using
    (unit_supported_moment_integrable hf hs n).norm

theorem unit_supported_moment_toLp_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) :
    ‖(unit_supported_moment_memLp hf hs n).toLp (fun x : ℝ => x ^ n • f x)‖ ≤ ‖hf.toLp f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(unit_supported_moment_memLp hf hs n).coeFn_toLp, hf.coeFn_toLp,
    unit_supported_moment_norm_le hs n] with x hm hf hx
  simpa only [hm, hf] using hx

theorem unit_supported_fourier_smooth {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ContDiff ℝ ∞ (𝓕 f) :=
  Real.contDiff_fourier (fun n _ => unit_supported_norm_moment_integrable hf hs n)

end TransposeFollowup
