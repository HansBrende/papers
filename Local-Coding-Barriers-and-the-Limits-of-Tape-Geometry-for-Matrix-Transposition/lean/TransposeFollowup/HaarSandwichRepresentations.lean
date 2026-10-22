import TransposeFollowup.HaarPopularOverlap

/-! Successive common-neighbor representations bound every sandwiched
product A*T^n*A^-1. Index n uses n+1 quotient-set factors. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

noncomputable def indicatorConvolutionIterate (σ : Measure G) (C : Set G) : ℕ → G → ℝ≥0∞
  | 0 => C.indicator 1
  | n + 1 => densityConvolution σ (C.indicator 1) (indicatorConvolutionIterate σ C n)

theorem indicatorConvolutionIterate_measurable (σ : Measure G) [SFinite σ]
    {C : Set G} (hC : MeasurableSet C) (n : ℕ) : Measurable (indicatorConvolutionIterate σ C n) := by
  induction n with
  | zero => exact measurable_const.indicator hC
  | succ n ih => exact densityConvolution_measurable σ (measurable_const.indicator hC) ih

theorem indicatorConvolutionIterate_lintegral (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] {C : Set G} (hC : MeasurableSet C) (n : ℕ) :
    (∫⁻ x, indicatorConvolutionIterate σ C n x ∂σ) = σ C ^ (n + 1) := by
  have hf : Measurable (C.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hC
  induction n with
  | zero => simpa only [indicatorConvolutionIterate, Nat.zero_add, pow_one] using (lintegral_indicator_one (μ := σ) hC)
  | succ n ih =>
    rw [indicatorConvolutionIterate, densityConvolution_lintegral σ
      hf (indicatorConvolutionIterate_measurable σ hC n),
      lintegral_indicator_one hC, ih]
    simp only [pow_succ']

theorem indicatorConvolutionIterate_sandwich_lower (σ : Measure G)
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    {A T : Set G} (hA : MeasurableSet A) {t : ℝ≥0∞}
    (hT : ∀ s ∈ T, t ≤ densityConvolution σ ((A⁻¹).indicator 1) (A.indicator 1) s)
    (n : ℕ) : ∀ a ∈ A, ∀ b ∈ A, ∀ s ∈ T ^ n,
      t ^ n ≤ indicatorConvolutionIterate σ (A * A⁻¹) n (a * s * b⁻¹) := by
  let C := A * A⁻¹
  have hf : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hA
  induction n with
  | zero =>
    intro a ha b hb s hs
    have hs1 : s = 1 := by simpa only [pow_zero, Set.mem_one] using hs
    subst s
    have hc : a * b⁻¹ ∈ A * A⁻¹ := Set.mul_mem_mul ha (by simpa only [Set.mem_inv, inv_inv] using hb)
    simp only [pow_zero, mul_one, indicatorConvolutionIterate, Set.indicator_of_mem hc, Pi.one_apply, le_refl]
  | succ n ih =>
    intro a ha b hb s hs
    rw [pow_succ'] at hs
    obtain ⟨z, hz, s, hsn, rfl⟩ := Set.mem_mul.mp hs
    have hchange : indicatorConvolutionIterate σ C (n + 1) (a * (z * s) * b⁻¹) =
        ∫⁻ u, C.indicator (1 : G → ℝ≥0∞) (a * u⁻¹) *
          indicatorConvolutionIterate σ C n (u * z * s * b⁻¹) ∂σ := by
      calc
        _ = ∫⁻ u, C.indicator (1 : G → ℝ≥0∞) (a * u) *
            indicatorConvolutionIterate σ C n (u⁻¹ * z * s * b⁻¹) ∂σ := by
          simpa only [indicatorConvolutionIterate, densityConvolution, mul_inv_rev, mul_assoc,
            inv_mul_cancel_left] using (lintegral_mul_left_eq_self (μ := σ)
              (fun y => C.indicator (1 : G → ℝ≥0∞) y *
                indicatorConvolutionIterate σ C n (y⁻¹ * (a * (z * s) * b⁻¹))) a).symm
        _ = _ := by
          simpa only [inv_inv] using (lintegral_inv_eq_self (μ := σ)
            (fun u => C.indicator (1 : G → ℝ≥0∞) (a * u) *
              indicatorConvolutionIterate σ C n (u⁻¹ * z * s * b⁻¹))).symm
    rw [hchange]
    calc
      t ^ (n + 1) = t * t ^ n := pow_succ' _ _
      _ ≤ densityConvolution σ ((A⁻¹).indicator 1) (A.indicator 1) z * t ^ n := mul_le_mul' (hT z hz) le_rfl
      _ = ∫⁻ u, (A.indicator (1 : G → ℝ≥0∞) u * A.indicator 1 (u * z)) * t ^ n ∂σ := by
        rw [inverse_indicator_convolution_eq_overlap σ hA]
        exact (lintegral_mul_const _ (by fun_prop)).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro u
        by_cases hu : u ∈ A
        · by_cases huz : u * z ∈ A
          · have hc : a * u⁻¹ ∈ C := Set.mul_mem_mul ha (by simpa only [Set.mem_inv, inv_inv] using hu)
            simp only [Set.indicator_of_mem hu, Set.indicator_of_mem huz,
              Set.indicator_of_mem hc, Pi.one_apply, one_mul]
            exact ih (u * z) huz b hb s hsn
          · simp only [Set.indicator_of_notMem huz, mul_zero, zero_mul, zero_le]
        · simp only [Set.indicator_of_notMem hu, zero_mul, zero_le]

theorem sandwich_power_threshold_volume_le (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    {A T : Set G} (hA : MeasurableSet A) (hAA : MeasurableSet (A * A⁻¹))
    {t : ℝ≥0∞} (hT : ∀ s ∈ T, t ≤ densityConvolution σ ((A⁻¹).indicator 1) (A.indicator 1) s)
    (n : ℕ) (hprod : MeasurableSet (A * T ^ n * A⁻¹)) :
    t ^ n * σ (A * T ^ n * A⁻¹) ≤ σ (A * A⁻¹) ^ (n + 1) := by
  calc
    _ = ∫⁻ _x in A * T ^ n * A⁻¹, t ^ n ∂σ := by rw [setLIntegral_const]
    _ ≤ ∫⁻ x in A * T ^ n * A⁻¹, indicatorConvolutionIterate σ (A * A⁻¹) n x ∂σ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hprod] with x hx
      obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨a, ha, s, hs, rfl⟩ := Set.mem_mul.mp hy
      have hbi : b⁻¹ ∈ A := by simpa only [Set.mem_inv] using hb
      simpa only [inv_inv] using indicatorConvolutionIterate_sandwich_lower σ hA hT n a ha b⁻¹ hbi s hs
    _ ≤ ∫⁻ x, indicatorConvolutionIterate σ (A * A⁻¹) n x ∂σ := setLIntegral_le_lintegral _ _
    _ = _ := indicatorConvolutionIterate_lintegral σ hAA n

end TransposeFollowup
