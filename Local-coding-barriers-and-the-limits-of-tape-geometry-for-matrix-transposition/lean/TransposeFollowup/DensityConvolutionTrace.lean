import TransposeFollowup.ContinuousDensityConvolution
import TransposeFollowup.FiniteEnergyExtraction

/-! Associativity and the trace identity for nonnegative Haar densities.
For symmetric inputs, mixed convolution energy is the inner product of
their self-convolutions; no commutativity of the group is assumed. -/
namespace TransposeFollowup
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

theorem densityConvolution_assoc (σ : Measure H) [SFinite σ] [Measure.IsMulLeftInvariant σ]
    {f g h : H → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (x : H) :
    densityConvolution σ (densityConvolution σ f g) h x =
      densityConvolution σ f (densityConvolution σ g h) x := by
  unfold densityConvolution
  calc
    _ = ∫⁻ z, ∫⁻ y, f y * g (y⁻¹ * z) * h (z⁻¹ * x) ∂σ ∂σ := by
      apply lintegral_congr
      intro z
      exact (lintegral_mul_const _ (by fun_prop)).symm
    _ = ∫⁻ y, ∫⁻ z, f y * g (y⁻¹ * z) * h (z⁻¹ * x) ∂σ ∂σ :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ y, ∫⁻ z, f y * g z * h (z⁻¹ * (y⁻¹ * x)) ∂σ ∂σ := by
      apply lintegral_congr
      intro y
      simpa only [inv_mul_cancel_left, mul_inv_rev, mul_assoc] using
        (lintegral_mul_left_eq_self (μ := σ)
          (fun z => f y * g (y⁻¹ * z) * h (z⁻¹ * x)) y).symm
    _ = _ := by
      apply lintegral_congr
      intro y
      simp only [mul_assoc]
      exact lintegral_const_mul _ (by fun_prop)

omit [MeasurableInv H] in
theorem densityConvolution_inv_of_symmetric (σ : Measure H) [Measure.IsMulLeftInvariant σ]
    {f g : H → ℝ≥0∞} (hf : ∀ x, f x⁻¹ = f x) (hg : ∀ x, g x⁻¹ = g x) (x : H) :
    densityConvolution σ f g x⁻¹ = densityConvolution σ g f x := by
  unfold densityConvolution
  calc
    _ = ∫⁻ y, f (x⁻¹ * y) * g ((x⁻¹ * y)⁻¹ * x⁻¹) ∂σ :=
      (lintegral_mul_left_eq_self (μ := σ) (fun y => f y * g (y⁻¹ * x⁻¹)) x⁻¹).symm
    _ = _ := by
      apply lintegral_congr
      intro y
      rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one, hg]
      have h : f (x⁻¹ * y) = f (y⁻¹ * x) := by
        simpa only [mul_inv_rev, inv_inv] using hf (y⁻¹ * x)
      rw [h, mul_comm]

omit [MeasurableMul₂ H] in
theorem densityConvolution_comm_at_one (σ : Measure H) [Measure.IsInvInvariant σ]
    (f g : H → ℝ≥0∞) : densityConvolution σ f g 1 = densityConvolution σ g f 1 := by
  unfold densityConvolution
  simp only [mul_one]
  calc
    _ = ∫⁻ y, f y⁻¹ * g (y⁻¹)⁻¹ ∂σ :=
      (lintegral_inv_eq_self (μ := σ) (fun y => f y * g y⁻¹)).symm
    _ = _ := by simp only [inv_inv, mul_comm]

omit [MeasurableMul₂ H] in
theorem densityConvolution_inverse_at_one (σ : Measure H) [Measure.IsInvInvariant σ]
    (f : H → ℝ≥0∞) :
    densityConvolution σ (fun x => f x⁻¹) f 1 = ∫⁻ x, f x ^ 2 ∂σ := by
  simp only [densityConvolution, mul_one, ← pow_two]
  exact lintegral_inv_eq_self (μ := σ) (fun x => f x ^ 2)

theorem densityConvolution_energy_trace (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    {f g : H → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfs : ∀ x, f x⁻¹ = f x) (hgs : ∀ x, g x⁻¹ = g x) :
    (∫⁻ x, densityConvolution σ f g x ^ 2 ∂σ) =
      ∫⁻ x, densityConvolution σ f f x * densityConvolution σ g g x ∂σ := by
  have hff := densityConvolution_measurable σ hf hf
  have hfg := densityConvolution_measurable σ hf hg
  have hinv : (fun x => densityConvolution σ f g x⁻¹) = densityConvolution σ g f :=
    funext (densityConvolution_inv_of_symmetric σ hfs hgs)
  calc
    _ = densityConvolution σ (densityConvolution σ g f) (densityConvolution σ f g) 1 := by
      rw [← hinv, densityConvolution_inverse_at_one]
    _ = densityConvolution σ g (densityConvolution σ f (densityConvolution σ f g)) 1 :=
      densityConvolution_assoc σ hg hf hfg 1
    _ = densityConvolution σ g (densityConvolution σ (densityConvolution σ f f) g) 1 := by
      congr 1
      funext x
      exact (densityConvolution_assoc σ hf hf hg x).symm
    _ = densityConvolution σ (densityConvolution σ (densityConvolution σ f f) g) g 1 :=
      densityConvolution_comm_at_one σ _ _
    _ = densityConvolution σ (densityConvolution σ f f) (densityConvolution σ g g) 1 :=
      densityConvolution_assoc σ hff hg hg 1
    _ = _ := by
      unfold densityConvolution at ⊢
      apply lintegral_congr
      intro x
      simp only [mul_one]
      rw [show (∫⁻ y, g y * g (y⁻¹ * x⁻¹) ∂σ) = densityConvolution σ g g x from
        densityConvolution_inv_of_symmetric σ hgs hgs x]
      rfl

theorem lintegral_mul_sq_le_lintegral_sq_mul_lintegral_sq {X : Type*} [MeasurableSpace X]
    (σ : Measure X) {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x ∂σ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂σ) * ∫⁻ x, g x ^ 2 ∂σ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq σ Real.HolderConjugate.two_two hf.aemeasurable hg.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two, one_div] at h
  have h2 := pow_le_pow_left' h 2
  have hs (z : ℝ≥0∞) : (z ^ (2⁻¹ : ℝ)) ^ 2 = z := by
    simpa only [Nat.cast_ofNat] using ENNReal.rpow_inv_natCast_pow (by norm_num : (2 : ℕ) ≠ 0) z
  simpa only [mul_pow, hs] using h2

theorem densityConvolution_energy_sq_le (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    {f g : H → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfs : ∀ x, f x⁻¹ = f x) (hgs : ∀ x, g x⁻¹ = g x) :
    (∫⁻ x, densityConvolution σ f g x ^ 2 ∂σ) ^ 2 ≤
      (∫⁻ x, densityConvolution σ f f x ^ 2 ∂σ) *
        ∫⁻ x, densityConvolution σ g g x ^ 2 ∂σ := by
  rw [densityConvolution_energy_trace σ hf hg hfs hgs]
  exact lintegral_mul_sq_le_lintegral_sq_mul_lintegral_sq σ
    (densityConvolution_measurable σ hf hf) (densityConvolution_measurable σ hg hg)

end TransposeFollowup
