import TransposeFollowup.DensityLevelEnergy

/-! Null-set changes do not change continuous Haar convolution or energy.
This permits literal support restriction before geometric covering claims. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

theorem densityConvolution_congr_ae (σ : Measure H) [Measure.IsMulRightInvariant σ]
    [Measure.IsInvInvariant σ] {f F g G : H → ℝ≥0∞}
    (hf : f =ᵐ[σ] F) (hg : g =ᵐ[σ] G) (x : H) :
    densityConvolution σ f g x = densityConvolution σ F G x := by
  have hp := (measurePreserving_mul_right σ x).comp (Measure.measurePreserving_inv σ)
  have hg' := hp.quasiMeasurePreserving.ae_eq_comp hg
  apply lintegral_congr_ae
  filter_upwards [hf, hg'] with y hy hgy
  change g (y⁻¹ * x) = G (y⁻¹ * x) at hgy
  rw [hy, hgy]

theorem haarMultiplicativeEnergy_congr_ae (σ : Measure H) [Measure.IsMulRightInvariant σ]
    [Measure.IsInvInvariant σ] {A A' B B' : Set H} (hA : A =ᵐ[σ] A') (hB : B =ᵐ[σ] B') :
    haarMultiplicativeEnergy σ A B = haarMultiplicativeEnergy σ A' B' := by
  have hAi : A.indicator (1 : H → ℝ≥0∞) =ᵐ[σ] A'.indicator 1 := by
    filter_upwards [hA] with x hx
    simp only [Set.indicator_apply, hx]
  have hBi : B.indicator (1 : H → ℝ≥0∞) =ᵐ[σ] B'.indicator 1 := by
    filter_upwards [hB] with x hx
    simp only [Set.indicator_apply, hx]
  exact lintegral_congr fun x => congrArg (fun z => z ^ 2) (densityConvolution_congr_ae σ hAi hBi x)

omit [MeasurableMul₂ H] [MeasurableInv H] in
theorem haarMultiplicativeEnergy_mono (σ : Measure H) {A A' B B' : Set H}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    haarMultiplicativeEnergy σ A B ≤ haarMultiplicativeEnergy σ A' B' := by
  apply lintegral_mono
  intro x
  apply pow_le_pow_left' _ 2
  apply densityConvolution_mono σ
  · intro y
    by_cases hy : y ∈ A
    · simp [hy, hA hy]
    · simp [hy]
  · intro y
    by_cases hy : y ∈ B
    · simp [hy, hB hy]
    · simp [hy]

theorem dyadicDensityLevel_inter_support_ae {X : Type*} [MeasurableSpace X] (σ : Measure X)
    {f : X → ℝ≥0∞} {S : Set X} (hs : ∀ᵐ x ∂σ, x ∉ S → f x = 0)
    {a : ℝ≥0∞} (ha : 0 < a) (j : ℕ) :
    (dyadicDensityLevel f a j ∩ S) =ᵐ[σ] dyadicDensityLevel f a j := by
  filter_upwards [hs] with x hx
  apply propext
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    by_contra hn
    have hp : 0 < f x := (ENNReal.mul_pos ha.ne' (by positivity)).trans_le h.1
    rw [hx hn] at hp
    exact (lt_irrefl 0) hp

end TransposeFollowup
