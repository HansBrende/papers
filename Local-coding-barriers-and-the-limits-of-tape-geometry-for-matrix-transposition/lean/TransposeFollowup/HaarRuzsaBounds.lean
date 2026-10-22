import TransposeFollowup.ProductQuotientControl

/-! Continuous Ruzsa and energy lower bounds, using the actual Haar
representations of products rather than a finite discretization. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem haar_ruzsa_product_bound (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    {A B : Set G} (hB : MeasurableSet B) (hAB : MeasurableSet (A * B))
    (hAA : MeasurableSet (A * A⁻¹)) :
    σ (A * A⁻¹) * σ B ≤ σ (A * B) ^ 2 := by
  let C := A * B
  have hp : ∀ x ∈ A * A⁻¹,
      σ B ≤ densityConvolution σ (C.indicator 1) ((C⁻¹).indicator 1) x := by
    intro x hx
    obtain ⟨a, ha, a', ha', rfl⟩ := Set.mem_mul.mp hx
    have hai : a'⁻¹ ∈ A := by simpa only [Set.mem_inv] using ha'
    have he : edgeCodegree (σ.restrict B) (productIncidence C) (a, a'⁻¹) = σ B := by
      calc
        _ = ∫⁻ _b in B, (1 : ℝ≥0∞) ∂σ := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hB] with b hb
          change C.indicator (1 : G → ℝ≥0∞) (a * b) * C.indicator 1 (a'⁻¹ * b) = 1
          simp only [C, Set.indicator_of_mem (Set.mul_mem_mul ha hb),
            Set.indicator_of_mem (Set.mul_mem_mul hai hb), Pi.one_apply, mul_one]
        _ = _ := by rw [lintegral_one, Measure.restrict_apply_univ]
    simpa only [he, inv_inv] using productCodegree_le_quotient_density σ B C a a'⁻¹
  calc
    _ = ∫⁻ _x in A * A⁻¹, σ B ∂σ := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in A * A⁻¹, densityConvolution σ (C.indicator 1) ((C⁻¹).indicator 1) x ∂σ :=
      lintegral_mono_ae ((ae_restrict_mem hAA).mono fun x hx => hp x hx)
    _ ≤ ∫⁻ x, densityConvolution σ (C.indicator 1) ((C⁻¹).indicator 1) x ∂σ := setLIntegral_le_lintegral _ _
    _ = _ := by rw [densityConvolution_indicator_lintegral σ hAB hAB.inv, Measure.measure_inv, pow_two]

theorem haarMultiplicativeEnergy_product_lower (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] {A B : Set G}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : MeasurableSet (A * B)) :
    (σ A * σ B) ^ 2 ≤ haarMultiplicativeEnergy σ A B * σ (A * B) := by
  let F := densityConvolution σ (A.indicator 1) (B.indicator 1)
  have hF : Measurable F := densityConvolution_measurable σ
    (measurable_const.indicator hA) (measurable_const.indicator hB)
  have hmass : (∫⁻ x in A * B, F x ∂σ) = σ A * σ B := by
    rw [setLIntegral_densityConvolution_eq_pair_measure σ hA hB hAB]
    have heq : {p : G × G | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 * p.2 ∈ A * B} = A ×ˢ B := by
      ext p
      constructor
      · exact fun hp => ⟨hp.1, hp.2.1⟩
      · exact fun hp => ⟨hp.1, hp.2, Set.mul_mem_mul hp.1 hp.2⟩
    rw [heq, Measure.prod_prod]
  have hcs := lintegral_mul_sq_le_lintegral_sq_mul_lintegral_sq (σ.restrict (A * B))
    hF (show Measurable (1 : G → ℝ≥0∞) from measurable_const)
  simp only [Pi.one_apply, mul_one, one_pow, lintegral_one, Measure.restrict_apply_univ, hmass] at hcs
  exact hcs.trans (mul_le_mul' (setLIntegral_le_lintegral _ _) le_rfl)

end TransposeFollowup
