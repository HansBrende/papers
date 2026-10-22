import TransposeFollowup.FiniteEnergyExtraction

/-! A bounded enlargement cannot account for all of a large overlap.
The core may agree with the original set only almost everywhere. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem measure_inter_le_of_ae_core {X : Type*} [MeasurableSpace X]
    (σ : Measure X) {E D O : Set X} (hE : MeasurableSet E)
    (hED : E =ᵐ[σ] D) (hEO : E ⊆ O) (hDt : σ D ≠ ⊤)
    {ε : ℝ≥0∞} (hbudget : σ O ≤ σ D + ε) (Z : Set X) :
    σ (O ∩ Z) ≤ σ (D ∩ Z) + ε := by
  have hm : σ E = σ D := measure_congr hED
  have hdiff : σ (O \ E) ≤ ε :=
    (measure_sdiff_le_iff_le_add hE.nullMeasurableSet hEO (by rwa [hm])).mpr (by rwa [hm])
  have hEZ : σ (E ∩ Z) = σ (D ∩ Z) := by
    apply measure_congr
    filter_upwards [hED] with x hx
    simp only [Set.mem_inter_iff, hx]
  calc
    σ (O ∩ Z) = σ ((O ∩ Z) ∩ E) + σ ((O ∩ Z) \ E) :=
      (measure_inter_add_sdiff _ hE).symm
    _ ≤ σ (E ∩ Z) + σ (O \ E) := add_le_add
      (measure_mono fun _ hx => ⟨hx.2, hx.1.2⟩)
      (measure_mono fun _ hx => ⟨hx.1.1, hx.2⟩)
    _ ≤ σ (D ∩ Z) + ε := by rw [hEZ]; exact add_le_add le_rfl hdiff

theorem measure_overlap_survives_enlargement {X : Type*} [MeasurableSpace X]
    (σ : Measure X) {E D O Z : Set X} (hE : MeasurableSet E)
    (hED : E =ᵐ[σ] D) (hEO : E ⊆ O) (hDt : σ D ≠ ⊤)
    {ε M : ℝ≥0∞} (hbudget : σ O ≤ σ D + ε)
    (htail : 2 * (M * ε) ≤ σ D) (hlarge : σ D ≤ M * σ (O ∩ Z)) :
    σ D ≤ 2 * M * σ (D ∩ Z) := by
  have hbound : σ D ≤ M * ε + M * σ (D ∩ Z) := by
    calc
      σ D ≤ M * σ (O ∩ Z) := hlarge
      _ ≤ M * (σ (D ∩ Z) + ε) := mul_le_mul' le_rfl
        (measure_inter_le_of_ae_core σ hE hED hEO hDt hbudget Z)
      _ = _ := by ring
  simpa only [mul_assoc] using ennreal_le_two_mul_of_small_add hDt htail hbound

end TransposeFollowup
