import TransposeFollowup.FrobeniusClosedRefinement
import TransposeFollowup.MobiusFrobeniusCoverVolume

/-! Native external covering numbers for the ambient Frobenius matrix
images of SL2 sets. The covering centers can be arbitrary real matrices. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal NNReal Matrix.Norms.Frobenius
set_option autoImplicit false

theorem externalCoveringNumber_le_finite_frobenius {A : Set Group} (E : Finset Group) {η : ℝ≥0}
    (hcover : ∀ g ∈ A, ∃ e ∈ E,
      (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < (η : ℝ) ^ 2) :
    (Metric.externalCoveringNumber η ((fun g : Group => (g : Matrix (Fin 2) (Fin 2) ℝ)) '' A) : ℝ≥0∞) ≤
      (E.card : ℝ≥0∞) := by
  let ι := fun g : Group => (g : Matrix (Fin 2) (Fin 2) ℝ)
  let F := E.image ι
  have hcov : Metric.IsCover η (ι '' A) (F : Set (Matrix (Fin 2) (Fin 2) ℝ)) := by
    apply isCover_of_strict_frobenius
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨e, he, hge⟩ := hcover g hg
    exact ⟨ι e, Finset.mem_image.mpr ⟨e, he, rfl⟩, hge⟩
  have hn : Metric.externalCoveringNumber η (ι '' A) ≤ (F.card : ℕ∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard] using hcov.externalCoveringNumber_le_encard
  exact (ENat.toENNReal_mono hn).trans (by exact_mod_cast (Finset.card_image_le : F.card ≤ E.card))

variable [MeasurableSpace Group] [BorelSpace Group]

theorem haar_le_externalCoveringNumber {A : Set Group} {η : ℝ≥0} (hη : 0 < η)
    (hηsmall : (η : ℝ) ≤ 1 / 32) (hA : A ⊆ matrixEntryBox 2)
    (hfin : Metric.externalCoveringNumber η
      ((fun g : Group => (g : Matrix (Fin 2) (Fin 2) ℝ)) '' A) ≠ ⊤) :
    (Measure.haar : Measure Group) A ≤
      6561 * 393216 ^ 4 *
        (Metric.externalCoveringNumber η ((fun g : Group => (g : Matrix (Fin 2) (Fin 2) ℝ)) '' A) : ℝ≥0∞) *
        (Measure.haar : Measure Group) (mobiusIdentityBall η) := by
  let H : Measure Group := Measure.haar
  let ι := fun g : Group => (g : Matrix (Fin 2) (Fin 2) ℝ)
  have hbound : ∀ F : Finset (Matrix (Fin 2) (Fin 2) ℝ),
      (∀ g ∈ ι '' A, ∃ e ∈ F, (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < (η : ℝ) ^ 2) →
      H A ≤ (393216 ^ 4 * H (mobiusIdentityBall η)) * (F.card : ℝ≥0∞) := by
    intro F hF
    have h := haar_le_frobenius_cover_card_at_scale F hη hηsmall hA
      (fun g hg => hF (ι g) (Set.mem_image_of_mem ι hg))
    calc
      H A ≤ 393216 ^ 4 * (F.card : ℝ≥0∞) * H (mobiusIdentityBall η) := h
      _ = _ := by ring
  calc
    H A ≤ 6561 * (393216 ^ 4 * H (mobiusIdentityBall η)) *
        (Metric.externalCoveringNumber η (ι '' A) : ℝ≥0∞) :=
      strict_cover_cost_le_externalCoveringNumber hη hfin hbound
    _ = _ := by ring

end TransposeFollowup.RealMobius
