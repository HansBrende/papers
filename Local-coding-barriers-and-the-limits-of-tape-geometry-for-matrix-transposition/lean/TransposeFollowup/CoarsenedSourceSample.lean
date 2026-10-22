import TransposeFollowup.SeparatedMatrixSample

/-! Pay for the larger spacing required by cubic packing. Existing
coordinate refinement and separated sampling suffice; source witnesses
are retained for the actual-word transfer. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set
open scoped Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ

theorem matrix_coveringNumber_change_radius {A : Set RMat} {η σ : ℝ≥0}
    (hη : 0 < η) (hfin : Metric.externalCoveringNumber σ A ≠ ⊤) :
    Metric.externalCoveringNumber η A ≠ ⊤ ∧
      (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤
        (4 * (σ : ℝ) / (η : ℝ) + 1) ^ 4 *
          (Metric.externalCoveringNumber σ A : ℝ≥0∞).toReal := by
  obtain ⟨F, hcover, hcard⟩ := Metric.exists_finset_card_eq_externalCoveringNumber hfin
  have hpatch : ∀ x ∈ A, ∃ c ∈ F, ∀ i j, |x i j - c i j| ≤ (σ : ℝ) := by
    intro x hx
    obtain ⟨c, hc, hd⟩ := hcover hx
    have hdr : dist x c ≤ (σ : ℝ) := by exact_mod_cast edist_le_coe.mp hd
    exact ⟨c, hc, fun i j => (entry_error_le_frobenius_dist x c i j).trans hdr⟩
  obtain ⟨hAfin, hbound⟩ := coveringNumber_le_coordinate_patches F σ.coe_nonneg hη hpatch
  have hcardR : (F.card : ℝ) = (Metric.externalCoveringNumber σ A : ℝ≥0∞).toReal := by
    have hh : (F.card : ℝ≥0∞) = (Metric.externalCoveringNumber σ A : ℝ≥0∞) := by
      exact_mod_cast hcard
    simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hh
  exact ⟨hAfin, by simpa only [hcardR] using hbound⟩

theorem exists_coarse_source_sample {ι : Type*} (g : ι → RMat)
    {B : ℝ} {η σ : ℝ≥0} (hB : 0 ≤ B) (hη : 0 < η) (hσ : 0 < σ)
    (hgn : (Set.range g).Nonempty) (hg : ∀ x i j, |g x i j| ≤ B) :
    ∃ F : Finset RMat, ∃ s : ↥F → ι,
      F.Nonempty ∧ (∀ y, g (s y) = (y : RMat)) ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → 2 * (σ : ℝ) < dist x y) ∧
      Metric.externalCoveringNumber η (Set.range g) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η (Set.range g) : ℝ≥0∞).toReal ≤
        6561 * (4 * (σ : ℝ) / (η : ℝ) + 1) ^ 4 * (F.card : ℝ) := by
  obtain ⟨F, hFn, hFg, hsep, hfin, hsize⟩ := exists_separated_matrix_sample hB hσ hgn
    (by rintro _ ⟨x, rfl⟩; exact hg x)
  have hsource (y : ↥F) : ∃ i, g i = (y : RMat) := hFg y.property
  choose s hs using hsource
  obtain ⟨hηfin, hchange⟩ := matrix_coveringNumber_change_radius hη hfin
  refine ⟨F, s, hFn, hs, hsep, hηfin, hchange.trans ?_⟩
  calc
    _ ≤ (4 * (σ : ℝ) / (η : ℝ) + 1) ^ 4 * (6561 * (F.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = _ := by ring

end TransposeFollowup.SL2Projection
