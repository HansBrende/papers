import TransposeFollowup.SL2TranslatedCluster

/-! Native covering bounds for left translates and finite covers by
left translates. The radius distortion is paid by the existing explicit
Frobenius coordinate refinement. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem left_translate_coveringNumber_le (t : G) {S : Set G} {B Q : ℝ} {η : ℝ≥0}
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hη : 0 < η)
    (ht : ∀ i j, |t i j| ≤ B) (hS : ∀ x ∈ S, ∀ i j, |x i j| ≤ Q) :
    Metric.externalCoveringNumber η ((fun x : G => ((t * x : G) : RMat)) '' S) ≠ ⊤ ∧
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => ((t * x : G) : RMat)) '' S) : ℝ≥0∞).toReal ≤
        (8 * B + 1) ^ 4 *
          (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) : ℝ≥0∞).toReal := by
  let S' := (fun x : G => t * x) '' S
  have hS' : ∀ x ∈ S', ∀ i j, |x i j| ≤ 2 * B * Q := by
    rintro x ⟨y, hy, rfl⟩
    exact matrixEntryBox_mul ht (hS y hy)
  obtain ⟨hfin, hfin', hbound⟩ := coveringNumber_le_left_translate t⁻¹ hB
    (by positivity : 0 ≤ 2 * B * Q) hη (matrixEntryBox_inv ht) hS'
  have ha : ((fun x : G => (x : RMat)) '' S') =
      (fun x : G => ((t * x : G) : RMat)) '' S := by simp only [S', Set.image_image]
  have hb : ((fun x : G => ((t⁻¹ * x : G) : RMat)) '' S') =
      (fun x : G => (x : RMat)) '' S := by simp only [S', Set.image_image, inv_mul_cancel_left]
  rw [ha] at hfin hbound
  rw [hb] at hfin' hbound
  exact ⟨hfin, hfin', hbound⟩

theorem coveringNumber_le_finite_left_cover {A C : Set G} (F : Finset G)
    {B Q : ℝ} {η : ℝ≥0} (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hη : 0 < η)
    (hF : ∀ t ∈ F, ∀ i j, |t i j| ≤ B) (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ Q)
    (hcover : C ⊆ (F : Set G) * A) :
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' C) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' C) : ℝ≥0∞).toReal ≤
        (8 * B + 1) ^ 4 * (F.card : ℝ) *
          (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal := by
  let P (t : G) := (fun x : G => ((t * x : G) : RMat)) '' A
  have hpiece (t : G) (ht : t ∈ F) := left_translate_coveringNumber_le t hB hQ hη (hF t ht) hA
  have hpieces : ∀ z ∈ (fun x : G => (x : RMat)) '' C, ∃ t ∈ F, z ∈ P t := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨t, ht, y, hy, rfl⟩ := hcover hx
    exact ⟨t, ht, y, hy, rfl⟩
  obtain ⟨hCfin, hsum⟩ := coveringNumber_le_sum_of_cover F
    ((fun x : G => (x : RMat)) '' C) P hpieces (fun t ht => (hpiece t ht).1)
  have hAfin : Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ := by
    apply finite_coveringNumber_of_entry_bound hQ hη
    rintro z ⟨x, hx, rfl⟩
    exact hA x hx
  refine ⟨hAfin, hCfin, hsum.trans ?_⟩
  calc
    _ ≤ ∑ _t ∈ F, (8 * B + 1) ^ 4 *
        (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal :=
      Finset.sum_le_sum (fun t ht => (hpiece t ht).2.2)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end TransposeFollowup.SL2Projection
