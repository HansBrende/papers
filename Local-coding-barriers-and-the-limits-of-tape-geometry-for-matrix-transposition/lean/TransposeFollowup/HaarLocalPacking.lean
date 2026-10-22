import TransposeFollowup.HaarFinitePacking

/-! A local piece of an approximate group controls an actual finite cover.
The output is a cardinality bound and a set inclusion, not an entropy assumption. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

theorem measure_le_of_finite_left_cover (σ : Measure G) [Measure.IsMulLeftInvariant σ]
    {B U : Set G} (F : Finset G) (hcover : B ⊆ (F : Set G) * U) :
    σ B ≤ (F.card : ℝ≥0∞) * σ U := by
  calc
    σ B ≤ σ (⋃ x ∈ F, x • U) := by
      apply measure_mono
      intro b hb
      obtain ⟨x, hx, u, hu, rfl⟩ := Set.mem_mul.mp (hcover hb)
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, Set.smul_mem_smul_set hu⟩⟩
    _ ≤ ∑ x ∈ F, σ (x • U) := measure_biUnion_finset_le _ _
    _ = _ := by simp only [measure_smul, Finset.sum_const, nsmul_eq_mul]

theorem exists_finite_cover_from_local_volume (σ : Measure G) [Measure.IsMulLeftInvariant σ]
    {U T : Set G} (hT : MeasurableSet T) (hTU : T ⊆ U) (hUt : σ U < ⊤)
    {c a : ℝ≥0∞} (hct : c ≠ ⊤) (ha : 0 < a) (hlocal : a ≤ 2 * σ T)
    (hsmall : σ (U ^ 2) ≤ c * σ U) :
    ∃ F : Finset G, (F : Set G) ⊆ U ∧ (F.card : ℝ≥0∞) * a ≤ 2 * c * σ U ∧
      U ⊆ (F : Set G) * T * T⁻¹ := by
  have hT0 : 0 < σ T := by
    by_contra hn
    have hz : σ T = 0 := le_antisymm (not_lt.mp hn) bot_le
    rw [hz, mul_zero] at hlocal
    exact (not_le_of_gt ha) hlocal
  have hTt : σ T < ⊤ := (measure_mono hTU).trans_lt hUt
  let R := c * σ U / σ T
  have hRt : R ≠ ⊤ := by dsimp only [R]; finiteness
  have hcancel : R * σ T = c * σ U := ENNReal.div_mul_cancel hT0.ne' hTt.ne
  have hUT : σ (U * T) ≤ R * σ T := by
    rw [hcancel]
    exact (measure_mono (Set.mul_subset_mul le_rfl hTU)).trans
      (by simpa only [pow_two] using hsmall)
  obtain ⟨F, hF, hcard, hcover⟩ := exists_finite_haar_translate_cover σ hT hT0 hTt hRt hUT
  refine ⟨F, hF, ?_, hcover⟩
  calc
    (F.card : ℝ≥0∞) * a ≤ (F.card : ℝ≥0∞) * (2 * σ T) := mul_le_mul' le_rfl hlocal
    _ = 2 * ((F.card : ℝ≥0∞) * σ T) := by ring
    _ ≤ 2 * (R * σ T) := mul_le_mul' le_rfl (mul_le_mul' hcard le_rfl)
    _ = 2 * c * σ U := by rw [hcancel, mul_assoc]

end TransposeFollowup
