import TransposeFollowup.HaarFinitePacking

/-! An actual finite translate cover retains a large intersection with
one translate. No measurability or finite-volume assumption is hidden. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

theorem exists_large_overlap_of_finite_translate_cover {G : Type*} [Group G] [MeasurableSpace G]
    (σ : Measure G) {A O U : Set G} (hA : A.Nonempty) (hAO : A ⊆ O)
    (F : Finset G) (hcover : A ⊆ (F : Set G) * U) :
    ∃ x ∈ F, σ A ≤ (F.card : ℝ≥0∞) * σ (O ∩ x • U) := by
  have hFn : F.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨x, hx, _, _, _⟩ := Set.mem_mul.mp (hcover ha)
    exact ⟨x, hx⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image F (fun y => σ (O ∩ y • U)) hFn
  refine ⟨x, hx, ?_⟩
  calc
    σ A ≤ σ (⋃ y ∈ F, O ∩ y • U) := by
      apply measure_mono
      intro a ha
      obtain ⟨y, hy, u, hu, heq⟩ := Set.mem_mul.mp (hcover ha)
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hAO ha,
        Set.mem_smul_set.mpr ⟨u, hu, heq⟩⟩⟩
    _ ≤ ∑ y ∈ F, σ (O ∩ y • U) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ F, σ (O ∩ x • U) := Finset.sum_le_sum hmax
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end TransposeFollowup
