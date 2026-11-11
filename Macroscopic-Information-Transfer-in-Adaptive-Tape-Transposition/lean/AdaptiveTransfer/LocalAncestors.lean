import AdaptiveTransfer.FragmentAncestors

/-! Literal ancestors inside a selected time set. Original full-graph cuts
still constrain incoming parents outside the selected set; deleting the
complement is used only to define the retained fragment. -/

namespace AdaptiveTransfer
open Finset BoundedNesting MergeDepth NativeRelations

theorem cutFreeAncestors_mono_deleted {k T : ℕ} {xs : Fin k → ℕ → ℤ}
    {roots B B' : Finset ℕ} (hBB' : B ⊆ B') :
    cutFreeAncestors xs T roots B' ⊆ cutFreeAncestors xs T roots B := by
  classical
  intro t ht
  obtain ⟨hrange, r, hr, ρ, hpath, hfree, hlast⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨hrange, r, hr, ρ, hpath,
    fun u hu huB => hfree u hu (hBB' huB), hlast⟩

noncomputable def localAncestors {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ)
    (roots C B : Finset ℕ) : Finset ℕ := cutFreeAncestors xs T roots (B ∪ (range T \ C))

theorem localAncestors_subset {k T : ℕ} {xs : Fin k → ℕ → ℤ} {roots C B : Finset ℕ} :
    localAncestors xs T roots C B ⊆ C := by
  classical
  intro t ht
  have hn := cutFreeAncestors_not_cut ht
  have htT := cutFreeAncestors_time ht
  by_contra htC
  exact hn (mem_union_right B (mem_sdiff.mpr ⟨mem_range.mpr htT, htC⟩))

theorem localAncestors_subset_global {k T : ℕ} {xs : Fin k → ℕ → ℤ} {roots C B : Finset ℕ} :
    localAncestors xs T roots C B ⊆ cutFreeAncestors xs T roots B :=
  cutFreeAncestors_mono_deleted subset_union_left

theorem localAncestors_closed {k T : ℕ} (xs : Fin k → ℕ → ℤ) (roots C B : Finset ℕ) :
    LocallyStateClosedExcept C (localAncestors xs T roots C B) B := by
  classical
  refine ⟨localAncestors_subset, ?_⟩
  intro t ht htpos hpC hpB
  apply cutFreeAncestors_state_closed xs T roots (B ∪ (range T \ C)) t ht htpos
  intro hp
  rcases mem_union.mp hp with hp | hp
  · exact hpB hp
  · exact (mem_sdiff.mp hp).2 hpC

theorem root_mem_cut_or_localAncestors {k T : ℕ} {xs : Fin k → ℕ → ℤ}
    {roots C B : Finset ℕ} {r : ℕ} (hr : r ∈ roots) (hrT : r < T) (hrC : r ∈ C) :
    r ∈ localAncestors xs T roots C B ∪ B := by
  classical
  have hh := root_mem_cut_or_ancestors (xs := xs) (B := B ∪ (range T \ C)) hr hrT
  rcases mem_union.mp hh with hk | hb
  · exact mem_union_left _ hk
  · rcases mem_union.mp hb with hb | hb
    · exact mem_union_right _ hb
    · exact ((mem_sdiff.mp hb).2 hrC).elim

/-- An internal dependency parent is retained or paid as a cut. -/
theorem localAncestors_parent_inside {k T t p : ℕ} {xs : Fin k → ℕ → ℤ}
    {roots C B : Finset ℕ} (ht : t ∈ localAncestors xs T roots C B)
    (he : DepStep xs T t p) (hpC : p ∈ C) : p ∈ localAncestors xs T roots C B ∪ B := by
  classical
  by_cases hpB : p ∈ B
  · exact mem_union_right _ hpB
  · apply mem_union_left
    apply cutFreeAncestors_parent ht he
    intro hp
    rcases mem_union.mp hp with hp | hp
    · exact hpB hp
    · exact (mem_sdiff.mp hp).2 hpC

/-- A targeted parent is in the ORIGINAL cut, even when it lies outside C.
The proof extends the retained root path by its actual dependency edge. -/
theorem localAncestors_target_parent_cut {k T t p : ℕ} {xs : Fin k → ℕ → ℤ}
    {roots C B targets : Finset ℕ}
    (hsep : IsMengerVertexCut xs T roots targets B)
    (ht : t ∈ localAncestors xs T roots C B) (he : DepStep xs T t p)
    (hp : p ∈ targets) : p ∈ B := by
  classical
  by_contra hpB
  exact cutFreeAncestors_avoid_targets hsep
    (cutFreeAncestors_parent (localAncestors_subset_global ht) he hpB) hp

end AdaptiveTransfer
