import SourceCovers.FiniteSkeleton

set_option autoImplicit false

/-!
# Span partitions and multiplicity

The fact used to state Theorem LA: a set `K` of complete families admits an `N`-class span
partition (`SourceCovers.HasSpanColoring K N`) exactly when no time lies in more than `N` full
spans, that is, when every elementary boundary `e | e + 1` is crossed by at most `N` families of `K`
(`SourceCovers.activeFamilies K e`; the boundary `e | e + 1` is crossed by the span `(p_G, U_G]`
exactly when the time `e + 1` lies in it).

* `family_start_lt_stop`: every full span is nonempty.
* `hasSpanColoring_iff_activeFamilies_card_le`: one direction is the ninth paper's
  `activeFamilies_card_le`. The other is the greedy colouring in the order of the left ends of the
  spans: when a family `G` is coloured, the families already coloured whose spans meet the span of
  `G` all contain its first time, so together with `G` there are at most `N` of them and a colour
  below `N` is free.
-/

namespace MergeDepth

open Finset SourceCovers BoundedNesting

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

/-- Every full span is nonempty: a family contains a long hop `(p, u)`, and
`p_G ≤ p < u ≤ U_G`. -/
theorem family_start_lt_stop (F : ActualFamily xs T) : F.start < F.stop := by
  obtain ⟨η, hη⟩ := fam_nonempty xs (allHops xs T) (actualOwner xs) F
  have hhop := mem_allHops.mp (mem_fam.mp hη).1
  have h1 : F.start ≤ η.2.1 := inf'_le (fun η : Fin k × ℕ × ℕ => η.2.1) hη
  have h2 : η.2.2 ≤ F.stop := le_sup (f := fun η : Fin k × ℕ × ℕ => η.2.2) hη
  have := hhop.1
  omega

theorem family_start_mem_edges (F : ActualFamily xs T) : F.start ∈ F.edges :=
  mem_Ico.mpr ⟨le_rfl, family_start_lt_stop F⟩

/-- **Span partitions.** `K` admits an `N`-class span partition exactly when no time lies in more
than `N` full spans of `K`. -/
theorem hasSpanColoring_iff_activeFamilies_card_le (K : Finset (ActualFamily xs T)) (N : ℕ) :
    HasSpanColoring K N ↔ ∀ e, (activeFamilies K e).card ≤ N := by
  classical
  refine ⟨fun h e => activeFamilies_card_le h e, fun h => ?_⟩
  refine Finset.induction_on_max_value (fun F : ActualFamily xs T => F.start)
    (motive := fun K => (∀ e, (activeFamilies K e).card ≤ N) → HasSpanColoring K N) K
    (fun _ => ⟨fun _ => 0, by simp, by simp⟩) ?_ h
  intro a s ha hmax ih hK
  -- the families of `s` keep their colours
  obtain ⟨color, hcolor, hdisj⟩ := ih fun e =>
    (card_le_card (filter_subset_filter _ (subset_insert a s))).trans (hK e)
  -- the families of `s` whose spans meet the span of `a` all contain the first time of `a`
  set S := s.filter fun q => ¬ Disjoint q.edges a.edges
  have hsub : insert a S ⊆ activeFamilies (insert a s) a.start := by
    intro q hq
    simp only [activeFamilies, mem_filter]
    rcases mem_insert.mp hq with rfl | hq
    · exact ⟨mem_insert_self _ _, family_start_mem_edges q⟩
    · obtain ⟨hqs, hmeet⟩ := mem_filter.mp hq
      refine ⟨mem_insert_of_mem hqs, ?_⟩
      obtain ⟨e, he1, he2⟩ := not_disjoint_iff.mp hmeet
      have h1 := mem_Ico.mp he1
      have h2 := mem_Ico.mp he2
      exact mem_Ico.mpr ⟨hmax q hqs, by omega⟩
  have haS : a ∉ S := fun haS => ha (mem_filter.mp haS).1
  have hS : S.card < N := by
    have := (card_le_card hsub).trans (hK a.start)
    rw [card_insert_of_notMem haS] at this
    omega
  -- a colour below `N` is free on those families
  obtain ⟨c, hcN, hcS⟩ := exists_mem_notMem_of_card_lt_card
    (s := S.image color) (t := range N) (by rw [card_range]; exact card_image_le.trans_lt hS)
  have hc : c < N := mem_range.mp hcN
  have hfree : ∀ q ∈ s, color q = c → Disjoint q.edges a.edges := by
    intro q hq hqc
    by_contra hmeet
    exact hcS (mem_image.mpr ⟨q, mem_filter.mpr ⟨hq, hmeet⟩, hqc⟩)
  refine ⟨Function.update color a c, fun q hq => ?_, fun q hq q' hq' hne hcol => ?_⟩
  · rcases mem_insert.mp hq with rfl | hqs
    · rw [Function.update_self]
      exact hc
    · rw [Function.update_of_ne (by rintro rfl; exact ha hqs)]
      exact hcolor q hqs
  · rcases mem_insert.mp hq with rfl | hqs <;> rcases mem_insert.mp hq' with rfl | hq's
    · exact absurd rfl hne
    · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hq's)] at hcol
      exact (hfree q' hq's hcol.symm).symm
    · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hqs)] at hcol
      exact hfree q hqs hcol
    · rw [Function.update_of_ne (by rintro rfl; exact ha hqs),
        Function.update_of_ne (by rintro rfl; exact ha hq's)] at hcol
      exact hdisj q hqs q' hq's hne hcol

end MergeDepth
