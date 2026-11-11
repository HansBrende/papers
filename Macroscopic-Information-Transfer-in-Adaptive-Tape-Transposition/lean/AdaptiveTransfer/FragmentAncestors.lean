import AdaptiveTransfer.Fragments
import AdaptiveTransfer.FrozenCutInvoice

/-! Literal cut-free ancestors in the native dependency graph. Both cut
endpoints are excluded, and all state/latest-visit closure used by fragment
replay is derived from paths, rather than supplied as a certificate. -/

namespace AdaptiveTransfer
open Finset SourceCovers BoundedNesting MergeDepth NativeRelations

private theorem path_append_edge {k T : ℕ} {xs : Fin k → ℕ → ℤ} :
    ∀ (ρ : List ℕ) (t u : ℕ), IsDepPath xs T (t :: ρ) →
      DepStep xs T ((t :: ρ).getLastD t) u → IsDepPath xs T (t :: (ρ ++ [u]))
  | [], _t, _u, _hp, he => ⟨he, trivial⟩
  | v :: ρ, t, u, hp, he => by
      exact ⟨hp.1, path_append_edge ρ v u hp.2 (by simpa only [LinNet.getLastD_cons_cons] using he)⟩

noncomputable def cutFreeAncestors {k : ℕ} (xs : Fin k → ℕ → ℤ)
    (T : ℕ) (roots B : Finset ℕ) : Finset ℕ := by
  classical
  exact (range T).filter fun t => ∃ r ∈ roots, ∃ ρ : List ℕ,
    IsDepPath xs T (r :: ρ) ∧ (∀ u ∈ r :: ρ, u ∉ B) ∧ (r :: ρ).getLastD r = t

theorem cutFreeAncestors_time {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ}
    {roots B : Finset ℕ} {t : ℕ} (ht : t ∈ cutFreeAncestors xs T roots B) : t < T := by
  classical
  exact mem_range.mp (mem_filter.mp ht).1

theorem cutFreeAncestors_not_cut {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ}
    {roots B : Finset ℕ} {t : ℕ} (ht : t ∈ cutFreeAncestors xs T roots B) : t ∉ B := by
  classical
  obtain ⟨r, _hr, ρ, _hp, hfree, he⟩ := (mem_filter.mp ht).2
  exact he ▸ hfree _ (by simpa only [List.getLastD_cons] using List.getLastD_mem_cons (l := ρ) (a := r))

theorem root_mem_cut_or_ancestors {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ}
    {roots B : Finset ℕ} {r : ℕ} (hr : r ∈ roots) (hrT : r < T) :
    r ∈ cutFreeAncestors xs T roots B ∪ B := by
  classical
  by_cases hrB : r ∈ B
  · exact mem_union_right _ hrB
  · apply mem_union_left
    refine mem_filter.mpr ⟨mem_range.mpr hrT, r, hr, [], trivial, ?_, rfl⟩
    intro u hu
    simpa only [List.mem_singleton.mp hu] using hrB

theorem cutFreeAncestors_parent {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ}
    {roots B : Finset ℕ} {t u : ℕ} (ht : t ∈ cutFreeAncestors xs T roots B)
    (hdep : DepStep xs T t u) (huB : u ∉ B) : u ∈ cutFreeAncestors xs T roots B := by
  classical
  obtain ⟨r, hr, ρ, hp, hfree, he⟩ := (mem_filter.mp ht).2
  refine mem_filter.mpr ⟨mem_range.mpr ((depStep_lt hdep).1.trans (cutFreeAncestors_time ht)),
    r, hr, ρ ++ [u], path_append_edge ρ r u hp (he ▸ hdep), ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ (r :: ρ) ++ [u] := hv
    rcases List.mem_append.mp hv' with hvr | hvu
    · exact hfree v hvr
    · simpa only [List.mem_singleton.mp hvu] using huB
  · simpa only [List.cons_append] using (List.getLastD_concat (l := r :: ρ) (a := r) (b := u))

/-- The full endpoint-inclusive separator excludes every target read from
the literal retained ancestor set. -/
theorem cutFreeAncestors_avoid_targets {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ}
    {roots targets B : Finset ℕ} (hcut : IsMengerVertexCut xs T roots targets B)
    {t : ℕ} (ht : t ∈ cutFreeAncestors xs T roots B) : t ∉ targets := by
  classical
  intro htarget
  obtain ⟨r, hr, ρ, hp, hfree, he⟩ := (mem_filter.mp ht).2
  obtain ⟨v, hv, hvB⟩ := hcut ρ r hr hp (he ▸ htarget)
  exact hfree v hv hvB

theorem cutFreeAncestors_state_closed {k : ℕ} (xs : Fin k → ℕ → ℤ)
    (T : ℕ) (roots B : Finset ℕ) : StateClosedExcept (cutFreeAncestors xs T roots B) B := by
  intro t ht htpos hprev
  exact cutFreeAncestors_parent ht (Or.inl ⟨by omega, cutFreeAncestors_time ht⟩) hprev

/-- A literal last visit is a dependency parent, including the adjacent case
which travels through the state edge instead of a nonadjacent work hop. -/
theorem depStep_of_last_visit {k T t p : ℕ} {xs : Fin k → ℕ → ℤ}
    (h : Fin k) (ht : t < T) (hpt : p < t) (he : xs h t = xs h p)
    (hlast : ∀ u, p < u → u < t → xs h t ≠ xs h u) : DepStep xs T t p := by
  by_cases hadj : p + 1 = t
  · exact Or.inl ⟨hadj, ht⟩
  · apply Or.inr
    refine mem_image.mpr ⟨(h, p, t), mem_allHops.mpr (show IsHop (xs h) T p t from ⟨by omega, ht, he, ?_⟩), rfl⟩
    intro u hu hup
    exact hlast u (mem_Ioo.mp hu).1 (mem_Ioo.mp hu).2 (he.trans hup.symm)

theorem cutFreeAncestors_last_parent {k T t p : ℕ} {xs : Fin k → ℕ → ℤ}
    {roots B : Finset ℕ} (ht : t ∈ cutFreeAncestors xs T roots B)
    (h : Fin k) (hpt : p < t) (he : xs h t = xs h p)
    (hlast : ∀ u, p < u → u < t → xs h t ≠ xs h u) :
    p ∈ cutFreeAncestors xs T roots B ∪ B := by
  classical
  by_cases hpB : p ∈ B
  · exact mem_union_right _ hpB
  · exact mem_union_left _ (cutFreeAncestors_parent ht
      (depStep_of_last_visit h (cutFreeAncestors_time ht) hpt he hlast) hpB)

end AdaptiveTransfer
