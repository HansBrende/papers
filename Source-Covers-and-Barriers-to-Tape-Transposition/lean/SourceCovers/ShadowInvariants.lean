import SourceCovers.ClippedShadows

set_option autoImplicit false

/-! Invariant sets for complete actual-family orbits. -/

namespace SourceCovers

open LeanMachine.MonotonePatches

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

namespace ActualFamily

theorem shadow_eq_self_of_le_owner (F : ActualFamily xs T) {t : ℕ}
    (ht : t ≤ F.owner) : F.shadow t = t := by
  by_contra h
  exact (not_lt_of_ge ht) ((F.shadow_ne_self_iff t).mp h).1

theorem shadow_idempotent (F : ActualFamily xs T) (t : ℕ) :
    F.shadow (F.shadow t) = F.shadow t := by
  by_cases h : F.shadow t = t
  · rw [h, h]
  · exact F.shadow_eq_self_of_le_owner
      (F.shadow_active_bounds ((F.shadow_ne_self_iff t).mp h)).2.1

/-- No shadow crosses a cut at or before its outer lower endpoint. -/
theorem shadow_preserves_lower (F : ActualFamily xs T) {c t : ℕ}
    (hc : c ≤ F.start) (ht : c ≤ t) : c ≤ F.shadow t := by
  by_cases h : F.shadow t = t
  · simpa only [h] using ht
  · exact hc.trans (F.shadow_active_bounds ((F.shadow_ne_self_iff t).mp h)).1.le

end ActualFamily

/-- A one-step invariant is an invariant of every finite word, including
the empty word. This concerns the ordinary orbit, without paid truncation. -/
theorem shadowOrbit_subset_of_closed (K : Finset (ActualFamily xs T))
    (S : Set ℕ) {t : ℕ} (ht : t ∈ S)
    (hclosed : ∀ F ∈ K, Set.MapsTo F.shadow S S) : shadowOrbit K t ⊆ S := by
  rintro u ⟨w, hw, rfl⟩
  induction w generalizing t with
  | nil => exact ht
  | cons F w ih =>
    have hw' := List.forall_mem_cons.mp hw
    exact ih (hclosed F hw'.1 ht) hw'.2

end SourceCovers
