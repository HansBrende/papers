import SourceCovers.NativeSweep

set_option autoImplicit false

/-! Appending an up/down/up sweep on a fresh spatial interval preserves
the complete return list and the three-entry bound. -/

namespace SourceCovers.FreshSweep

open Finset BoundedNesting

def append (x : ℕ → ℤ) (c : ℤ) (h s t : ℕ) : ℤ :=
  if t ≤ s then x t else c + NativeSweep.walk h s t

theorem before {x : ℕ → ℤ} {c : ℤ} {h s t : ℕ} (ht : t ≤ s) :
    append x c h s t = x t := by simp only [append, ite_eq_left ht]

theorem on_late {x : ℕ → ℤ} {c : ℤ} {h s t : ℕ}
    (hx : x s = c) (ht : s ≤ t) : append x c h s t = c + NativeSweep.walk h s t := by
  by_cases he : t ≤ s
  · have ht' : t = s := by omega
    subst t
    rw [before le_rfl, hx, NativeSweep.before h s le_rfl, add_zero]
  · exact ite_eq_right he

theorem after {x : ℕ → ℤ} {c : ℤ} {h s t : ℕ}
    (hx : x s = c) (ht : s + 3 * h ≤ t) : append x c h s t = c + h := by
  rw [on_late hx (by omega), NativeSweep.after h s ht]

theorem isWalk {x : ℕ → ℤ} {c : ℤ} {h s : ℕ} (hx : IsWalk x) (hs : x s = c) :
    IsWalk (append x c h s) := by
  intro t
  by_cases ht : t < s
  · simpa only [before (show t + 1 ≤ s by omega), before ht.le] using hx t
  · simpa only [on_late hs (show s ≤ t + 1 by omega), on_late hs (show s ≤ t by omega),
      add_sub_add_left_eq_sub] using NativeSweep.isWalk h s t

theorem bounds {x : ℕ → ℤ} {c : ℤ} {h s : ℕ} (hc : 0 ≤ c)
    (hx : ∀ t ≤ s, 0 ≤ x t ∧ x t ≤ c) (hs : x s = c) (t : ℕ) :
    0 ≤ append x c h s t ∧ append x c h s t ≤ c + h := by
  by_cases ht : t ≤ s
  · rw [before ht]
    have hb := hx t ht
    omega
  · rw [on_late hs (by omega)]
    have hb := NativeSweep.bounds h s t
    omega

theorem hop_before_iff {x : ℕ → ℤ} {c : ℤ} {h s T p u : ℕ} (hu : u ≤ s) :
    IsHop (append x c h s) T p u ↔ IsHop x T p u := by
  apply NativeWalkLocal.hop_iff_of_shift_on 0
  intro t _ ht
  simp only [before (ht.trans hu), zero_add]

theorem hop_after_iff {x : ℕ → ℤ} {c : ℤ} {h s T p u : ℕ}
    (hs : x s = c) (hp : s ≤ p) :
    IsHop (append x c h s) T p u ↔ IsHop (NativeSweep.walk h s) T p u :=
  NativeWalkLocal.hop_iff_of_shift_on c (fun _ ht _ => on_late hs (hp.trans ht))

/-- No return can straddle the splice: the common boundary would be
another intermediate visit of the same cell. -/
theorem hop_iff {x : ℕ → ℤ} {c : ℤ} {h s T p u : ℕ}
    (hs : x s = c) (hx : ∀ t ≤ s, x t ≤ c) :
    IsHop (append x c h s) T p u ↔
      (u ≤ s ∧ IsHop x T p u) ∨
      (s ≤ p ∧ IsHop (NativeSweep.walk h s) T p u) := by
  constructor
  · intro hh
    by_cases hu : u ≤ s
    · exact Or.inl ⟨hu, hop_before_iff hu |>.mp hh⟩
    · have hp : s ≤ p := by
        by_contra! hp
        have hlo : append x c h s p ≤ c := by rw [before hp.le]; exact hx p hp.le
        have hhi : c ≤ append x c h s u := by
          rw [on_late hs (by omega)]
          have := (NativeSweep.bounds h s u).1
          omega
        have heq := hh.2.2.1
        have he : append x c h s p = c := by omega
        apply hh.2.2.2 s (mem_Ioo.mpr ⟨hp, by omega⟩)
        rw [before le_rfl, hs, he]
      exact Or.inr ⟨hp, (hop_after_iff hs hp).mp hh⟩
  · rintro (⟨hu, hh⟩ | ⟨hp, hh⟩)
    · exact (hop_before_iff hu).mpr hh
    · exact (hop_after_iff hs hp).mpr hh

theorem entry_before_iff {x : ℕ → ℤ} {c z : ℤ} {h s t T : ℕ} (ht : t ≤ s) :
    t ∈ entries (append x c h s) z T ↔ t ∈ entries x z T := by
  simp only [entries, mem_filter, before ht, before ((Nat.sub_le t 1).trans ht)]

theorem entry_after_iff {x : ℕ → ℤ} {c z : ℤ} {h s t T : ℕ}
    (hs : x s = c) (ht : s < t) :
    t ∈ entries (append x c h s) z T ↔ t ∈ entries (NativeSweep.walk h s) (z - c) T := by
  simp only [entries, mem_filter, on_late hs ht.le, on_late hs (show s ≤ t - 1 by omega)]
  have ht0 : t ≠ 0 := by omega
  simp only [ht0, false_or, ne_eq, eq_sub_iff_add_eq, add_comm]

theorem entries_below_subset {x : ℕ → ℤ} {c z : ℤ} {h s T : ℕ}
    (hs : x s = c) (hz : z < c) :
    entries (append x c h s) z T ⊆ entries x z T := by
  intro t ht
  by_cases hts : t ≤ s
  · exact (entry_before_iff hts).mp ht
  · have he := (mem_filter.mp ht).2.1
    rw [on_late hs (by omega)] at he
    have := (NativeSweep.bounds h s t).1
    omega

theorem entries_above_subset {x : ℕ → ℤ} {c z : ℤ} {h s T : ℕ}
    (hs : x s = c) (hx : ∀ t ≤ s, x t ≤ c) (hz : c < z) :
    entries (append x c h s) z T ⊆ entries (NativeSweep.walk h s) (z - c) T := by
  intro t ht
  by_cases hts : t ≤ s
  · have he := (mem_filter.mp ht).2.1
    rw [before hts] at he
    have := hx t hts
    omega
  · exact (entry_after_iff hs (Nat.lt_of_not_ge hts)).mp ht

theorem entries_boundary_subset {x : ℕ → ℤ} {c : ℤ} {h s T : ℕ}
    (hs : x s = c) :
    entries (append x c h s) c T ⊆ insert (s + 2 * h) (entries x c T) := by
  intro t ht
  by_cases hts : t ≤ s
  · exact mem_insert_of_mem ((entry_before_iff hts).mp ht)
  · have he := (entry_after_iff hs (Nat.lt_of_not_ge hts)).mp ht
    simp only [sub_self] at he
    have hm := NativeSweep.entries_zero_subset h s T he
    simp only [mem_insert, mem_singleton] at hm
    exact mem_insert.mpr (Or.inl (by omega))

/-- The only shared cell is the old maximum. It gains at most one entry. -/
theorem entries_card_le_three {x : ℕ → ℤ} {c : ℤ} {h s : ℕ}
    (hs : x s = c) (hx : ∀ t ≤ s, x t ≤ c)
    (hentries : ∀ z T, (entries x z T).card ≤ 3)
    (htop : ∀ T, (entries x c T).card ≤ 2) (z : ℤ) (T : ℕ) :
    (entries (append x c h s) z T).card ≤ 3 := by
  rcases lt_trichotomy z c with hz | rfl | hz
  · exact (card_le_card (entries_below_subset hs hz)).trans (hentries z T)
  · have hb := card_le_card (entries_boundary_subset (h := h) (T := T) hs)
    have hi := card_insert_le (s + 2 * h) (entries x z T)
    have hh := htop T
    omega
  · exact (card_le_card (entries_above_subset hs hx hz)).trans
      (NativeSweep.entries_card_le_three h s (z - c) T)

theorem entries_top_card {x : ℕ → ℤ} {c : ℤ} {h s : ℕ}
    (hs : x s = c) (hx : ∀ t ≤ s, x t ≤ c) (hh : 0 < h) (T : ℕ) :
    (entries (append x c h s) (c + h) T).card ≤ 2 := by
  have hi := card_le_card (entries_above_subset (h := h) (T := T) hs hx
    (show c < c + h by omega))
  simp only [add_sub_cancel_left] at hi
  exact hi.trans (NativeSweep.entries_top_card hh s T)

end SourceCovers.FreshSweep
