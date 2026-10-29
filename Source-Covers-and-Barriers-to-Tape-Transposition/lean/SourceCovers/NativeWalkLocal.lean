import SourceCovers.FamilyAccounting

set_option autoImplicit false

/-! Local equality up to a spatial translation preserves actual hops and
their original first-maximum-distance owners. -/

namespace SourceCovers.NativeWalkLocal

open Finset BoundedNesting

theorem entries_const_card_le_one (b c : ℤ) (T : ℕ) :
    (entries (fun _ => b) c T).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha a' ha'
  have ha₀ := (mem_filter.mp ha).2.2.resolve_right
    (fun hn => hn (mem_filter.mp ha).2.1)
  have ha₀' := (mem_filter.mp ha').2.2.resolve_right
    (fun hn => hn (mem_filter.mp ha').2.1)
  exact ha₀.trans ha₀'.symm

theorem hop_iff_of_shift_on {x y : ℕ → ℤ} {T p u : ℕ} (c : ℤ)
    (he : ∀ t, p ≤ t → t ≤ u → x t = c + y t) :
    IsHop x T p u ↔ IsHop y T p u := by
  constructor
  · rintro ⟨hl, hT, heq, hne⟩
    have hp : p ≤ u := by omega
    refine ⟨hl, hT, ?_, ?_⟩
    · rw [he u hp le_rfl, he p le_rfl hp] at heq
      exact add_left_cancel heq
    · intro t ht hn
      obtain ⟨hpt, htu⟩ := mem_Ioo.mp ht
      apply hne t ht
      rw [he t hpt.le htu.le, he p le_rfl hp, hn]
  · rintro ⟨hl, hT, heq, hne⟩
    have hp : p ≤ u := by omega
    refine ⟨hl, hT, ?_, ?_⟩
    · rw [he u hp le_rfl, he p le_rfl hp, heq]
    · intro t ht hn
      obtain ⟨hpt, htu⟩ := mem_Ioo.mp ht
      rw [he t hpt.le htu.le, he p le_rfl hp] at hn
      exact hne t ht (add_left_cancel hn)

/-- A certified first maximizer agrees with the original canonical owner. -/
theorem hopOwner_eq_of_first_max {x : ℕ → ℤ} {p u o : ℕ}
    (hl : p + 2 ≤ u) (hp : p < o) (hu : o < u)
    (hmax : ∀ t, p < t → t < u → |x t - x p| ≤ |x o - x p|)
    (hfirst : ∀ t, p < t → t < o → |x t - x p| < |x o - x p|) :
    hopOwner x p u = o := by
  obtain ⟨ha, hb, hm, hf⟩ := hopOwner_spec x hl
  rcases lt_trichotomy (hopOwner x p u) o with h | h | h
  · exact False.elim (not_lt_of_ge (hm o hp hu) (hfirst _ ha h))
  · exact h
  · exact False.elim (not_lt_of_ge (hmax _ ha hb) (hf o hp h))

theorem hopOwner_eq_of_shift_on {x y : ℕ → ℤ} {p u : ℕ} (c : ℤ)
    (hl : p + 2 ≤ u) (he : ∀ t, p ≤ t → t ≤ u → x t = c + y t) :
    hopOwner x p u = hopOwner y p u := by
  obtain ⟨ha, hb, hm, hf⟩ := hopOwner_spec y hl
  have hd (t : ℕ) (ht : p ≤ t) (hu : t ≤ u) : |x t - x p| = |y t - y p| := by
    rw [he t ht hu, he p le_rfl (by omega), add_sub_add_left_eq_sub]
  apply hopOwner_eq_of_first_max hl ha hb
  · intro t ht hu
    simpa only [hd t ht.le hu.le, hd _ ha.le hb.le] using hm t ht hu
  · intro t ht hu
    simpa only [hd t ht.le (hu.trans hb).le, hd _ ha.le hb.le] using hf t ht hu

end SourceCovers.NativeWalkLocal
