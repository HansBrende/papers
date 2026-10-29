import SourceCovers.NativeExcursion
import SourceCovers.NativeWalkLocal
import TransposeFollowup.ExcursionPulse

set_option autoImplicit false

/-! One literal up/down/up sweep, reusing the earlier capped ramps.
All actual long returns are derived from its entry times. -/

namespace SourceCovers.NativeSweep

open Finset BoundedNesting TransposeFollowup

def walk (h s t : ℕ) : ℤ :=
  excursionPulse h s (s + h) t + cappedRamp h (s + 2 * h) t

theorem before (h s : ℕ) {t : ℕ} (ht : t ≤ s) : walk h s t = 0 := by
  dsimp [walk, excursionPulse, cappedRamp]
  omega

theorem rise (h s : ℕ) {t : ℕ} (ht : s ≤ t) (hu : t ≤ s + h) :
    walk h s t = (t - s : ℕ) := by
  dsimp [walk, excursionPulse, cappedRamp]
  omega

theorem fall (h s : ℕ) {t : ℕ} (ht : s + h ≤ t) (hu : t ≤ s + 2 * h) :
    walk h s t = (s + 2 * h - t : ℕ) := by
  dsimp [walk, excursionPulse, cappedRamp]
  omega

theorem rise_again (h s : ℕ) {t : ℕ} (ht : s + 2 * h ≤ t) (hu : t ≤ s + 3 * h) :
    walk h s t = (t - (s + 2 * h) : ℕ) := by
  dsimp [walk, excursionPulse, cappedRamp]
  omega

theorem after (h s : ℕ) {t : ℕ} (ht : s + 3 * h ≤ t) : walk h s t = h := by
  dsimp [walk, excursionPulse, cappedRamp]
  omega

theorem bounds (h s t : ℕ) : 0 ≤ walk h s t ∧ walk h s t ≤ h := by
  dsimp [walk, excursionPulse, cappedRamp]
  omega

@[simp] theorem zero (h s : ℕ) : walk h s 0 = 0 := before _ _ (Nat.zero_le _)

theorem isWalk (h s : ℕ) : IsWalk (walk h s) := by
  intro t
  by_cases ht : t < s + 2 * h
  · have h₀ : cappedRamp h (s + 2 * h) t = 0 := by dsimp [cappedRamp]; omega
    have h₁ : cappedRamp h (s + 2 * h) (t + 1) = 0 := by dsimp [cappedRamp]; omega
    simpa only [walk, h₀, h₁, add_zero] using excursionPulse_unitSteps h s (s + h) t
  · have h₀ : excursionPulse h s (s + h) t = 0 :=
      excursionPulse_after (by omega) (by omega)
    have h₁ : excursionPulse h s (s + h) (t + 1) = 0 :=
      excursionPulse_after (by omega) (by omega)
    have hc := cappedRamp_step h (s + 2 * h) t
    simp only [walk, h₀, h₁, zero_add, abs_le]
    omega

/-- Every positive-time entry is on one of the three moving legs. -/
theorem entry_cases (h s : ℕ) {t : ℕ} (ht : 0 < t)
    (he : walk h s t ≠ walk h s (t - 1)) :
    ∃ a : ℕ, a ≤ h ∧ walk h s t = a ∧
      ((0 < a ∧ t = s + a) ∨
       (a < h ∧ t = s + 2 * h - a) ∨
       (0 < a ∧ t = s + 2 * h + a)) := by
  by_cases hs : t ≤ s
  · exact False.elim (he ((before h s hs).trans (before h s (by omega)).symm))
  by_cases h₁ : t ≤ s + h
  · refine ⟨t - s, by omega, rise h s (by omega) h₁, Or.inl ⟨by omega, by omega⟩⟩
  by_cases h₂ : t ≤ s + 2 * h
  · refine ⟨s + 2 * h - t, by omega, fall h s (by omega) h₂,
      Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
  by_cases h₃ : t ≤ s + 3 * h
  · refine ⟨t - (s + 2 * h), by omega, rise_again h s (by omega) h₃,
      Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
  exact False.elim (he ((after h s (by omega)).trans (after h s (by omega)).symm))

theorem upper_inside {h s a t : ℕ}
    (hp : s + a < t) (hu : t < s + 2 * h - a) : (a : ℤ) < walk h s t := by
  by_cases hm : t ≤ s + h
  · rw [rise h s (by omega) hm]
    omega
  · rw [fall h s (by omega) (by omega)]
    omega

theorem lower_inside {h s a t : ℕ} (hah : a ≤ h)
    (hp : s + 2 * h - a < t) (hu : t < s + 2 * h + a) : walk h s t < a := by
  by_cases hm : t ≤ s + 2 * h
  · rw [fall h s (by omega) hm]
    omega
  · rw [rise_again h s (by omega) (by omega)]
    omega

theorem upper_hop {h s a T : ℕ} (ha : a < h) (hT : s + 2 * h - a < T) :
    IsHop (walk h s) T (s + a) (s + 2 * h - a) := by
  refine ⟨by omega, hT, ?_, ?_⟩
  · rw [rise h s (t := s + a) (by omega) (by omega),
      fall h s (t := s + 2 * h - a) (by omega) (by omega)]
    congr 1
    omega
  · intro t ht
    obtain ⟨hp, hu⟩ := mem_Ioo.mp ht
    rw [rise h s (t := s + a) (by omega) (by omega)]
    simpa using (upper_inside hp hu).ne'

theorem lower_hop {h s a T : ℕ} (ha : 0 < a) (hah : a ≤ h)
    (hT : s + 2 * h + a < T) :
    IsHop (walk h s) T (s + 2 * h - a) (s + 2 * h + a) := by
  refine ⟨by omega, hT, ?_, ?_⟩
  · rw [fall h s (t := s + 2 * h - a) (by omega) (by omega),
      rise_again h s (t := s + 2 * h + a) (by omega) (by omega)]
    congr 1
    omega
  · intro t ht
    obtain ⟨hp, hu⟩ := mem_Ioo.mp ht
    rw [fall h s (t := s + 2 * h - a) (by omega) (by omega)]
    have he : s + 2 * h - (s + 2 * h - a) = a := by omega
    simpa only [he] using (lower_inside hah hp hu).ne

theorem upper_owner {h s a : ℕ} (ha : a < h) :
    hopOwner (walk h s) (s + a) (s + 2 * h - a) = s + h := by
  have hp : walk h s (s + a) = a := by rw [rise h s (by omega) (by omega)]; congr 1; omega
  have ho : walk h s (s + h) = h := by rw [rise h s (by omega) (by omega)]; congr 1; omega
  apply NativeWalkLocal.hopOwner_eq_of_first_max (by omega) (by omega) (by omega)
  · intro t ht hu
    have hi := upper_inside ht hu
    have hb := bounds h s t
    rw [hp, ho, abs_of_pos (show (0 : ℤ) < h - a by omega), abs_le]
    omega
  · intro t ht hu
    have he := rise h s (t := t) (by omega) (by omega)
    rw [hp, ho, he, abs_of_pos (show (0 : ℤ) < h - a by omega), abs_lt]
    omega

theorem lower_owner {h s a : ℕ} (ha : 0 < a) (hah : a ≤ h) :
    hopOwner (walk h s) (s + 2 * h - a) (s + 2 * h + a) = s + 2 * h := by
  have hp : walk h s (s + 2 * h - a) = a := by
    rw [fall h s (by omega) (by omega)]
    congr 1
    omega
  have ho : walk h s (s + 2 * h) = 0 := by rw [fall h s (by omega) (by omega)]; simp
  apply NativeWalkLocal.hopOwner_eq_of_first_max (by omega) (by omega) (by omega)
  · intro t ht hu
    have hi := lower_inside hah ht hu
    have hb := bounds h s t
    rw [hp, ho]
    simp only [zero_sub, abs_neg, abs_of_nonneg (show (0 : ℤ) ≤ a by omega), abs_le]
    omega
  · intro t ht hu
    have he := fall h s (t := t) (by omega) (by omega)
    rw [hp, ho, he]
    simp only [zero_sub, abs_neg, abs_of_nonneg (show (0 : ℤ) ≤ a by omega), abs_lt]
    omega

/-- Parking contributes no additional nonadjacent return, and both
the upper and lower turns are included. -/
theorem hop_iff (h s T p u : ℕ) : IsHop (walk h s) T p u ↔
    u < T ∧ ((∃ a < h, p = s + a ∧ u = s + 2 * h - a) ∨
      ∃ a, 0 < a ∧ a ≤ h ∧ p = s + 2 * h - a ∧ u = s + 2 * h + a) := by
  constructor
  · intro hh
    refine ⟨hh.2.1, ?_⟩
    have he : walk h s u ≠ walk h s (u - 1) := by
      intro he
      exact hh.2.2.2 (u - 1) (mem_Ioo.mpr ⟨by have := hh.1; omega, by have := hh.1; omega⟩)
        (he.symm.trans hh.2.2.1)
    obtain ⟨a, hah, hva, ha | ha | ha⟩ := entry_cases h s (by have := hh.1; omega) he
    · have hp : walk h s p < a := by
        have hpu := hh.1
        dsimp [walk, excursionPulse, cappedRamp]
        omega
      exact False.elim (hp.ne (hh.2.2.1.symm.trans hva))
    · have hc : IsHop (walk h s) T (s + a) u := by
        rw [ha.2]
        exact upper_hop ha.1 (ha.2 ▸ hh.2.1)
      exact Or.inl ⟨a, ha.1, hop_end_unique hh hc, ha.2⟩
    · have hc : IsHop (walk h s) T (s + 2 * h - a) u := by
        rw [ha.2]
        exact lower_hop ha.1 hah (ha.2 ▸ hh.2.1)
      exact Or.inr ⟨a, ha.1, hah, hop_end_unique hh hc, ha.2⟩
  · rintro ⟨hT, ⟨a, ha, rfl, rfl⟩ | ⟨a, ha, hah, rfl, rfl⟩⟩
    · exact upper_hop ha hT
    · exact lower_hop ha hah hT

theorem hop_bounds {h s T p u : ℕ} (hh : IsHop (walk h s) T p u) :
    s ≤ p ∧ u ≤ s + 3 * h := by
  obtain ⟨_, ⟨a, ha, rfl, rfl⟩ | ⟨a, ha, hah, rfl, rfl⟩⟩ := (hop_iff h s T p u).mp hh
  all_goals omega

theorem entries_zero_subset (h s T : ℕ) : entries (walk h s) 0 T ⊆ {0, s + 2 * h} := by
  intro t ht
  obtain ⟨he, hprev⟩ := (mem_filter.mp ht).2
  rcases hprev with rfl | hprev
  · simp
  · by_cases ht : t = 0
    · simp [ht]
    obtain ⟨a, _, ha, h₁ | h₂ | h₃⟩ := entry_cases h s (t := t) (by omega)
      (fun hn => hprev (hn.symm.trans he))
    · omega
    · have : a = 0 := by omega
      simp [h₂.2, this]
    · omega

theorem entries_nonzero_subset (h s T : ℕ) {c : ℤ} (hc : c ≠ 0) :
    entries (walk h s) c T ⊆ {s + c.toNat, s + 2 * h - c.toNat, s + 2 * h + c.toNat} := by
  intro t ht
  obtain ⟨he, hprev⟩ := (mem_filter.mp ht).2
  have ht0 : t ≠ 0 := by rintro rfl; simp only [zero] at he; exact hc he.symm
  have hprev' := hprev.resolve_left ht0
  obtain ⟨a, _, ha, h₁ | h₂ | h₃⟩ := entry_cases h s (t := t) (by omega)
    (fun hn => hprev' (hn.symm.trans he))
  all_goals
    have hac : a = c.toNat := by omega
    simp_all

theorem entries_card_le_three (h s : ℕ) (c : ℤ) (T : ℕ) :
    (entries (walk h s) c T).card ≤ 3 := by
  by_cases hc : c = 0
  · subst c
    exact (card_le_card (entries_zero_subset h s T)).trans
      ((card_insert_le _ _).trans (by simp))
  · have hb := card_insert_le (s + 2 * h - c.toNat) ({s + 2 * h + c.toNat} : Finset ℕ)
    exact (card_le_card (entries_nonzero_subset h s T hc)).trans
      ((card_insert_le _ _).trans (by simp only [card_singleton] at hb; omega))

theorem entries_top_subset {h : ℕ} (hh : 0 < h) (s T : ℕ) :
    entries (walk h s) h T ⊆ {s + h, s + 3 * h} := by
  intro t ht
  obtain ⟨he, hprev⟩ := (mem_filter.mp ht).2
  have ht0 : t ≠ 0 := by rintro rfl; simp only [zero] at he; omega
  have hprev' := hprev.resolve_left ht0
  obtain ⟨a, _, ha, h₁ | h₂ | h₃⟩ := entry_cases h s (t := t) (by omega)
    (fun hn => hprev' (hn.symm.trans he))
  all_goals
    have hah : a = h := by omega
    simp only [mem_insert, mem_singleton]
    omega

theorem entries_top_card {h : ℕ} (hh : 0 < h) (s T : ℕ) :
    (entries (walk h s) h T).card ≤ 2 :=
  (card_le_card (entries_top_subset hh s T)).trans ((card_insert_le _ _).trans (by simp))

end SourceCovers.NativeSweep
