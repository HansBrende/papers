import SourceCovers.ShadowInvariants
import LeanMachine.ScheduledExcursion

set_option autoImplicit false

/-! Constructed paused excursions use the original actual-hop and
first-maximum-owner definitions. The full family is derived from the walk. -/

namespace SourceCovers.NativeExcursion

open Finset BoundedNesting LeanMachine.ScheduledExcursion
noncomputable section

variable {h k T : ℕ}

def walk (D : Schedule h) (t : ℕ) : ℤ := D.height t

theorem isWalk (D : Schedule h) : IsWalk (walk D) := by
  intro t
  have hs := D.height_step t
  simp only [walk, abs_le]
  omega

@[simp] theorem walk_zero (D : Schedule h) : walk D 0 = 0 := by simp [walk]

/-- The original previous-visit relation contains precisely the scheduled returns. -/
theorem hop_iff (D : Schedule h) (T p u : ℕ) :
    IsHop (walk D) T p u ↔ u < T ∧ ∃ i : Fin h, p = D.depart i ∧ u = D.arrive i := by
  constructor
  · rintro ⟨hl, hT, heq, hne⟩
    refine ⟨hT, (D.return_iff p u).mp ⟨hl, Int.ofNat_inj.mp heq, ?_⟩⟩
    intro t hp hu he
    exact hne t (mem_Ioo.mpr ⟨hp, hu⟩) (congrArg Int.ofNat he)
  · rintro ⟨hT, hi⟩
    obtain ⟨hl, heq, hne⟩ := (D.return_iff p u).mpr hi
    refine ⟨hl, hT, congrArg Int.ofNat heq, ?_⟩
    intro t ht he
    exact hne t (mem_Ioo.mp ht).1 (mem_Ioo.mp ht).2 (Int.ofNat_inj.mp he)

theorem upperHop (D : Schedule h) (i : Fin h) :
    IsUpperHop (walk D) (D.depart i) (D.arrive i) := by
  refine ⟨by have := D.separated i i; omega, ?_, ?_⟩
  · simp only [walk, D.height_arrive, D.height_depart]
  · intro t hp hu
    have ht := (D.lt_height_iff i t).mpr ⟨hp, hu⟩
    simpa only [walk, D.height_depart, Nat.cast_lt] using ht

/-- All returns have the same first peak, including a held peak. -/
theorem hopOwner_eq (D : Schedule h) (i : Fin h) :
    hopOwner (walk D) (D.depart i) (D.arrive i) = D.peak := by
  have hu := upperHop D i
  obtain ⟨hlo, hhi, hmax, hfirst⟩ := hopOwner_spec (walk D) hu.long
  have habs : ∀ t, D.depart i < t → t < D.arrive i →
      |walk D t - walk D (D.depart i)| = walk D t - walk D (D.depart i) :=
    fun t ht hu' => abs_of_pos (sub_pos.mpr (hu.above t ht hu'))
  have ho : IsOwner (walk D) (D.depart i) (D.arrive i)
      (hopOwner (walk D) (D.depart i) (D.arrive i)) := by
    refine ⟨hlo, hhi, ?_, ?_⟩
    · intro t hp ht
      have hh := hmax t hp ht
      rw [habs t hp ht, habs _ hlo hhi] at hh
      omega
    · intro t hp ht
      have hh := hfirst t hp ht
      rw [habs t hp (ht.trans hhi), habs _ hlo hhi] at hh
      omega
  apply ho.unique
  refine ⟨D.depart_lt_peak i, D.peak_lt_arrive i, ?_, ?_⟩
  · intro t _ _
    simpa only [walk, D.height_peak, Nat.cast_le] using D.height_le t
  · intro t _ ht
    simpa only [walk, D.height_peak, Nat.cast_lt] using D.height_lt_peak i.pos ht

/-- The supplied head of a multihead geometry has the actual canonical key. -/
theorem hop_key (D : Schedule h) {xs : Fin k → ℕ → ℤ} {head : Fin k}
    (hx : xs head = walk D) (i : Fin h) :
    key xs (actualOwner xs) (head, D.depart i, D.arrive i) = (head, true, D.peak) := by
  have ha := (upperHop D i).above (D.depart i + 1) (by omega)
    (by have := D.separated i i; omega)
  simp only [key, side, actualOwner, hx, ha, decide_true, hopOwner_eq]

/-- Each cell has at most one entry before the peak and one afterwards.
The initial visit at time zero is counted, as in the original entry convention. -/
theorem entries_card_le_two (D : Schedule h) (c : ℤ) (T : ℕ) :
    (entries (walk D) c T).card ≤ 2 := by
  have hbad : ∀ a ∈ entries (walk D) c T, ∀ b ∈ entries (walk D) c T,
      a < b → (a ≤ D.peak ↔ b ≤ D.peak) → False := by
    intro a ha b hb hab hside
    obtain ⟨haeq, _⟩ := (mem_filter.mp ha).2
    obtain ⟨hbeq, hbprev⟩ := (mem_filter.mp hb).2
    have hprev : walk D (b - 1) ≠ c := hbprev.resolve_left (by omega)
    by_cases hbp : b ≤ D.peak
    · have hap := hside.mpr hbp
      have hl := D.height_mono_before hap (show b - 1 ≤ D.peak by omega) (show a ≤ b - 1 by omega)
      have hr := D.height_mono_before (show b - 1 ≤ D.peak by omega) hbp (Nat.sub_le b 1)
      apply hprev
      dsimp only [walk] at haeq hbeq ⊢
      omega
    · have hap : D.peak ≤ a := by
        have han : ¬ a ≤ D.peak := fun ha' => hbp (hside.mp ha')
        omega
      have hl := D.height_anti_after hap (show D.peak ≤ b - 1 by omega) (show a ≤ b - 1 by omega)
      have hr := D.height_anti_after (show D.peak ≤ b - 1 by omega)
        (show D.peak ≤ b by omega) (Nat.sub_le b 1)
      apply hprev
      dsimp only [walk] at haeq hbeq ⊢
      omega
  have hinj : Set.InjOn (fun t : ℕ => decide (t ≤ D.peak)) (entries (walk D) c T) := by
    intro a ha b hb he
    have hs : a ≤ D.peak ↔ b ≤ D.peak := by simpa only [decide_eq_decide] using he
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact False.elim (hbad a ha b hb hab hs)
    · rfl
    · exact False.elim (hbad b hb a ha hba hs.symm)
  simpa using card_le_card_of_injOn (fun t : ℕ => decide (t ≤ D.peak))
    (fun _ _ => mem_univ _) hinj

variable [NeZero h]

/-- The complete actual family on an excursion head. Its outer return is
already before the horizon, so every nested return is before it too. -/
def family (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) : ActualFamily xs T :=
  ⟨(head, true, D.peak), mem_image.mpr
    ⟨(head, D.depart 0, D.arrive 0), mem_allHops.mpr (by
      rw [hx, hop_iff]
      exact ⟨hT, 0, rfl, rfl⟩), hop_key D hx 0⟩⟩

theorem family_hops (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) :
    (family D head hx hT).hops =
      univ.image (fun i : Fin h => (head, D.depart i, D.arrive i)) := by
  ext η
  constructor
  · intro hη
    obtain ⟨hHop, hhead, _, _⟩ := mem_fam.mp hη
    have hh := mem_allHops.mp hHop
    change η.1 = head at hhead
    rw [hhead, hx, hop_iff] at hh
    obtain ⟨i, hp, hu⟩ := hh.2
    exact mem_image.mpr ⟨i, mem_univ i, Prod.ext hhead.symm (Prod.ext hp.symm hu.symm)⟩
  · intro hη
    obtain ⟨i, _, rfl⟩ := mem_image.mp hη
    apply mem_filter.mpr
    refine ⟨mem_allHops.mpr ?_, hop_key D hx i⟩
    rw [hx, hop_iff]
    exact ⟨(D.arrive_strictAnti.antitone (Fin.zero_le i)).trans_lt hT, i, rfl, rfl⟩

theorem family_card (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) :
    (family D head hx hT).hops.card = h := by
  rw [family_hops, card_image_of_injective]
  · simp
  · intro i j hij
    exact D.depart_strictMono.injective (congrArg (fun η => η.2.1) hij)

theorem family_start (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) :
    (family D head hx hT).start = D.depart 0 := by
  change ((family D head hx hT).hops.inf' (family D head hx hT).nonempty
    (fun η : Fin k × ℕ × ℕ => η.2.1)) = D.depart 0
  apply le_antisymm
  · exact inf'_le (s := (family D head hx hT).hops) (fun η => η.2.1) (by
      rw [family_hops]
      exact mem_image.mpr ⟨0, mem_univ _, rfl⟩)
  · apply le_inf'
    intro η hη
    rw [family_hops] at hη
    obtain ⟨i, _, rfl⟩ := mem_image.mp hη
    exact D.depart_strictMono.monotone (Fin.zero_le i)

theorem family_stop (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) :
    (family D head hx hT).stop = D.arrive 0 := by
  change ((family D head hx hT).hops.sup (fun η : Fin k × ℕ × ℕ => η.2.2)) = D.arrive 0
  apply le_antisymm
  · apply Finset.sup_le
    intro η hη
    rw [family_hops] at hη
    obtain ⟨i, _, rfl⟩ := mem_image.mp hη
    exact D.arrive_strictAnti.antitone (Fin.zero_le i)
  · exact Finset.le_sup (s := (family D head hx hT).hops) (f := fun η => η.2.2) (by
      rw [family_hops]
      exact mem_image.mpr ⟨0, mem_univ _, rfl⟩)

@[simp] theorem family_owner (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) :
    (family D head hx hT).owner = D.peak := rfl

theorem mem_family (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) (i : Fin h) :
    (head, D.depart i, D.arrive i) ∈ (family D head hx hT).hops := by
  rw [family_hops]
  exact mem_image.mpr ⟨i, mem_univ _, rfl⟩

/-- The scheduled return alone determines the held value; no hypotheses
about any other head are needed. -/
theorem family_held_arrive (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) (i : Fin h) :
    (family D head hx hT).held (D.arrive i) = D.depart i := by
  apply le_antisymm
  · have hh := inf'_le
      (fun η : Fin k × ℕ × ℕ => if η.2.2 ≤ D.arrive i then η.2.1 else D.peak)
      (mem_family D head hx hT i)
    simpa only [ActualFamily.held, family_owner, ite_eq_left le_rfl] using hh
  · apply le_inf'
    intro η hη
    rw [family_hops] at hη
    obtain ⟨j, _, rfl⟩ := mem_image.mp hη
    by_cases he : D.arrive j ≤ D.arrive i
    · simp only [ite_eq_left he]
      exact D.depart_strictMono.monotone
        (le_of_not_gt fun hij => (not_lt_of_ge he) (D.arrive_strictAnti hij))
    · simpa only [ite_eq_right he, family_owner] using (D.depart_lt_peak i).le

theorem family_shadow_arrive (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) (i : Fin h) :
    (family D head hx hT).shadow (D.arrive i) = max (D.depart 0 + 1) (D.depart i) := by
  let F := family D head hx hT
  have ht : D.arrive i ∈ F.shadowAction.domain := by
    change F.owner < D.arrive i ∧ D.arrive i ≤ F.stop
    rw [family_owner, family_stop]
    exact ⟨D.peak_lt_arrive i, D.arrive_strictAnti.antitone (Fin.zero_le i)⟩
  rw [ActualFamily.shadow, F.shadowAction.apply_eq ht]
  change max (F.start + 1) (F.held (D.arrive i)) = _
  rw [family_start, family_held_arrive]

theorem family_shadow_exact (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) {i : Fin h} (hi : i ≠ 0) :
    (family D head hx hT).shadow (D.arrive i) = D.depart i := by
  rw [family_shadow_arrive, max_eq_right]
  exact D.depart_strictMono (Fin.pos_iff_ne_zero.mpr hi)

theorem family_shadow_held (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T) {t : ℕ}
    (ht : D.peak < t) (hbefore : ∀ i, t < D.arrive i) :
    (family D head hx hT).shadow t = D.peak := by
  let F := family D head hx hT
  have hh : F.held t = F.owner := F.held_initial t (by
    intro η hη
    rw [family_hops] at hη
    obtain ⟨i, _, rfl⟩ := mem_image.mp hη
    exact hbefore i)
  have hdom : t ∈ F.shadowAction.domain := by
    change F.owner < t ∧ t ≤ F.stop
    rw [family_owner, family_stop]
    exact ⟨ht, (hbefore 0).le⟩
  rw [ActualFamily.shadow, F.shadowAction.apply_eq hdom]
  change max (F.start + 1) (F.held t) = _
  rw [hh, max_eq_right F.owner_bounds.1]
  rfl

/-- Exhaustiveness is about the whole actual-family system, not a selected list. -/
theorem family_unique (D : Schedule h) {xs : Fin k → ℕ → ℤ} (head : Fin k)
    (hx : xs head = walk D) (hT : D.arrive 0 < T)
    (F : ActualFamily xs T) (hhead : F.val.1 = head) : F = family D head hx hT := by
  obtain ⟨η, hη⟩ := F.nonempty
  obtain ⟨hHop, hηhead, _, _⟩ := mem_fam.mp hη
  have hh := mem_allHops.mp hHop
  have hhhead : η.1 = head := hηhead.trans hhead
  rw [hhhead, hx, hop_iff] at hh
  obtain ⟨i, hp, hu⟩ := hh.2
  apply Subtype.ext
  have hkey := (mem_filter.mp hη).2
  rw [show η = (head, D.depart i, D.arrive i) from Prod.ext hhhead (Prod.ext hp hu),
    hop_key D hx] at hkey
  exact hkey.symm

end
end SourceCovers.NativeExcursion
