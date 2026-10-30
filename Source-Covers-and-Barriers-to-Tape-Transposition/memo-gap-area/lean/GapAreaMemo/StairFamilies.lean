import GapAreaMemo.BankShapes

set_option autoImplicit false

/-!
# The actual families of a staircase of zigzags

A head performs a staircase (`Staircase.walk`) of zigzag segments `S j`, `j < n`, spliced at
the times `start j`, each segment finishing by the next splice time and before the horizon `T`
(`Stair`). Its actual families are then exactly `2n` explicit families. Segment `j` contributes

* its **upper family** `Stair.upper`, with key `(head, true, (S j).Z.P.peak)`, whose hops are the
  returns `(P.depart c, P.arrive c)` of its excursion `P` above its base, and
* its **lower family** `Stair.lower`, with key `(head, false, (S j).Z.trough)`, whose hops are
  the returns `(Q.depart i, Q.arrive i)` of its excursion `Q` below its top.

The families are pairwise distinct (`upper_ne_lower`, `upper_ne_upper`, `lower_ne_lower`) and
exhaust the families of the head (`family_cases`).

The sizes, spans, held values and shadows of the two families are those of the schedules `P` and
`Q`. They are derived once, following `NativeExcursion.family`, for any family whose hops are the
returns of a schedule and whose owner is its peak (`IsSchedFamily`): at the return `c` the
shadow is `max (depart 0 + 1) (depart c)`, which is `depart c` for the unpaid returns `c ≠ 0`,
and it keeps that value until the next outer return (`IsSchedFamily.shadow_between`).
-/

namespace SourceCovers.StairFamilies

open Finset BoundedNesting LeanMachine.ScheduledExcursion

noncomputable section

/-! ### Schedules and zigzags -/

/-- A time before the return just outside the return `c` is before every return outside `c`. -/
theorem lt_arrive_of_lt_pred {h : ℕ} (D : Schedule h) (c : Fin h) {t : ℕ}
    (ht : t < D.arrive ⟨c.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) c.isLt⟩)
    (c' : Fin h) (hc' : c' < c) : t < D.arrive c' :=
  ht.trans_le (D.arrive_strictAnti.antitone (Fin.le_iff_val_le_val.mpr
    (show c'.val ≤ c.val - 1 by have := Fin.lt_def.mp hc'; omega)))

/-- A time before the innermost return is before every return. -/
theorem lt_arrive_of_lt_last {h : ℕ} (D : Schedule h) (hh : 0 < h) {t : ℕ}
    (ht : t < D.arrive ⟨h - 1, by omega⟩) (c : Fin h) : t < D.arrive c :=
  ht.trans_le (D.arrive_strictAnti.antitone (Fin.le_iff_val_le_val.mpr
    (show c.val ≤ h - 1 by have := c.isLt; omega)))

/-- The outermost upper return of a zigzag lands at its trough. -/
theorem P_arrive_zero {h : ℕ} (Z : Zigzag.Shape h) (hh : 0 < h) :
    Z.P.arrive ⟨0, hh⟩ = Z.trough := by
  have := Z.p_arrive ⟨0, hh⟩
  simp only at this
  unfold Zigzag.Shape.trough
  omega

/-- The outermost lower return of a zigzag departs from its peak. -/
theorem Q_depart_zero {h : ℕ} (Z : Zigzag.Shape h) (hh : 0 < h) :
    Z.Q.depart ⟨0, hh⟩ = Z.P.peak := by
  have := Z.q_depart ⟨0, hh⟩
  simp only at this
  omega

/-! ### Families of scheduled returns -/

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

/-- The hops of the actual family `q` are exactly the returns of the schedule `D`, as hops of the
head `head`, and `q` is owned by the peak of `D`. -/
structure IsSchedFamily (q : ActualFamily xs T) (head : Fin k) {h : ℕ} (D : Schedule h) :
    Prop where
  hops_eq : q.hops = univ.image (fun c : Fin h => (head, D.depart c, D.arrive c))
  owner_eq : q.owner = D.peak

namespace IsSchedFamily

variable {q : ActualFamily xs T} {head : Fin k} {h : ℕ} {D : Schedule h}

theorem mem_hops (hq : IsSchedFamily q head D) (c : Fin h) :
    (head, D.depart c, D.arrive c) ∈ q.hops := by
  rw [hq.hops_eq]
  exact mem_image.mpr ⟨c, mem_univ _, rfl⟩

theorem card (hq : IsSchedFamily q head D) : q.hops.card = h := by
  rw [hq.hops_eq, card_image_of_injective]
  · simp
  · intro i j hij
    exact D.depart_strictMono.injective (congrArg (fun η : Fin k × ℕ × ℕ => η.2.1) hij)

/-- The span starts at the outermost departure. -/
theorem start_eq (hq : IsSchedFamily q head D) (hh : 0 < h) : q.start = D.depart ⟨0, hh⟩ := by
  change q.hops.inf' q.nonempty (fun η : Fin k × ℕ × ℕ => η.2.1) = _
  apply le_antisymm
  · exact inf'_le _ (hq.mem_hops ⟨0, hh⟩)
  · apply le_inf'
    intro η hη
    rw [hq.hops_eq] at hη
    obtain ⟨c, _, rfl⟩ := mem_image.mp hη
    exact D.depart_strictMono.monotone (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))

/-- The span stops at the outermost arrival. -/
theorem stop_eq (hq : IsSchedFamily q head D) (hh : 0 < h) : q.stop = D.arrive ⟨0, hh⟩ := by
  change q.hops.sup (fun η : Fin k × ℕ × ℕ => η.2.2) = _
  apply le_antisymm
  · apply Finset.sup_le
    intro η hη
    rw [hq.hops_eq] at hη
    obtain ⟨c, _, rfl⟩ := mem_image.mp hη
    exact D.arrive_strictAnti.antitone (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
  · exact Finset.le_sup (f := fun η : Fin k × ℕ × ℕ => η.2.2) (hq.mem_hops ⟨0, hh⟩)

/-- From the return `c` until the next outer return, the family holds the departure of `c`. -/
theorem held_eq (hq : IsSchedFamily q head D) (c : Fin h) {t : ℕ} (h1 : D.arrive c ≤ t)
    (h2 : ∀ c' : Fin h, c' < c → t < D.arrive c') : q.held t = D.depart c := by
  apply le_antisymm
  · calc q.held t
        ≤ (fun η : Fin k × ℕ × ℕ => if η.2.2 ≤ t then η.2.1 else q.owner)
            (head, D.depart c, D.arrive c) := inf'_le _ (hq.mem_hops c)
      _ = D.depart c := ite_eq_left h1
  · apply le_inf'
    intro η hη
    rw [hq.hops_eq] at hη
    obtain ⟨c', _, rfl⟩ := mem_image.mp hη
    by_cases he : D.arrive c' ≤ t
    · simp only [ite_eq_left he]
      exact D.depart_strictMono.monotone
        (le_of_not_gt fun hlt => absurd he (not_le.mpr (h2 c' hlt)))
    · simp only [ite_eq_right he, hq.owner_eq]
      exact (D.depart_lt_peak c).le

theorem held_arrive (hq : IsSchedFamily q head D) (c : Fin h) :
    q.held (D.arrive c) = D.depart c :=
  hq.held_eq c le_rfl fun _ hlt => D.arrive_strictAnti hlt

/-- Between the return `c` and the next outer return `c - 1` the held value is constant. -/
theorem held_between (hq : IsSchedFamily q head D) (c : Fin h) {t : ℕ} (h1 : D.arrive c ≤ t)
    (h2 : t < D.arrive ⟨c.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) c.isLt⟩) :
    q.held t = D.depart c :=
  hq.held_eq c h1 (lt_arrive_of_lt_pred D c h2)

/-- Before the innermost return, the family holds its owner. -/
theorem held_before (hq : IsSchedFamily q head D) {t : ℕ} (ht : ∀ c : Fin h, t < D.arrive c) :
    q.held t = D.peak := by
  have h0 : ∀ η ∈ q.hops, t < η.2.2 := by
    intro η hη
    rw [hq.hops_eq] at hη
    obtain ⟨c, _, rfl⟩ := mem_image.mp hη
    exact ht c
  rw [q.held_initial t h0, hq.owner_eq]

/-- The shadow acts exactly on `(peak, outermost arrival]`. -/
theorem shadow_ne_self_iff (hq : IsSchedFamily q head D) (hh : 0 < h) (t : ℕ) :
    q.shadow t ≠ t ↔ D.peak < t ∧ t ≤ D.arrive ⟨0, hh⟩ := by
  rw [q.shadow_ne_self_iff t, hq.owner_eq, hq.stop_eq hh]

/-- On its active interval the shadow is the held value, clipped above the outermost departure. -/
theorem shadow_eq (hq : IsSchedFamily q head D) (hh : 0 < h) {t : ℕ} (h1 : D.peak < t)
    (h2 : t ≤ D.arrive ⟨0, hh⟩) : q.shadow t = max (D.depart ⟨0, hh⟩ + 1) (q.held t) := by
  have hdom : t ∈ q.shadowAction.domain := by
    change q.owner < t ∧ t ≤ q.stop
    rw [hq.owner_eq, hq.stop_eq hh]
    exact ⟨h1, h2⟩
  rw [ActualFamily.shadow, q.shadowAction.apply_eq hdom]
  change max (q.start + 1) (q.held t) = _
  rw [hq.start_eq hh]

/-- The shadow at a return time. -/
theorem shadow_arrive (hq : IsSchedFamily q head D) (hh : 0 < h) (c : Fin h) :
    q.shadow (D.arrive c) = max (D.depart ⟨0, hh⟩ + 1) (D.depart c) := by
  rw [hq.shadow_eq hh (D.peak_lt_arrive c)
    (D.arrive_strictAnti.antitone (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))), hq.held_arrive c]

/-- At the outermost (paid) return the shadow is clipped just above its departure. -/
theorem shadow_outer (hq : IsSchedFamily q head D) (hh : 0 < h) :
    q.shadow (D.arrive ⟨0, hh⟩) = D.depart ⟨0, hh⟩ + 1 := by
  rw [hq.shadow_arrive hh, max_eq_left (Nat.le_succ _)]

/-- Every unpaid (inner) return is represented exactly by the shadow. -/
theorem shadow_exact (hq : IsSchedFamily q head D) (hh : 0 < h) {c : Fin h} (hc : 0 < c.val) :
    q.shadow (D.arrive c) = D.depart c := by
  rw [hq.shadow_arrive hh c, max_eq_right]
  exact D.depart_strictMono (show (⟨0, hh⟩ : Fin h) < c from Fin.lt_def.mpr hc)

/-- From an inner return `c` until the next outer return, the shadow is the departure of `c`. -/
theorem shadow_of_between (hq : IsSchedFamily q head D) (hh : 0 < h) (c : Fin h)
    (hc : 0 < c.val) {t : ℕ} (h1 : D.arrive c ≤ t)
    (h2 : ∀ c' : Fin h, c' < c → t < D.arrive c') : q.shadow t = D.depart c := by
  have h0 : (⟨0, hh⟩ : Fin h) < c := Fin.lt_def.mpr hc
  rw [hq.shadow_eq hh ((D.peak_lt_arrive c).trans_le h1) (h2 ⟨0, hh⟩ h0).le,
    hq.held_eq c h1 h2, max_eq_right]
  exact D.depart_strictMono h0

/-- Between consecutive returns `c` and `c - 1` (`c ≥ 1`) the shadow is the departure of `c`. -/
theorem shadow_between (hq : IsSchedFamily q head D) (hh : 0 < h) (c : Fin h) (hc : 0 < c.val)
    {t : ℕ} (h1 : D.arrive c ≤ t)
    (h2 : t < D.arrive ⟨c.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) c.isLt⟩) :
    q.shadow t = D.depart c :=
  hq.shadow_of_between hh c hc h1 (lt_arrive_of_lt_pred D c h2)

/-- After the peak and before the innermost return, the shadow is the owner. -/
theorem shadow_before (hq : IsSchedFamily q head D) (hh : 0 < h) {t : ℕ} (h1 : D.peak < t)
    (h2 : ∀ c : Fin h, t < D.arrive c) : q.shadow t = D.peak := by
  rw [hq.shadow_eq hh h1 (h2 ⟨0, hh⟩).le, hq.held_before h2, max_eq_right]
  exact D.depart_lt_peak ⟨0, hh⟩

end IsSchedFamily

/-! ### Staircases of zigzags -/

/-- The hypotheses on a head `head` that performs the staircase of the zigzag segments `S j`,
`j < n`, spliced at the times `start j`: each segment is finished by the next splice time and
before the horizon `T`. -/
structure Stair (xs : Fin k → ℕ → ℤ) (T : ℕ) (head : Fin k) (S : ℕ → Zigzag.Seg)
    (start : ℕ → ℕ) (n : ℕ) : Prop where
  valid : Staircase.Valid (fun j => (S j).walk) (fun j => (S j).h) start
  walk_eq : xs head = Staircase.walk (fun j => (S j).walk) (fun j => (S j).h) start n
  finish_le : ∀ j, j + 1 < n → (S j).finish ≤ start (j + 1)
  finish_lt : ∀ j < n, (S j).finish < T

namespace Stair

variable {head : Fin k} {S : ℕ → Zigzag.Seg} {start : ℕ → ℕ} {n : ℕ}
  (H : Stair xs T head S start n)
include H

/-! #### Times and levels -/

/-- A segment is at its base at its splice time, so it departs no earlier. -/
theorem start_le_depart (j : ℕ) (c : Fin (S j).h) : start j ≤ (S j).Z.P.depart c := by
  have hpos := (S j).pos
  have h0 : (S j).Z.P.depart ⟨0, hpos⟩ ≤ (S j).Z.P.depart c :=
    (S j).Z.P.depart_strictMono.monotone (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
  by_contra hlt
  have hpk := (S j).Z.P.depart_lt_peak ⟨0, hpos⟩
  have hsep := (S j).Z.P.separated ⟨0, hpos⟩ ⟨0, hpos⟩
  have hb : (S j).Z.walk ((S j).Z.P.depart ⟨0, hpos⟩ + 1) = 0 :=
    H.valid.before j _ (by omega)
  rw [(S j).Z.walk_of_le (t := (S j).Z.P.depart ⟨0, hpos⟩ + 1)
    (by unfold Zigzag.Shape.trough; omega)] at hb
  have hact : 0 < (S j).Z.P.height ((S j).Z.P.depart ⟨0, hpos⟩ + 1) :=
    ((S j).Z.P.lt_height_iff ⟨0, hpos⟩ _).mpr ⟨by omega, by omega⟩
  omega

theorem start_le_Q_depart (j : ℕ) (i : Fin (S j).h) : start j ≤ (S j).Z.Q.depart i := by
  have h1 := H.start_le_depart j ⟨0, (S j).pos⟩
  have h2 := (S j).Z.P.depart_lt_peak ⟨0, (S j).pos⟩
  rw [(S j).Z.q_depart i]
  omega

/-- A segment finishes before every later splice time. -/
theorem finish_le_start {j j' : ℕ} (hjj : j < j') (hj' : j' < n) : (S j).finish ≤ start j' :=
  (H.finish_le j (by omega)).trans (H.valid.start_mono.monotone (show j + 1 ≤ j' by omega))

/-- From its splice time to its finish, the head is segment `j` raised by the heights of the
earlier segments. -/
theorem walk_on_seg {j : ℕ} (hj : j < n) {t : ℕ} (h1 : start j ≤ t) (h2 : t ≤ (S j).finish) :
    xs head t = (∑ l ∈ range j, ((S l).h : ℤ)) + (S j).Z.walk t := by
  rw [H.walk_eq]
  exact Staircase.walk_on H.valid hj h1 fun hjn => h2.trans (H.finish_le j hjn)

theorem peak_lt_peak {j j' : ℕ} (hjj : j < j') (hj' : j' < n) :
    (S j).Z.P.peak < (S j').Z.P.peak := by
  have h1 := H.finish_le_start hjj hj'
  have h2 := H.start_le_depart j' ⟨0, (S j').pos⟩
  have h3 := (S j').Z.P.depart_lt_peak ⟨0, (S j').pos⟩
  have h4 : (S j).Z.P.peak < (S j).finish :=
    ((S j).Z.P.peak_lt_arrive ⟨0, (S j).pos⟩).trans_le
      ((S j).Z.P_arrive_le_finish (S j).pos ⟨0, (S j).pos⟩)
  omega

theorem trough_lt_trough {j j' : ℕ} (hjj : j < j') (hj' : j' < n) :
    (S j).Z.trough < (S j').Z.trough := by
  have h1 := H.finish_le_start hjj hj'
  have h2 := H.start_le_depart j' ⟨0, (S j').pos⟩
  have h3 := (S j').Z.P.depart_lt_peak ⟨0, (S j').pos⟩
  have h4 : (S j).Z.trough < (S j).finish := (S j).Z.Q_arrive_gt (S j).pos ⟨0, (S j).pos⟩
  have h5 : (S j').Z.P.peak ≤ (S j').Z.trough := by unfold Zigzag.Shape.trough; omega
  omega

/-- Distinct segments have distinct peaks. -/
theorem peak_inj {j j' : ℕ} (hj : j < n) (hj' : j' < n)
    (he : (S j).Z.P.peak = (S j').Z.P.peak) : j = j' := by
  rcases lt_trichotomy j j' with h | h | h
  · exact absurd he (H.peak_lt_peak h hj').ne
  · exact h
  · exact absurd he.symm (H.peak_lt_peak h hj).ne

/-- Distinct segments have distinct troughs. -/
theorem trough_inj {j j' : ℕ} (hj : j < n) (hj' : j' < n)
    (he : (S j).Z.trough = (S j').Z.trough) : j = j' := by
  rcases lt_trichotomy j j' with h | h | h
  · exact absurd he (H.trough_lt_trough h hj').ne
  · exact h
  · exact absurd he.symm (H.trough_lt_trough h hj).ne

/-! #### Returns and keys -/

/-- **The returns of the head** are the upper and the lower returns of its segments. -/
theorem hop_iff (p u : ℕ) :
    IsHop (xs head) T p u ↔ ∃ j < n,
      (∃ c : Fin (S j).h, p = (S j).Z.P.depart c ∧ u = (S j).Z.P.arrive c) ∨
        (∃ i : Fin (S j).h, p = (S j).Z.Q.depart i ∧ u = (S j).Z.Q.arrive i) := by
  rw [H.walk_eq, Staircase.walk_hop_iff H.valid]
  constructor
  · rintro ⟨j, hj, -, -, hhop⟩
    exact ⟨j, hj, (((S j).Z.hop_iff (S j).pos T p u).mp hhop).2⟩
  · rintro ⟨j, hj, hret⟩
    have hu : u ≤ (S j).finish := by
      rcases hret with ⟨c, -, rfl⟩ | ⟨i, -, rfl⟩
      · exact (S j).Z.P_arrive_le_finish (S j).pos c
      · exact (S j).Z.arrive_le_finish (S j).pos i
    have hp : start j ≤ p := by
      rcases hret with ⟨c, rfl, -⟩ | ⟨i, rfl, -⟩
      · exact H.start_le_depart j c
      · exact H.start_le_Q_depart j i
    exact ⟨j, hj, hp, fun hjn => hu.trans (H.finish_le j hjn),
      ((S j).Z.hop_iff (S j).pos T p u).mpr ⟨hu.trans_lt (H.finish_lt j hj), hret⟩⟩

/-- Every actual hop of the head is a return of one of its segments. -/
theorem hop_cases {η : Fin k × ℕ × ℕ} (hη : η ∈ allHops xs T) (hhead : η.1 = head) :
    ∃ j < n,
      (∃ c : Fin (S j).h, η = (head, (S j).Z.P.depart c, (S j).Z.P.arrive c)) ∨
        (∃ i : Fin (S j).h, η = (head, (S j).Z.Q.depart i, (S j).Z.Q.arrive i)) := by
  have hh := mem_allHops.mp hη
  rw [hhead, H.hop_iff] at hh
  obtain ⟨j, hj, ⟨c, hp, hu⟩ | ⟨i, hp, hu⟩⟩ := hh
  · exact ⟨j, hj, Or.inl ⟨c, Prod.ext hhead (Prod.ext hp hu)⟩⟩
  · exact ⟨j, hj, Or.inr ⟨i, Prod.ext hhead (Prod.ext hp hu)⟩⟩

/-- The upper returns of segment `j` are upper hops owned by its peak. -/
theorem key_P {j : ℕ} (hj : j < n) (c : Fin (S j).h) :
    key xs (actualOwner xs) (head, (S j).Z.P.depart c, (S j).Z.P.arrive c) =
      (head, true, (S j).Z.P.peak) :=
  (S j).Z.key_upper (S j).pos (∑ l ∈ range j, ((S l).h : ℤ)) c fun _ h1 h2 =>
    H.walk_on_seg hj ((H.start_le_depart j c).trans h1)
      (h2.trans ((S j).Z.P_arrive_le_finish (S j).pos c))

/-- The lower returns of segment `j` are lower hops owned by its trough. -/
theorem key_Q {j : ℕ} (hj : j < n) (i : Fin (S j).h) :
    key xs (actualOwner xs) (head, (S j).Z.Q.depart i, (S j).Z.Q.arrive i) =
      (head, false, (S j).Z.trough) :=
  (S j).Z.key_lower (S j).pos (∑ l ∈ range j, ((S l).h : ℤ)) i fun _ h1 h2 =>
    H.walk_on_seg hj ((H.start_le_Q_depart j i).trans h1)
      (h2.trans ((S j).Z.arrive_le_finish (S j).pos i))

/-! #### The two families of a segment -/

/-- The **upper family** of segment `j`: the returns of `P`, owned by the peak. -/
def upper (j : ℕ) (hj : j < n) : ActualFamily xs T :=
  ⟨(head, true, (S j).Z.P.peak), mem_image.mpr
    ⟨(head, (S j).Z.P.depart ⟨0, (S j).pos⟩, (S j).Z.P.arrive ⟨0, (S j).pos⟩),
      mem_allHops.mpr ((H.hop_iff _ _).mpr ⟨j, hj, Or.inl ⟨⟨0, (S j).pos⟩, rfl, rfl⟩⟩),
      H.key_P hj _⟩⟩

/-- The **lower family** of segment `j`: the returns of `Q`, owned by the trough. -/
def lower (j : ℕ) (hj : j < n) : ActualFamily xs T :=
  ⟨(head, false, (S j).Z.trough), mem_image.mpr
    ⟨(head, (S j).Z.Q.depart ⟨0, (S j).pos⟩, (S j).Z.Q.arrive ⟨0, (S j).pos⟩),
      mem_allHops.mpr ((H.hop_iff _ _).mpr ⟨j, hj, Or.inr ⟨⟨0, (S j).pos⟩, rfl, rfl⟩⟩),
      H.key_Q hj _⟩⟩

theorem upper_val (j : ℕ) (hj : j < n) : (H.upper j hj).1 = (head, true, (S j).Z.P.peak) := rfl

theorem lower_val (j : ℕ) (hj : j < n) : (H.lower j hj).1 = (head, false, (S j).Z.trough) := rfl

/-- The hops of the upper family are exactly the returns of `P`. -/
theorem upper_hops (j : ℕ) (hj : j < n) :
    (H.upper j hj).hops =
      univ.image (fun c : Fin (S j).h => (head, (S j).Z.P.depart c, (S j).Z.P.arrive c)) := by
  ext η
  constructor
  · intro hη
    obtain ⟨hHop, hkey⟩ := mem_filter.mp hη
    obtain ⟨m, hm, ⟨c, rfl⟩ | ⟨i, rfl⟩⟩ := H.hop_cases hHop (congrArg Prod.fst hkey)
    · have he : (head, true, (S m).Z.P.peak) = (head, true, (S j).Z.P.peak) :=
        (H.key_P hm c).symm.trans hkey
      obtain rfl := H.peak_inj hm hj (congrArg (fun q : Fin k × Bool × ℕ => q.2.2) he)
      exact mem_image.mpr ⟨c, mem_univ _, rfl⟩
    · have he : (head, false, (S m).Z.trough) = (head, true, (S j).Z.P.peak) :=
        (H.key_Q hm i).symm.trans hkey
      have hs : false = true := congrArg (fun q : Fin k × Bool × ℕ => q.2.1) he
      exact absurd hs Bool.false_ne_true
  · intro hη
    obtain ⟨c, _, rfl⟩ := mem_image.mp hη
    exact mem_filter.mpr
      ⟨mem_allHops.mpr ((H.hop_iff _ _).mpr ⟨j, hj, Or.inl ⟨c, rfl, rfl⟩⟩), H.key_P hj c⟩

/-- The hops of the lower family are exactly the returns of `Q`. -/
theorem lower_hops (j : ℕ) (hj : j < n) :
    (H.lower j hj).hops =
      univ.image (fun i : Fin (S j).h => (head, (S j).Z.Q.depart i, (S j).Z.Q.arrive i)) := by
  ext η
  constructor
  · intro hη
    obtain ⟨hHop, hkey⟩ := mem_filter.mp hη
    obtain ⟨m, hm, ⟨c, rfl⟩ | ⟨i, rfl⟩⟩ := H.hop_cases hHop (congrArg Prod.fst hkey)
    · have he : (head, true, (S m).Z.P.peak) = (head, false, (S j).Z.trough) :=
        (H.key_P hm c).symm.trans hkey
      have hs : true = false := congrArg (fun q : Fin k × Bool × ℕ => q.2.1) he
      exact absurd hs.symm Bool.false_ne_true
    · have he : (head, false, (S m).Z.trough) = (head, false, (S j).Z.trough) :=
        (H.key_Q hm i).symm.trans hkey
      obtain rfl := H.trough_inj hm hj (congrArg (fun q : Fin k × Bool × ℕ => q.2.2) he)
      exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  · intro hη
    obtain ⟨i, _, rfl⟩ := mem_image.mp hη
    exact mem_filter.mpr
      ⟨mem_allHops.mpr ((H.hop_iff _ _).mpr ⟨j, hj, Or.inr ⟨i, rfl, rfl⟩⟩), H.key_Q hj i⟩

theorem upper_sched (j : ℕ) (hj : j < n) : IsSchedFamily (H.upper j hj) head (S j).Z.P :=
  ⟨H.upper_hops j hj, rfl⟩

theorem lower_sched (j : ℕ) (hj : j < n) : IsSchedFamily (H.lower j hj) head (S j).Z.Q :=
  ⟨H.lower_hops j hj, ((S j).Z.Q_peak (S j).pos).symm⟩

/-! #### Spans -/

theorem upper_start (j : ℕ) (hj : j < n) :
    (H.upper j hj).start = (S j).Z.P.depart ⟨0, (S j).pos⟩ :=
  (H.upper_sched j hj).start_eq (S j).pos

theorem upper_stop (j : ℕ) (hj : j < n) :
    (H.upper j hj).stop = (S j).Z.P.arrive ⟨0, (S j).pos⟩ :=
  (H.upper_sched j hj).stop_eq (S j).pos

/-- The upper family stops at the trough. -/
theorem upper_stop_eq_trough (j : ℕ) (hj : j < n) : (H.upper j hj).stop = (S j).Z.trough :=
  (H.upper_stop j hj).trans (P_arrive_zero (S j).Z (S j).pos)

theorem lower_start (j : ℕ) (hj : j < n) :
    (H.lower j hj).start = (S j).Z.Q.depart ⟨0, (S j).pos⟩ :=
  (H.lower_sched j hj).start_eq (S j).pos

/-- The lower family starts at the peak. -/
theorem lower_start_eq_peak (j : ℕ) (hj : j < n) : (H.lower j hj).start = (S j).Z.P.peak :=
  (H.lower_start j hj).trans (Q_depart_zero (S j).Z (S j).pos)

theorem lower_stop (j : ℕ) (hj : j < n) :
    (H.lower j hj).stop = (S j).Z.Q.arrive ⟨0, (S j).pos⟩ :=
  (H.lower_sched j hj).stop_eq (S j).pos

/-- The lower family stops at the finish of the segment. -/
theorem lower_stop_eq_finish (j : ℕ) (hj : j < n) : (H.lower j hj).stop = (S j).finish :=
  H.lower_stop j hj

/-! #### Completeness and distinctness -/

/-- **Completeness.** Every actual family of the head is the upper or the lower family of one of
its segments. -/
theorem family_cases (q : ActualFamily xs T) (hq : q.1.1 = head) :
    ∃ j, ∃ hj : j < n, q = H.upper j hj ∨ q = H.lower j hj := by
  obtain ⟨η, hη⟩ := q.nonempty
  obtain ⟨hHop, hkey⟩ := mem_filter.mp hη
  obtain ⟨j, hj, ⟨c, rfl⟩ | ⟨i, rfl⟩⟩ := H.hop_cases hHop ((congrArg Prod.fst hkey).trans hq)
  · exact ⟨j, hj, Or.inl (Subtype.ext (hkey.symm.trans (H.key_P hj c)))⟩
  · exact ⟨j, hj, Or.inr (Subtype.ext (hkey.symm.trans (H.key_Q hj i)))⟩

theorem upper_ne_lower (j : ℕ) (hj : j < n) (j' : ℕ) (hj' : j' < n) :
    H.upper j hj ≠ H.lower j' hj' := by
  intro he
  have hs : true = false := congrArg (fun q : ActualFamily xs T => q.1.2.1) he
  exact absurd hs.symm Bool.false_ne_true

theorem upper_inj {j j' : ℕ} (hj : j < n) (hj' : j' < n) :
    H.upper j hj = H.upper j' hj' ↔ j = j' := by
  constructor
  · intro he
    exact H.peak_inj hj hj' (congrArg (fun q : ActualFamily xs T => q.1.2.2) he)
  · rintro rfl
    rfl

theorem lower_inj {j j' : ℕ} (hj : j < n) (hj' : j' < n) :
    H.lower j hj = H.lower j' hj' ↔ j = j' := by
  constructor
  · intro he
    exact H.trough_inj hj hj' (congrArg (fun q : ActualFamily xs T => q.1.2.2) he)
  · rintro rfl
    rfl

theorem upper_ne_upper {j j' : ℕ} (hj : j < n) (hj' : j' < n) (hne : j ≠ j') :
    H.upper j hj ≠ H.upper j' hj' :=
  fun he => hne ((H.upper_inj hj hj').mp he)

theorem lower_ne_lower {j j' : ℕ} (hj : j < n) (hj' : j' < n) (hne : j ≠ j') :
    H.lower j hj ≠ H.lower j' hj' :=
  fun he => hne ((H.lower_inj hj hj').mp he)

/-! #### Held values and shadows of the upper family -/

/-! #### Held values and shadows of the lower family -/

end Stair

end
end SourceCovers.StairFamilies
