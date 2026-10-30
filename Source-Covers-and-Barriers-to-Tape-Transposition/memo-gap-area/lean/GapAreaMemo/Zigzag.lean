import SourceCovers.NativeExcursion
import SourceCovers.NativeWalkLocal

set_option autoImplicit false

/-!
# Zigzags with scheduled legs

A zigzag of height `h` rises from its base to its top, descends at unit
speed to the base, and rises again to the top. Its rise and its descent form
an excursion above the base, and its descent and second rise an excursion
below the top. Both excursions are scheduled excursions, so either rise may
pause arbitrarily. The returns of the zigzag are exactly the returns of the
two excursions: an upper family owned by the peak and a lower family owned
by the trough.
-/

namespace SourceCovers.Zigzag

open Finset BoundedNesting LeanMachine.ScheduledExcursion

variable {h : ℕ}

/-- Two excursions sharing the unit-speed descent from `P.peak` to `P.peak + h`.
`P` is measured upwards from the base, `Q` downwards from the top. -/
structure Shape (h : ℕ) where
  P : Schedule h
  Q : Schedule h
  p_arrive : ∀ c : Fin h, P.arrive c = P.peak + h - c
  q_depart : ∀ i : Fin h, Q.depart i = P.peak + i

namespace Shape

variable (Z : Shape h)

def trough : ℕ := Z.P.peak + h

def walk (t : ℕ) : ℤ := if t ≤ Z.trough then (Z.P.height t : ℤ) else (h : ℤ) - Z.Q.height t

theorem P_height_descent {t : ℕ} (ht : Z.P.peak ≤ t) (ht' : t ≤ Z.trough) :
    Z.P.height t = Z.P.peak + h - t := by
  have hact : Z.P.active t = univ.filter (fun c : Fin h => c.val < Z.P.peak + h - t) := by
    ext c
    simp only [Schedule.mem_active, mem_filter, mem_univ, true_and]
    have hd := Z.P.depart_lt_peak c
    rw [Z.p_arrive c]
    have := c.isLt
    constructor
    · rintro ⟨_, h2⟩; omega
    · intro h1; exact ⟨by omega, by omega⟩
  unfold Schedule.height
  rw [hact, Fin.card_filter_val_lt]
  unfold trough at ht'
  omega

theorem Q_arrive_gt (hh : 0 < h) (i : Fin h) : Z.trough < Z.Q.arrive i := by
  have := Z.Q.separated ⟨h - 1, by omega⟩ i
  rw [Z.q_depart] at this
  unfold trough
  simp only at this
  omega

theorem Q_height_descent (hh : 0 < h) {t : ℕ} (ht : Z.P.peak ≤ t) (ht' : t ≤ Z.trough) :
    Z.Q.height t = t - Z.P.peak := by
  have hact : Z.Q.active t = univ.filter (fun i : Fin h => i.val < t - Z.P.peak) := by
    ext i
    simp only [Schedule.mem_active, mem_filter, mem_univ, true_and]
    rw [Z.q_depart i]
    have := Z.Q_arrive_gt hh i
    constructor
    · rintro ⟨h1, _⟩; omega
    · intro h1; exact ⟨by omega, by omega⟩
  unfold Schedule.height
  rw [hact, Fin.card_filter_val_lt]
  unfold trough at ht'
  omega

/-- On the shared descent the two descriptions agree. -/
theorem descent_agree (hh : 0 < h) {t : ℕ} (ht : Z.P.peak ≤ t) (ht' : t ≤ Z.trough) :
    (Z.P.height t : ℤ) = (h : ℤ) - Z.Q.height t := by
  rw [Z.P_height_descent ht ht', Z.Q_height_descent hh ht ht']
  unfold trough at ht'
  omega

theorem walk_of_le {t : ℕ} (ht : t ≤ Z.trough) : Z.walk t = Z.P.height t := by
  simp only [walk, ht, ite_true]

theorem walk_of_peak_le (hh : 0 < h) {t : ℕ} (ht : Z.P.peak ≤ t) :
    Z.walk t = (h : ℤ) - Z.Q.height t := by
  unfold walk
  split_ifs with h1
  · exact Z.descent_agree hh ht h1
  · rfl

theorem isWalk (hh : 0 < h) : IsWalk Z.walk := by
  intro t
  by_cases h1 : t + 1 ≤ Z.trough
  · rw [Z.walk_of_le h1, Z.walk_of_le (by omega)]
    have := Z.P.height_step t
    rw [abs_le]; constructor <;> omega
  · have hpk : Z.P.peak ≤ t := by unfold trough at h1; omega
    rw [Z.walk_of_peak_le hh hpk, Z.walk_of_peak_le hh (by omega)]
    have := Z.Q.height_step t
    rw [abs_le]; constructor <;> omega

theorem walk_nonneg (t : ℕ) : 0 ≤ Z.walk t := by
  unfold walk
  split_ifs
  · positivity
  · have := Z.Q.height_le t; omega

theorem walk_le (t : ℕ) : Z.walk t ≤ h := by
  unfold walk
  split_ifs
  · have := Z.P.height_le t; omega
  · have := Z.Q.height_le t; omega

theorem hop_iff_of_neg_shift_on {x y : ℕ → ℤ} {T p u : ℕ} (c : ℤ)
    (he : ∀ t, p ≤ t → t ≤ u → x t = c - y t) :
    IsHop x T p u ↔ IsHop y T p u := by
  rw [NativeWalkLocal.hop_iff_of_shift_on c (y := fun t => -y t)
    (fun t h1 h2 => by rw [he t h1 h2]; ring)]
  unfold IsHop
  simp only [neg_inj, ne_eq]

theorem hopOwner_eq_of_neg_shift_on {x y : ℕ → ℤ} {p u : ℕ} (c : ℤ) (hl : p + 2 ≤ u)
    (he : ∀ t, p ≤ t → t ≤ u → x t = c - y t) :
    hopOwner x p u = hopOwner y p u := by
  rw [NativeWalkLocal.hopOwner_eq_of_shift_on c (y := fun t => -y t) hl
    (fun t h1 h2 => by rw [he t h1 h2]; ring)]
  obtain ⟨ha, hb, hm, hf⟩ := hopOwner_spec y hl
  apply NativeWalkLocal.hopOwner_eq_of_first_max hl ha hb
  · intro t h1 h2
    have := hm t h1 h2
    rw [show -y t - -y p = -(y t - y p) by ring, abs_neg,
      show -y (hopOwner y p u) - -y p = -(y (hopOwner y p u) - y p) by ring, abs_neg]
    exact this
  · intro t h1 h2
    have := hf t h1 h2
    rw [show -y t - -y p = -(y t - y p) by ring, abs_neg,
      show -y (hopOwner y p u) - -y p = -(y (hopOwner y p u) - y p) by ring, abs_neg]
    exact this

/-- **The returns of a zigzag.** -/
theorem hop_iff (hh : 0 < h) (T p u : ℕ) :
    IsHop Z.walk T p u ↔ u < T ∧
      ((∃ c : Fin h, p = Z.P.depart c ∧ u = Z.P.arrive c) ∨
        (∃ i : Fin h, p = Z.Q.depart i ∧ u = Z.Q.arrive i)) := by
  constructor
  · intro hhop
    have hT := hhop.2.1
    by_cases hu : u ≤ Z.trough
    · have hP : IsHop (NativeExcursion.walk Z.P) T p u :=
        (NativeWalkLocal.hop_iff_of_shift_on 0 (fun t _ ht => by
          rw [Z.walk_of_le (ht.trans hu), zero_add]; rfl)).mp hhop
      obtain ⟨_, c, hc⟩ := (NativeExcursion.hop_iff Z.P T p u).mp hP
      exact ⟨hT, Or.inl ⟨c, hc⟩⟩
    · by_cases hp : Z.P.peak ≤ p
      · have hQ : IsHop (NativeExcursion.walk Z.Q) T p u :=
          (hop_iff_of_neg_shift_on (h : ℤ) (fun t ht _ => by
            rw [Z.walk_of_peak_le hh (hp.trans ht)]; rfl)).mp hhop
        obtain ⟨_, i, hi⟩ := (NativeExcursion.hop_iff Z.Q T p u).mp hQ
        exact ⟨hT, Or.inr ⟨i, hi⟩⟩
      · exfalso
        push Not at hp
        have hpt : p ≤ Z.trough := by unfold trough; omega
        have hlt := Z.P.height_lt_peak hh hp
        set c := Z.P.height p with hc
        have hq := Z.P.height_arrive ⟨c, hlt⟩
        have harr := Z.p_arrive ⟨c, hlt⟩
        simp only at harr
        apply hhop.2.2.2 (Z.P.arrive ⟨c, hlt⟩)
        · refine mem_Ioo.mpr ⟨?_, ?_⟩
          · rw [harr]; omega
          · rw [harr]; unfold trough at hu; omega
        · rw [Z.walk_of_le (by rw [harr]; unfold trough; omega), hq, Z.walk_of_le hpt]
  · rintro ⟨hT, ⟨c, rfl, rfl⟩ | ⟨i, rfl, rfl⟩⟩
    · have hu : Z.P.arrive c ≤ Z.trough := by
        rw [Z.p_arrive c]; unfold trough; omega
      refine (NativeWalkLocal.hop_iff_of_shift_on 0 (fun t _ ht => by
          rw [Z.walk_of_le (ht.trans hu), zero_add])).mpr ?_
      exact (NativeExcursion.hop_iff Z.P T _ _).mpr ⟨hT, c, rfl, rfl⟩
    · have hp : Z.P.peak ≤ Z.Q.depart i := by rw [Z.q_depart i]; omega
      refine (hop_iff_of_neg_shift_on (h : ℤ) (fun t ht _ => by
          rw [Z.walk_of_peak_le hh (hp.trans ht)])).mpr ?_
      exact (NativeExcursion.hop_iff Z.Q T _ _).mpr ⟨hT, i, rfl, rfl⟩

theorem Q_peak (hh : 0 < h) : Z.Q.peak = Z.trough := by
  unfold Schedule.peak trough
  have hsup : univ.sup Z.Q.depart = Z.P.peak + (h - 1) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      rw [Z.q_depart i]
      have := i.isLt
      omega
    · have := Finset.le_sup (f := Z.Q.depart) (mem_univ (⟨h - 1, by omega⟩ : Fin h))
      rw [Z.q_depart] at this
      exact this
  rw [hsup]
  omega

/-- Keys of the upper returns, for a head that follows the zigzag up to a vertical shift. -/
theorem key_upper {k : ℕ} {xs : Fin k → ℕ → ℤ} {head : Fin k} (_hh : 0 < h) (base : ℤ)
    (c : Fin h) (hx : ∀ t, Z.P.depart c ≤ t → t ≤ Z.P.arrive c → xs head t = base + Z.walk t) :
    key xs (actualOwner xs) (head, Z.P.depart c, Z.P.arrive c) = (head, true, Z.P.peak) := by
  have hu : Z.P.arrive c ≤ Z.trough := by rw [Z.p_arrive c]; unfold trough; omega
  have hloc : ∀ t, Z.P.depart c ≤ t → t ≤ Z.P.arrive c →
      xs head t = base + NativeExcursion.walk Z.P t := by
    intro t h1 h2
    rw [hx t h1 h2, Z.walk_of_le (h2.trans hu)]; rfl
  have hup := NativeExcursion.upperHop Z.P c
  have hsep := Z.P.separated c c
  have hside : xs head (Z.P.depart c) < xs head (Z.P.depart c + 1) := by
    rw [hloc _ le_rfl (by omega), hloc _ (by omega) (by omega)]
    have := hup.above (Z.P.depart c + 1) (by omega) (by omega)
    linarith
  have hown : hopOwner (xs head) (Z.P.depart c) (Z.P.arrive c) = Z.P.peak := by
    rw [NativeWalkLocal.hopOwner_eq_of_shift_on base hup.long hloc]
    exact NativeExcursion.hopOwner_eq Z.P c
  simp only [key, side, actualOwner, hside, decide_true, hown]

/-- Keys of the lower returns: the lower side, owned by the trough. -/
theorem key_lower {k : ℕ} {xs : Fin k → ℕ → ℤ} {head : Fin k} (hh : 0 < h) (base : ℤ)
    (i : Fin h) (hx : ∀ t, Z.Q.depart i ≤ t → t ≤ Z.Q.arrive i → xs head t = base + Z.walk t) :
    key xs (actualOwner xs) (head, Z.Q.depart i, Z.Q.arrive i) = (head, false, Z.trough) := by
  have hp : Z.P.peak ≤ Z.Q.depart i := by rw [Z.q_depart i]; omega
  have hloc : ∀ t, Z.Q.depart i ≤ t → t ≤ Z.Q.arrive i →
      xs head t = (base + h) - NativeExcursion.walk Z.Q t := by
    intro t h1 h2
    rw [hx t h1 h2, Z.walk_of_peak_le hh (hp.trans h1)]; unfold NativeExcursion.walk; ring
  have hup := NativeExcursion.upperHop Z.Q i
  have hsep := Z.Q.separated i i
  have hside : ¬ xs head (Z.Q.depart i) < xs head (Z.Q.depart i + 1) := by
    rw [hloc _ le_rfl (by omega), hloc _ (by omega) (by omega)]
    have := hup.above (Z.Q.depart i + 1) (by omega) (by omega)
    linarith
  have hown : hopOwner (xs head) (Z.Q.depart i) (Z.Q.arrive i) = Z.trough := by
    rw [hopOwner_eq_of_neg_shift_on (base + h) hup.long hloc]
    rw [NativeExcursion.hopOwner_eq Z.Q i, Z.Q_peak hh]
  simp only [key, side, actualOwner, hside, decide_false, hown]

end Shape
end SourceCovers.Zigzag

namespace SourceCovers.Zigzag.Shape

open Finset BoundedNesting LeanMachine.ScheduledExcursion

variable {h : ℕ} (Z : Shape h)

/-- Before its first departure a zigzag is at its base. -/
theorem walk_before (hh : 0 < h) {t : ℕ} (ht : t ≤ Z.P.depart ⟨0, hh⟩) : Z.walk t = 0 := by
  have hpk := Z.P.depart_lt_peak ⟨0, hh⟩
  rw [Z.walk_of_le (by unfold trough; omega)]
  have : Z.P.active t = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    have h1 := (Schedule.mem_active Z.P).mp hi
    have h2 := Z.P.depart_strictMono.monotone (show (⟨0, hh⟩ : Fin h) ≤ i from Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
    omega
  unfold Schedule.height
  rw [this, card_empty, Nat.cast_zero]

/-- After its last arrival a zigzag is at its top. -/
theorem walk_after (hh : 0 < h) {t : ℕ} (ht : Z.Q.arrive ⟨0, hh⟩ ≤ t) : Z.walk t = h := by
  have hgt := Z.Q_arrive_gt hh ⟨0, hh⟩
  rw [Z.walk_of_peak_le hh (by unfold trough at hgt; omega)]
  have : Z.Q.active t = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    have h1 := (Schedule.mem_active Z.Q).mp hi
    have h2 := Z.Q.arrive_strictAnti.antitone (show (⟨0, hh⟩ : Fin h) ≤ i from Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
    omega
  unfold Schedule.height
  rw [this, card_empty, Nat.cast_zero, sub_zero]

/-- The last arrival of the zigzag, at its top cell. -/
def finish (hh : 0 < h) : ℕ := Z.Q.arrive ⟨0, hh⟩

theorem arrive_le_finish (hh : 0 < h) (i : Fin h) : Z.Q.arrive i ≤ Z.finish hh :=
  Z.Q.arrive_strictAnti.antitone (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))

theorem P_arrive_le_finish (hh : 0 < h) (c : Fin h) : Z.P.arrive c ≤ Z.finish hh := by
  have h1 := Z.Q_arrive_gt hh ⟨0, hh⟩
  rw [Z.p_arrive c]
  unfold finish
  unfold trough at h1
  omega

end SourceCovers.Zigzag.Shape
