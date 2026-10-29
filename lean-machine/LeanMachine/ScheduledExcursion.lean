import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-! A finite excursion specified by last outward visits and first inward
returns. Counting nested active levels constructs a unit-step walk, including
arbitrary pauses. Its return pairs are proved exhaustive. -/

namespace LeanMachine.ScheduledExcursion

open Finset

/-- The endpoints of the excursion above each cell. Ascending endpoints
increase, descending endpoints decrease, and every return follows the peak. -/
structure Schedule (h : ℕ) where
  depart : Fin h → ℕ
  arrive : Fin h → ℕ
  depart_strictMono : StrictMono depart
  arrive_strictAnti : StrictAnti arrive
  separated : ∀ i j, depart i + 1 < arrive j

namespace Schedule

variable {h : ℕ} (D : Schedule h)

/-- Levels strictly below the head at time `t`. -/
def active (t : ℕ) : Finset (Fin h) := univ.filter fun i => D.depart i < t ∧ t < D.arrive i

def height (t : ℕ) : ℕ := (D.active t).card

@[simp] theorem mem_active {i : Fin h} {t : ℕ} :
    i ∈ D.active t ↔ D.depart i < t ∧ t < D.arrive i := by simp [active]

theorem height_le (t : ℕ) : D.height t ≤ h := (card_filter_le ..).trans_eq (by simp)

@[simp] theorem height_zero : D.height 0 = 0 := by simp [height, active]

theorem active_downward {i j : Fin h} {t : ℕ} (hij : j ≤ i)
    (hi : i ∈ D.active t) : j ∈ D.active t := by
  rw [mem_active] at hi ⊢
  exact ⟨(D.depart_strictMono.monotone hij).trans_lt hi.1,
    hi.2.trans_le (D.arrive_strictAnti.antitone hij)⟩

/-- The cardinality of a downward-closed set of levels recovers its membership. -/
theorem lt_height_iff (i : Fin h) (t : ℕ) :
    i.val < D.height t ↔ D.depart i < t ∧ t < D.arrive i := by
  rw [← D.mem_active]
  constructor
  · intro hc
    by_contra hn
    have hs : D.active t ⊆ Iio i := by
      intro j hj
      exact mem_Iio.mpr (lt_of_not_ge fun hij => hn (D.active_downward hij hj))
    have hh := card_le_card hs
    simp only [Fin.card_Iio] at hh
    exact (not_le_of_gt hc) hh
  · intro hi
    have hs : Iic i ⊆ D.active t := fun j hj => D.active_downward (mem_Iic.mp hj) hi
    have hh := card_le_card hs
    simp only [Fin.card_Iic] at hh
    exact hh

theorem height_depart (i : Fin h) : D.height (D.depart i) = i.val := by
  apply Nat.le_antisymm
  · exact Nat.le_of_not_gt (by simp [D.lt_height_iff])
  · by_contra! hc
    let j : Fin h := ⟨D.height (D.depart i), hc.trans i.isLt⟩
    have hji : j < i := hc
    have hj : j.val < D.height (D.depart i) := (D.lt_height_iff j _).mpr
      ⟨D.depart_strictMono hji, by have := D.separated i j; omega⟩
    exact (lt_irrefl _ hj)

theorem height_arrive (i : Fin h) : D.height (D.arrive i) = i.val := by
  apply Nat.le_antisymm
  · exact Nat.le_of_not_gt (by simp [D.lt_height_iff])
  · by_contra! hc
    let j : Fin h := ⟨D.height (D.arrive i), hc.trans i.isLt⟩
    have hji : j < i := hc
    have hj : j.val < D.height (D.arrive i) := (D.lt_height_iff j _).mpr
      ⟨by have := D.separated j i; omega, D.arrive_strictAnti hji⟩
    exact (lt_irrefl _ hj)

/-- At most one new level and at most one departing level occur per tick. -/
theorem height_step (t : ℕ) :
    D.height (t + 1) ≤ D.height t + 1 ∧ D.height t ≤ D.height (t + 1) + 1 := by
  have hnew (i : Fin h) (hi : i ∈ D.active (t + 1) \ D.active t) : D.depart i = t := by
    simp only [mem_sdiff, mem_active] at hi
    omega
  have hold (i : Fin h) (hi : i ∈ D.active t \ D.active (t + 1)) : D.arrive i = t + 1 := by
    simp only [mem_sdiff, mem_active] at hi
    omega
  have hn : (D.active (t + 1) \ D.active t).card ≤ 1 := card_le_one.mpr
    fun i hi j hj => D.depart_strictMono.injective ((hnew i hi).trans (hnew j hj).symm)
  have ho : (D.active t \ D.active (t + 1)).card ≤ 1 := card_le_one.mpr
    fun i hi j hj => D.arrive_strictAnti.injective ((hold i hi).trans (hold j hj).symm)
  have h₁ := card_le_card_sdiff_add_card (s := D.active (t + 1)) (t := D.active t)
  have h₂ := card_le_card_sdiff_add_card (s := D.active t) (t := D.active (t + 1))
  unfold height
  omega

/-- Every superlevel set is an interval. -/
theorem min_height_le {p t u : ℕ} (hpt : p ≤ t) (htu : t ≤ u) :
    min (D.height p) (D.height u) ≤ D.height t := by
  by_contra! hn
  have hp : D.height t < D.height p := hn.trans_le (Nat.min_le_left ..)
  have hu : D.height t < D.height u := hn.trans_le (Nat.min_le_right ..)
  let i : Fin h := ⟨D.height t, hp.trans_le (D.height_le p)⟩
  obtain ⟨ha, _⟩ := (D.lt_height_iff i p).mp hp
  obtain ⟨_, hb⟩ := (D.lt_height_iff i u).mp hu
  have ht := (D.lt_height_iff i t).mpr ⟨ha.trans_le hpt, htu.trans_lt hb⟩
  exact lt_irrefl _ ht

/-- Exactly the supplied pairs are nonadjacent consecutive visits.
In particular, pauses cannot introduce an unlisted long return. -/
theorem return_iff (p u : ℕ) :
    (p + 2 ≤ u ∧ D.height u = D.height p ∧
      ∀ t, p < t → t < u → D.height t ≠ D.height p) ↔
    ∃ i : Fin h, p = D.depart i ∧ u = D.arrive i := by
  constructor
  · rintro ⟨hlen, heq, hne⟩
    have habove : ∀ t, p < t → t < u → D.height p < D.height t := by
      intro t hp hu
      have h := D.min_height_le hp.le hu.le
      rw [heq, min_self] at h
      exact lt_of_le_of_ne h (hne t hp hu).symm
    have hc := habove (p + 1) (by omega) (by omega)
    let i : Fin h := ⟨D.height p, hc.trans_le (D.height_le (p + 1))⟩
    have hpi := (D.lt_height_iff i p).not.mp (lt_irrefl _)
    have hui := (D.lt_height_iff i u).not.mp (by simp [i, heq])
    have hpa := (D.lt_height_iff i (p + 1)).mp hc
    have hua := (D.lt_height_iff i (u - 1)).mp (habove (u - 1) (by omega) (by omega))
    exact ⟨i, by omega, by omega⟩
  · rintro ⟨i, rfl, rfl⟩
    refine ⟨by have := D.separated i i; omega,
      (D.height_arrive i).trans (D.height_depart i).symm, ?_⟩
    intro t hp hu
    rw [D.height_depart]
    exact ((D.lt_height_iff i t).mpr ⟨hp, hu⟩).ne'

/-- The common first peak, including any pauses at maximum height. -/
def peak : ℕ := univ.sup D.depart + 1

theorem depart_lt_peak (i : Fin h) : D.depart i < D.peak :=
  (Finset.le_sup (f := D.depart) (mem_univ i)).trans_lt (Nat.lt_succ_self _)

theorem peak_lt_arrive (i : Fin h) : D.peak < D.arrive i := by
  obtain ⟨j, _, hj⟩ := exists_mem_eq_sup univ ⟨i, mem_univ i⟩ D.depart
  simpa only [peak, hj] using D.separated j i

theorem height_peak : D.height D.peak = h := by
  have hs : D.active D.peak = univ := by
    ext i
    simp only [mem_active, mem_univ, iff_true]
    exact ⟨D.depart_lt_peak i, D.peak_lt_arrive i⟩
  simp only [height, hs, card_univ, Fintype.card_fin]

theorem height_lt_peak (hh : 0 < h) {t : ℕ} (ht : t < D.peak) :
    D.height t < h := by
  obtain ⟨i, _, hi⟩ := exists_mem_eq_sup univ ⟨⟨0, hh⟩, mem_univ _⟩ D.depart
  have hn : ¬ i.val < D.height t := by
    rw [D.lt_height_iff]
    dsimp [peak] at ht
    rw [hi] at ht
    omega
  exact (Nat.le_of_not_gt hn).trans_lt i.isLt

theorem height_mono_before :
    MonotoneOn D.height (Set.Iic D.peak) := by
  intro p _ t ht hpt
  apply card_le_card
  intro i hi
  rw [mem_active] at hi ⊢
  exact ⟨hi.1.trans_le hpt, ht.trans_lt (D.peak_lt_arrive i)⟩

theorem height_anti_after :
    AntitoneOn D.height (Set.Ici D.peak) := by
  intro p hp t _ hpt
  apply card_le_card
  intro i hi
  rw [mem_active] at hi ⊢
  exact ⟨(D.depart_lt_peak i).trans_le hp, hpt.trans_lt hi.2⟩

/-- A unit ascent, a plateau, and a unit descent, with arbitrary initial wait. -/
def plateau (start h hold : ℕ) : Schedule h where
  depart i := start + i
  arrive i := start + 2 * h + hold - i
  depart_strictMono := by intro i j hij; dsimp; omega
  arrive_strictAnti := by intro i j hij; dsimp; have := j.isLt; omega
  separated := by intro i j; have := i.isLt; have := j.isLt; omega

@[simp] theorem plateau_peak (start h hold : ℕ) (hh : 0 < h) :
    (plateau start h hold).peak = start + h := by
  have hsup : univ.sup (plateau start h hold).depart < start + h :=
    (Finset.sup_lt_iff (by change 0 < start + h; omega)).mpr fun i _ => by
      dsimp [plateau]
      have := i.isLt
      omega
  have hlast := Finset.le_sup (f := (plateau start h hold).depart)
    (mem_univ (⟨h - 1, by omega⟩ : Fin h))
  dsimp only [plateau] at hlast hsup
  dsimp only [peak, plateau]
  omega

end Schedule
end LeanMachine.ScheduledExcursion
