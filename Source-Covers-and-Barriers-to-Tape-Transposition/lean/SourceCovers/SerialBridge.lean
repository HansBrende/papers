import SourceCovers.SerialParameters

set_option autoImplicit false

/-! The core bridge is one complete scheduled excursion. Its long pauses
change the last few return times, not the family or its canonical owner. -/

namespace SourceCovers.SerialGeometry.Parameters

open BoundedNesting LeanMachine.ScheduledExcursion

variable (P : Parameters)

/-- Return of the cell `a`, with the lowest `m` cells delayed. -/
def bridgeArrival (a : ℕ) : ℕ :=
  if a < P.m then
    8 * P.length - (3 * P.m + a) * P.width - P.width / 2
  else 7 * P.length - a

theorem bridgeArrival_low {a : ℕ} (ha : a < P.m) :
    7 * P.length < P.bridgeArrival a ∧ P.bridgeArrival a < 8 * P.length := by
  have hm := P.hm
  have hw := P.width_pos
  have hh := Nat.div_le_self P.width 2
  have hmul := Nat.mul_le_mul_right P.width (show 3 * P.m + a ≤ 4 * P.m by omega)
  have hcost : (3 * P.m + a) * P.width + P.width / 2 < P.length := by
    dsimp only [length, bankCount]
    nlinarith
  have hpos : 0 < (3 * P.m + a) * P.width := Nat.mul_pos (by omega) hw
  rw [bridgeArrival, ite_eq_left ha]
  omega

theorem bridgeArrival_bounds (a : Fin P.length) :
    6 * P.length < P.bridgeArrival a ∧ P.bridgeArrival a < 8 * P.length := by
  by_cases ha : a.val < P.m
  · have h := P.bridgeArrival_low ha
    omega
  · rw [bridgeArrival, ite_eq_right ha]
    have := a.isLt
    omega

theorem bridgeArrival_strictAnti :
    StrictAnti (fun a : Fin P.length => P.bridgeArrival a.val) := by
  intro a b hab
  have hab' : a.val < b.val := hab
  by_cases ha : a.val < P.m <;> by_cases hb : b.val < P.m
  · have hcost := Nat.mul_lt_mul_of_pos_right
      (show 3 * P.m + a.val < 3 * P.m + b.val by omega) P.width_pos
    have hbound := (P.bridgeArrival_low hb).1
    simp only [bridgeArrival, ite_eq_left ha, ite_eq_left hb] at hbound ⊢
    omega
  · have h := (P.bridgeArrival_low ha).1
    simp only [bridgeArrival, ite_eq_left ha, ite_eq_right hb] at h ⊢
    omega
  · omega
  · simp only [bridgeArrival, ite_eq_right ha, ite_eq_right hb]
    have := b.isLt
    omega

def bridge : Schedule P.length where
  depart a := 5 * P.length + a
  arrive a := P.bridgeArrival a
  depart_strictMono := by intro a b hab; dsimp; omega
  arrive_strictAnti := P.bridgeArrival_strictAnti
  separated := by
    intro a b
    have := a.isLt
    have := (P.bridgeArrival_bounds b).1
    omega

@[simp] theorem bridge_depart (a : Fin P.length) :
    P.bridge.depart a = 5 * P.length + a := rfl

@[simp] theorem bridge_arrive (a : Fin P.length) :
    P.bridge.arrive a = P.bridgeArrival a := rfl

@[simp] theorem bridge_peak : P.bridge.peak = 6 * P.length := by
  change (Schedule.plateau (5 * P.length) P.length 0).peak = _
  rw [Schedule.plateau_peak _ _ _ P.length_pos]
  omega

theorem bridge_before_horizon (a : Fin P.length) : P.bridge.arrive a < P.horizon := by
  have := (P.bridgeArrival_bounds a).2
  dsimp only [horizon]
  exact lt_of_lt_of_le this (by omega)

/-- Increasing delayed return times, in the indexing of the manuscript. -/
def bridgeReturn (k : ℕ) : ℕ :=
  8 * P.length - (4 * P.m - 1 - k) * P.width - P.width / 2

theorem bridgeArrival_delayed {k : ℕ} (hk : k < P.m) :
    P.bridgeArrival (P.m - 1 - k) = P.bridgeReturn k := by
  have hm := P.hm
  have he : 3 * P.m + (P.m - 1 - k) = 4 * P.m - 1 - k := by omega
  simp only [bridgeArrival, ite_eq_left (show P.m - 1 - k < P.m by omega), he, bridgeReturn]

theorem bridge_hops (p u : ℕ) :
    IsHop (NativeExcursion.walk P.bridge) P.horizon p u ↔
      ∃ a : Fin P.length, p = 5 * P.length + a ∧ u = P.bridgeArrival a := by
  rw [NativeExcursion.hop_iff]
  constructor
  · exact fun h => h.2
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨P.bridge_before_horizon a, a, rfl, rfl⟩

theorem bridge_legal :
    IsWalk (NativeExcursion.walk P.bridge) ∧ NativeExcursion.walk P.bridge 0 = 0 ∧
      ∀ c T, (entries (NativeExcursion.walk P.bridge) c T).card ≤ 2 :=
  ⟨NativeExcursion.isWalk _, NativeExcursion.walk_zero _,
    fun c T => NativeExcursion.entries_card_le_two _ c T⟩

end SourceCovers.SerialGeometry.Parameters
