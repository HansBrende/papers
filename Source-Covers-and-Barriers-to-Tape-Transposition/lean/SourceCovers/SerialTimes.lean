import SourceCovers.SerialUnpaid

set_option autoImplicit false

/-! The concrete path times and the payment checks needed for every
stage of the serial construction. These use the original paid phase. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting
noncomputable section

variable (P : Parameters)

instance lanes_neZero : NeZero (P.m - 1) := ⟨by have := P.hm; omega⟩

def laneHeight (k : Fin (P.m - 1)) : ℕ := P.m - 1 - k.val

theorem laneHeight_bounds (k : Fin (P.m - 1)) :
    0 < P.laneHeight k ∧ P.laneHeight k < P.m := by
  have hk := k.isLt
  have hm := P.hm
  dsimp only [laneHeight]
  omega

def lateWindow (k : Fin (P.m - 1)) : ℕ := 3 * P.m + P.laneHeight k

theorem lateWindow_eq (k : Fin (P.m - 1)) : P.lateWindow k = 4 * P.m - 1 - k.val := by
  have hk := k.isLt
  have hm := P.hm
  dsimp only [lateWindow, laneHeight]
  omega

theorem lateWindow_lt (k : Fin (P.m - 1)) : P.lateWindow k < P.bankCount := by
  have hh := P.laneHeight_bounds k
  dsimp only [lateWindow, bankCount]
  omega

theorem lateWindow_mod (k : Fin (P.m - 1)) : P.lateWindow k % P.m = P.laneHeight k := by
  simp [lateWindow, Nat.add_mod, Nat.mod_eq_of_lt (P.laneHeight_bounds k).2]

theorem width_half_pos : 0 < P.width / 2 := by
  have hh := P.width_ge
  have hm := P.hm
  omega

theorem width_half_lt : P.width / 2 < P.width := Nat.div_lt_self P.width_pos (by omega)

theorem width_half_twice : P.width / 2 + P.width / 2 = P.width := by
  have he : P.width % 2 = 0 := by simp [width, Nat.mul_mod]
  have hd := Nat.mod_add_div P.width 2
  omega

def lateTime (k : Fin (P.m - 1)) : ℕ :=
  11 * P.length + P.lateWindow k * P.width + P.width / 2

def root : ℕ := P.lateTime 0

def bridgeExit (k : Fin (P.m - 1)) : ℕ := 5 * P.length + P.laneHeight k

theorem lateTime_bounds (k : Fin (P.m - 1)) :
    11 * P.length < P.lateTime k ∧ P.lateTime k < 12 * P.length := by
  have hb := P.bank_window_bounds 1 ⟨P.lateWindow k, P.lateWindow_lt k⟩ P.width_half_lt
  have hh := P.width_half_pos
  change 11 * P.length ≤ P.lateTime k ∧ P.lateTime k < 11 * P.length + P.length at hb
  dsimp only [lateTime] at *
  omega

theorem root_is_output : ∃ i : Fin P.length, P.root = P.output i := by
  have hb := (P.lateTime_bounds 0).2
  let i : Fin P.length := ⟨P.lateWindow 0 * P.width + P.width / 2, by
    dsimp only [lateTime] at hb
    omega⟩
  refine ⟨i, ?_⟩
  dsimp only [root, lateTime, output, i]
  omega

theorem root_lt_horizon : P.root < P.horizon := by
  obtain ⟨i, hi⟩ := P.root_is_output
  rw [hi]
  exact P.output_lt i.isLt

theorem lateTime_unpaid (k : Fin (P.m - 1)) : P.lateTime k ∉ P.payment := by
  exact P.bank_window_unpaid 1 ⟨P.lateWindow k, P.lateWindow_lt k⟩ P.width_half_pos
    P.width_half_lt (Or.inr (by
      change P.lateWindow k % P.m ≠ 0
      rw [P.lateWindow_mod]
      exact (P.laneHeight_bounds k).1.ne'))

theorem bridgeReturn_bounds (k : Fin (P.m - 1)) :
    7 * P.length < P.bridgeReturn k ∧ P.bridgeReturn k < 8 * P.length := by
  rw [← P.bridgeArrival_delayed (show k.val < P.m by have := k.isLt; omega)]
  exact P.bridgeArrival_low (P.laneHeight_bounds k).2

theorem bridgeReturn_unpaid (k : Fin (P.m - 1)) : P.bridgeReturn k ∉ P.payment := by
  have hb := P.bridgeReturn_bounds k
  apply P.unpaid_outside_banks <;> omega

theorem bridgeExit_bounds (k : Fin (P.m - 1)) :
    5 * P.length < P.bridgeExit k ∧ P.bridgeExit k < 6 * P.length := by
  have hh := P.laneHeight_bounds k
  have hm := P.m_lt_length
  dsimp only [bridgeExit]
  omega

theorem bridgeExit_unpaid (k : Fin (P.m - 1)) : P.bridgeExit k ∉ P.payment := by
  have hb := P.bridgeExit_bounds k
  apply P.unpaid_outside_banks <;> omega

theorem olderWindow_mod (i : P.GridIndex) : P.olderWindow i % P.m = P.laneHeight i.2 := by
  have ha := P.olderWindow_add i
  have hb := i.2.isLt
  have he : P.olderWindow i = 7 * P.m + P.laneHeight i.2 := by
    dsimp only [bankCount] at ha
    dsimp only [laneHeight]
    omega
  rw [he]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (P.laneHeight_bounds i.2).2]

theorem olderTime_unpaid (i : P.GridIndex) : P.olderTime i ∉ P.payment := by
  have hwin : P.olderWindow i < P.bankCount := by have := P.olderWindow_add i; omega
  have hb := P.olderOffset_bounds i
  exact P.bank_window_unpaid 0 ⟨P.olderWindow i, hwin⟩ hb.1 hb.2
    (Or.inr (by
      change P.olderWindow i % P.m ≠ 0
      rw [P.olderWindow_mod]
      exact (P.laneHeight_bounds i.2).1.ne'))

theorem coverSeed_unpaid (i : Fin P.targets) : P.coverSeed i ∉ P.payment := by
  have hb := P.coverSeed_bounds i
  apply P.unpaid_outside_banks <;> omega

theorem coverTarget_unpaid (i : Fin P.targets) : P.coverTarget i ∉ P.payment := by
  have hb := P.coverTarget_bounds i
  apply P.unpaid_outside_banks <;> omega

end
end SourceCovers.SerialGeometry.Parameters
