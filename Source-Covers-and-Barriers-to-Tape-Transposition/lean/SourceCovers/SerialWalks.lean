import SourceCovers.NativeBank
import SourceCovers.SerialBridge
import SourceCovers.SerialGrid

set_option autoImplicit false

/-! The eight prescribed physical work-head walks. Their motion, initial
positions, entry bounds, and bank horizons are derived from the construction. -/

namespace SourceCovers.SerialGeometry.Parameters

open BoundedNesting
noncomputable section

variable (P : Parameters)

def bankStart (q : Fin 4) : ℕ :=
  (if q.val < 2 then 4 * P.length else 11 * P.length) + 2 * (q.val % 2) * P.width

abbrev bankHead (q : Fin 4) : ℕ → ℤ := NativeBank.walk P.width (P.bankStart q) (2 * P.m)

def excursionHead (q : Fin 4) : ℕ → ℤ :=
  if q.val = 0 then NativeExcursion.walk P.newer
  else if q.val = 1 then NativeExcursion.walk P.early
  else if q.val = 2 then NativeExcursion.walk P.older
  else NativeExcursion.walk P.bridge

def heads (q : Fin 8) : ℕ → ℤ :=
  Fin.addCases (m := 4) (n := 4) P.bankHead P.excursionHead q

theorem bankHead_isWalk (q : Fin 4) : IsWalk (P.bankHead q) := NativeBank.isWalk _ _ _

theorem excursionHead_isWalk (q : Fin 4) : IsWalk (P.excursionHead q) := by
  fin_cases q <;> change IsWalk (NativeExcursion.walk _) <;>
    exact NativeExcursion.isWalk _

theorem heads_isWalk (q : Fin 8) : IsWalk (P.heads q) := by
  refine Fin.addCases (m := 4) (n := 4) (fun q => ?_) (fun q => ?_) q
  · simpa only [heads, Fin.addCases_left] using P.bankHead_isWalk q
  · simpa only [heads, Fin.addCases_right] using P.excursionHead_isWalk q

@[simp] theorem heads_zero (q : Fin 8) : P.heads q 0 = 0 := by
  refine Fin.addCases (m := 4) (n := 4) (fun q => ?_) (fun q => ?_) q
  · simp only [heads, Fin.addCases_left, bankHead, NativeBank.zero]
  · fin_cases q <;> change NativeExcursion.walk _ 0 = 0 <;>
      exact NativeExcursion.walk_zero _

theorem heads_entries (q : Fin 8) (c : ℤ) (T : ℕ) : (entries (P.heads q) c T).card ≤ 3 := by
  refine Fin.addCases (m := 4) (n := 4) (fun q => ?_) (fun q => ?_) q
  · simpa only [heads, Fin.addCases_left, bankHead] using
      NativeBank.entries_card_le_three P.width_pos (P.bankStart q) (2 * P.m) c T
  · fin_cases q <;> change (entries (NativeExcursion.walk _) c T).card ≤ 3 <;>
      exact (NativeExcursion.entries_card_le_two _ c T).trans (by norm_num)

theorem bank_before_horizon (q : Fin 4) (r : Fin (2 * P.m)) :
    NativeBank.start P.width (P.bankStart q) r.val + 3 * P.width < P.horizon := by
  have hr := r.isLt
  have hq := Nat.mod_lt q.val (by norm_num : 0 < 2)
  have hm := Nat.mul_le_mul_right P.width
    (show 4 * r.val + 2 * (q.val % 2) + 3 ≤ 8 * P.m + 1 by omega)
  have hL : P.length = 8 * P.m * P.width := rfl
  dsimp only [NativeBank.start, bankStart, horizon]
  split <;> nlinarith

@[simp] theorem heads_bank (q : Fin 4) : P.heads (Fin.castAdd 4 q) = P.bankHead q :=
  Fin.addCases_left q

@[simp] theorem heads_newer : P.heads 4 = NativeExcursion.walk P.newer := rfl

@[simp] theorem heads_early : P.heads 5 = NativeExcursion.walk P.early := rfl

@[simp] theorem heads_older : P.heads 6 = NativeExcursion.walk P.older := rfl

@[simp] theorem heads_bridge : P.heads 7 = NativeExcursion.walk P.bridge := rfl

theorem newer_before_horizon (i : Fin P.length) : P.newer.arrive i < P.horizon := by
  rw [newer_arrive]
  unfold horizon
  omega

/-- The four non-bank families are the original canonical actual families
of the combined geometry; the other heads are not suppressed. -/
def newerFamily : ActualFamily P.heads P.horizon :=
  NativeExcursion.family (T := P.horizon) P.newer 4 P.heads_newer (P.newer_before_horizon 0)

def earlyFamily : ActualFamily P.heads P.horizon :=
  NativeExcursion.family (T := P.horizon) P.early 5 P.heads_early (by
    have := P.length_pos
    simp only [early_arrive, Fin.val_zero, Nat.sub_zero, horizon]
    omega)

def olderFamily : ActualFamily P.heads P.horizon :=
  NativeExcursion.family (T := P.horizon) P.older 6 P.heads_older (P.older_before_horizon 0)

def bridgeFamily : ActualFamily P.heads P.horizon :=
  NativeExcursion.family (T := P.horizon) P.bridge 7 P.heads_bridge (P.bridge_before_horizon 0)

@[simp] theorem newerFamily_head : P.newerFamily.val.1 = 4 := rfl
@[simp] theorem earlyFamily_head : P.earlyFamily.val.1 = 5 := rfl
@[simp] theorem olderFamily_head : P.olderFamily.val.1 = 6 := rfl
@[simp] theorem bridgeFamily_head : P.bridgeFamily.val.1 = 7 := rfl

@[simp] theorem newerFamily_start : P.newerFamily.start = 7 * P.length := by
  rw [newerFamily, NativeExcursion.family_start, newer_depart]
  rfl

@[simp] theorem newerFamily_stop : P.newerFamily.stop = 12 * P.length := by
  rw [newerFamily, NativeExcursion.family_stop, newer_arrive]
  rfl

@[simp] theorem earlyFamily_start : P.earlyFamily.start = 0 := by
  simp only [earlyFamily, NativeExcursion.family_start, early_depart, Fin.val_zero]

@[simp] theorem earlyFamily_stop : P.earlyFamily.stop = 3 * P.length := by
  simp only [earlyFamily, NativeExcursion.family_stop, early_arrive, Fin.val_zero, Nat.sub_zero]

@[simp] theorem olderFamily_start : P.olderFamily.start = 2 * P.length := by
  simp only [olderFamily, NativeExcursion.family_start, older, sparseDeparture_zero]

theorem olderFamily_stop_lt : P.olderFamily.stop < 5 * P.length := by
  rw [olderFamily, NativeExcursion.family_stop]
  exact (P.sparseArrival_bounds 0).2

@[simp] theorem bridgeFamily_start : P.bridgeFamily.start = 5 * P.length := by
  simp only [bridgeFamily, NativeExcursion.family_start, bridge_depart, Fin.val_zero, Nat.add_zero]

theorem bridgeFamily_stop_bounds :
    7 * P.length < P.bridgeFamily.stop ∧ P.bridgeFamily.stop < 8 * P.length := by
  rw [bridgeFamily, NativeExcursion.family_stop, bridge_arrive]
  exact P.bridgeArrival_low (by have := P.hm; change 0 < P.m; omega)

end
end SourceCovers.SerialGeometry.Parameters
