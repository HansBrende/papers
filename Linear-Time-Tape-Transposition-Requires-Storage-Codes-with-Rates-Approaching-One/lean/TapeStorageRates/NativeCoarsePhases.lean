import TapeStorageRates.NativeSchedule

/-! Fixed nine-slot coarsening of one actual aligned simulator batch. -/

namespace TapeStorageRates.Native

open Transpose MergeDepth

/-- Offset of a physical head before step `i` in one complete batch. -/
def fineOffset (s : ℕ) (e : Fin 3) (i : ℕ) : ℤ :=
  if i < s then -(i : ℤ)
  else if i < 4*s then (i : ℤ)-2*s
  else if i < 4*s+1 then 2*(s : ℤ)-1
  else if i < 7*s+1 then 6*(s : ℤ)-i
  else if i < 8*s+1 then (i : ℤ)-8*s-1
  else if i < 9*s+1 then ((i : ℤ)-8*s-1)*moveInt (direction e)
  else (s : ℤ)*moveInt (direction e)

/-- The coarse slot of a fine step. Slot seven can be empty when `s=1`. -/
def fineSlot (s i : ℕ) : ℕ :=
  if i = 0 then 0
  else if i < 2*s then 1
  else if i < 3*s then 2
  else if i < 5*s+1 then 3
  else if i < 6*s+1 then 4
  else if i < 8*s+1 then 5
  else if i < 8*s+2 then 6
  else if i < 9*s+1 then 7 else 8

/-- A padded common coarse word, valid for arbitrarily many work heads. -/
def coarseOffset (e : Fin 3) (i : ℕ) : ℤ :=
  match i with
  | 1 | 5 => -1
  | 3 => 1
  | 7 => if e = 0 then -1 else 0
  | 8 => moveInt (direction e)
  | _ => 0

theorem fineSlot_lt (s i : ℕ) : fineSlot s i < 9 := by
  unfold fineSlot
  split_ifs <;> omega


theorem fineOffset_zero {s : ℕ} (hs : 0<s) (e : Fin 3) :
    fineOffset s e 0 = 0 := by simp [fineOffset,hs]

theorem fineOffset_end (s : ℕ) (e : Fin 3) :
    fineOffset s e (10*s+1) = (s : ℤ)*moveInt (direction e) := by
  simp [fineOffset,show ¬10*s+1<s by omega,show ¬10*s+1<4*s by omega,
    show ¬10*s+1<4*s+1 by omega,show ¬10*s+1<7*s+1 by omega,
    show ¬10*s+1<8*s+1 by omega,show ¬10*s+1<9*s+1 by omega]


/-- The padded coarse word is itself a simultaneous unit-step walk. -/
theorem coarseOffset_step (e : Fin 3) (i : ℕ) (hi : i<8) :
    |coarseOffset e (i+1)-coarseOffset e i| ≤ 1 := by
  interval_cases i <;> fin_cases e <;> norm_num [coarseOffset,direction,moveInt]

theorem fineOffset_window {s : ℕ} (hs : 0<s) (e : Fin 3) (i : ℕ)
    (hi : i<10*s+1) : -(s : ℤ) ≤ fineOffset s e i ∧ fineOffset s e i < 2*s := by
  generalize hf : fineOffset s e i = z
  unfold fineOffset at hf
  split_ifs at hf <;> fin_cases e <;>
    (try simp [direction,moveInt] at hf) <;> omega

/-- The read sweep witnesses every cell of all three aligned blocks. -/
theorem fineOffset_read {s : ℕ} (_hs : 0<s) (e : Fin 3) (i : ℕ)
    (hi : i<3*s) : fineOffset s e (s+i) = (i : ℤ)-s := by
  simp only [fineOffset,show ¬s+i<s by omega,ite_false,show s+i<4*s by omega,ite_true]
  omega

end TapeStorageRates.Native
