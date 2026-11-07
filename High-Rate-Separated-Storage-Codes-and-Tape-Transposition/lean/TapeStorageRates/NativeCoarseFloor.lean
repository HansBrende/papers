import TapeStorageRates.NativeCoarsePhases

namespace TapeStorageRates.Native
open Transpose MergeDepth

private theorem mono_step (n a : ℕ) (f : ℕ → ℕ) (hf : Monotone f)
    (lo : ∀ i, a≤f i) : Monotone (fun i => if i<n then a else f i) := by
  intro i j hij
  by_cases hi : i<n
  · by_cases hj : j<n
    · simp [hi,hj]
    · simpa [hi,hj] using lo j
  · have hj : ¬j<n := by omega
    simpa [hi,hj] using hf hij

theorem fineSlot_mono (s : ℕ) : Monotone (fineSlot s) := by
  have tail : Monotone (fun i =>
      if i<2*s then 1 else if i<3*s then 2 else if i<5*s+1 then 3
      else if i<6*s+1 then 4 else if i<8*s+1 then 5 else if i<8*s+2 then 6
      else if i<9*s+1 then 7 else 8) := by
    repeat' apply mono_step
    all_goals first | exact monotone_const | intro i; (try split_ifs) <;> omega
  intro i j hij
  by_cases hi : i=0
  · simp [fineSlot,hi]
  · have hj : j≠0 := by omega
    simpa only [fineSlot,ite_eq_right hi,ite_eq_right hj] using tail hij

set_option maxHeartbeats 1500000 in
/-- Every fine position lies in the block named by its coarse slot. -/
theorem fineOffset_block {s : ℕ} (hs : 0<s) (e : Fin 3) (i : ℕ)
    (hi : i < 10*s+1) :
    (s : ℤ)*coarseOffset e (fineSlot s i) ≤ fineOffset s e i ∧
    fineOffset s e i < (s : ℤ)*(coarseOffset e (fineSlot s i)+1) := by
  generalize hf : fineOffset s e i = z
  generalize hc : coarseOffset e (fineSlot s i) = c
  unfold fineSlot at hc
  split_ifs at hc <;> fin_cases e <;>
    simp [coarseOffset,direction,moveInt] at hc <;> subst c <;>
    unfold fineOffset at hf <;> split_ifs at hf <;>
    (try simp [direction,moveInt] at hf) <;> omega


end TapeStorageRates.Native
