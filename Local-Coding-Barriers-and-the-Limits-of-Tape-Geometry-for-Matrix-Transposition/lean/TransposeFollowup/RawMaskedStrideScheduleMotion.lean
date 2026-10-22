import TransposeFollowup.ScheduledRawIOMotion
import TransposeFollowup.ScheduledMotion
import TransposeFollowup.RawMaskedStrideMotion

/-! Exact head coordinates through all seven paid raw-execution phases.
These prefix formulas are valid up to the final halt; the native frozen
tail is connected separately through the original paper's run semantics. -/
namespace TransposeFollowup.RawMaskedStride
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (State)
set_option autoImplicit false

def bankPrefix (P S n : ℕ) : ℤ :=
  ((min n (3*P)+1)/3 : ℕ)-(min (n-3*P) P : ℕ)+
    (MaskedStrideScan.bankPosition P S (min (n-3*P-P) (MaskedStrideScan.ticks P S)) : ℕ)-
    (min (n-3*P-P-MaskedStrideScan.ticks P S-S-S) P : ℕ)+
    ((n-3*P-P-MaskedStrideScan.ticks P S-S-S-P)/3 : ℕ)

def scratchPrefix (P S n : ℕ) : ℤ :=
  MaskedStrideScan.scratchPosition P S (min (n-3*P-P) (MaskedStrideScan.ticks P S))+
    (min (n-3*P-P-MaskedStrideScan.ticks P S) S : ℕ)-
    (min (n-3*P-P-MaskedStrideScan.ticks P S-S) S : ℕ)

theorem schedule_position (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0<S) (w : List Bool) (c : State) (n : ℕ) (hn : n ≤ ticks P S) (t : Fin 2) :
    (trajectory (schedule isPrefix mask P S) w c n).work.pos t=
      c.work.pos t+if t=0 then bankPrefix P S n else scratchPrefix P S n := by
  have hr0 (d : State) (m : ℕ) :
      (trajectory (fun _ => action 0 ⟨none,.left⟩) w d m).work.pos t=
        d.work.pos t+(-(if t=0 then (m : ℤ) else 0)) := by
    by_cases ht : t=0 <;> simpa [rewind,ht,sub_eq_add_neg] using rewind_position (M:=MaskedStrideCell.Mode) 0 w d m t
  have hr1 (d : State) (m : ℕ) :
      (trajectory (fun _ => action 1 ⟨none,.left⟩) w d m).work.pos t=
        d.work.pos t+(-(if t=1 then (m : ℤ) else 0)) := by
    by_cases ht : t=1 <;> simpa [rewind,ht,sub_eq_add_neg] using rewind_position (M:=MaskedStrideCell.Mode) 1 w d m t
  have he1 (d : State) (m : ℕ) :
      (trajectory (fun _ => action 1 ⟨some .blank,.right⟩) w d m).work.pos t=
        d.work.pos t+(if t=1 then (m : ℤ) else 0) := by
    by_cases ht : t=1 <;> simpa [erase,ht] using erase_position (M:=MaskedStrideCell.Mode) 1 w d m t
  have hp (d : State) (m : ℕ) :
      (trajectory (MaskedStrideScan.schedule isPrefix mask P S) w d m).work.pos t=
        d.work.pos t+(if t=0 then (MaskedStrideScan.bankPosition P S m : ℤ)
          else MaskedStrideScan.scratchPosition P S m) := by
    have h := MaskedStrideScan.schedule_positions isPrefix mask P hS w d m
    fin_cases t
    · simpa using h.1
    · simpa using h.2
  have h6 := append_position _ _ P (3*P) w t _ _
    (fun d m _ => hr0 d m) (fun d m _ => ScheduledRawOutput.schedule_position w d m t)
  have h5 := append_position _ _ S (P+3*P) w t _ _ (fun d m _ => hr1 d m) h6
  have h4 := append_position _ _ S (S+(P+3*P)) w t _ _ (fun d m _ => he1 d m) h5
  have h3 := append_position _ _ (MaskedStrideScan.ticks P S) (S+(S+(P+3*P))) w t _ _
    (fun d m _ => hp d m) h4
  have h2 := append_position _ _ P (MaskedStrideScan.ticks P S+(S+(S+(P+3*P)))) w t _ _
    (fun d m _ => hr0 d m) h3
  have h1 := append_position _ _ (3*P) (P+(MaskedStrideScan.ticks P S+(S+(S+(P+3*P))))) w t _ _
    (fun d m _ => ScheduledRawInput.schedule_position w d m t) h2
  have h := h1 c n hn
  change (trajectory (schedule isPrefix mask P S) w c n).work.pos t=_ at h
  fin_cases t <;> simpa [bankPrefix,scratchPrefix,sub_eq_add_neg,add_assoc] using h

end TransposeFollowup.RawMaskedStride
