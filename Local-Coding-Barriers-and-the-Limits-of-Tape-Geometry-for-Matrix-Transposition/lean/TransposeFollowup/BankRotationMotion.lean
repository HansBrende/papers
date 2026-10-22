import TransposeFollowup.BankRotation
import TransposeFollowup.BankReversalMotion

/-! Exact rotation paths, with three delayed reversal excursions and
the two intervening paid bank seeks. -/
namespace TransposeFollowup.BankRotation
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (State)
set_option autoImplicit false

def path (P R : ℕ) (h : Fin 2) (n : ℕ) : ℤ :=
  BankReversal.path P h n+
    BankReversal.path (P-R) h (n-BankReversal.ticks P)+
    BankReversal.path R h (n-BankReversal.ticks P-BankReversal.ticks (P-R)-(P-R))+
    if h=0 then ((min (n-BankReversal.ticks P-BankReversal.ticks (P-R)) (P-R) : ℕ) : ℤ)-
      (min (n-BankReversal.ticks P-BankReversal.ticks (P-R)-(P-R)-BankReversal.ticks R) (P-R) : ℕ)
    else 0

theorem schedule_position (P R : ℕ) (w : List Bool) (c : State) (n : ℕ)
    (hn : n≤ticks P R) (h : Fin 2) :
    (trajectory (schedule P R) w c n).work.pos h=c.work.pos h+path P R h n := by
  have hf (d : State) (m : ℕ) :
      (trajectory (fun _ => action 0 ⟨none,.right⟩) w d m).work.pos h=
        d.work.pos h+(if h=0 then (m : ℤ) else 0) := by
    by_cases hh : h=0 <;> simpa [advance,hh] using advance_position 0 w d m h
  have hr (d : State) (m : ℕ) :
      (trajectory (fun _ => action 0 ⟨none,.left⟩) w d m).work.pos h=
        d.work.pos h+(-(if h=0 then (m : ℤ) else 0)) := by
    by_cases hh : h=0 <;> simpa [rewind,hh,sub_eq_add_neg] using rewind_position 0 w d m h
  have h4 := append_position _ _ (BankReversal.ticks R) (P-R) w h _ _
    (fun d m hm => BankReversal.schedule_position R w d m hm h) (fun d m _ => hr d m)
  have h3 := append_position _ _ (P-R) (BankReversal.ticks R+(P-R)) w h _ _
    (fun d m _ => hf d m) h4
  have h2 := append_position _ _ (BankReversal.ticks (P-R))
    ((P-R)+(BankReversal.ticks R+(P-R))) w h _ _
    (fun d m hm => BankReversal.schedule_position (P-R) w d m hm h) h3
  have hall := append_position _ _ (BankReversal.ticks P)
    (BankReversal.ticks (P-R)+((P-R)+(BankReversal.ticks R+(P-R)))) w h _ _
    (fun d m hm => BankReversal.schedule_position P w d m hm h) h2 c n hn
  have hl : n-BankReversal.ticks P-BankReversal.ticks (P-R)-(P-R)-BankReversal.ticks R≤P-R := by
    unfold ticks at hn; omega
  change (trajectory (schedule P R) w c n).work.pos h=_ at hall
  fin_cases h <;>
    simpa [path,BankReversal.path_frozen,Nat.min_eq_left hl,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hall

theorem path_zero (P R : ℕ) (h : Fin 2) : path P R h 0=0 := by
  simp [path,BankReversal.path_zero]

theorem path_after (P R : ℕ) (h : Fin 2) (n : ℕ) (hn : ticks P R≤n) : path P R h n=0 := by
  unfold ticks at hn
  have h1 : BankReversal.ticks P≤n := by omega
  have h2 : BankReversal.ticks (P-R)≤n-BankReversal.ticks P := by omega
  have h3 : BankReversal.ticks R≤n-BankReversal.ticks P-BankReversal.ticks (P-R)-(P-R) := by omega
  have h4 : min (n-BankReversal.ticks P-BankReversal.ticks (P-R)) (P-R)=P-R := by omega
  have h5 : min (n-BankReversal.ticks P-BankReversal.ticks (P-R)-(P-R)-BankReversal.ticks R) (P-R)=P-R := by omega
  simp [path,BankReversal.path_after P h n h1,BankReversal.path_after (P-R) h _ h2,
    BankReversal.path_after R h _ h3,h4,h5]

theorem path_frozen (P R : ℕ) (h : Fin 2) (n : ℕ) : path P R h (min n (ticks P R))=path P R h n := by
  by_cases hn : n≤ticks P R
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega),path_after P R h _ le_rfl,path_after P R h n (by omega)]

end TransposeFollowup.BankRotation
