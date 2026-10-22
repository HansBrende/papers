import TransposeFollowup.BankReversal

/-! Exact head paths of the paid reversal routine. The paths include
both transfers, both rewinds and the two single-cell scratch turns. -/
namespace TransposeFollowup.BankReversal
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (State)
set_option autoImplicit false

def path (P : ℕ) (t : Fin 2) (n : ℕ) : ℤ :=
  if t=0 then ((min n (2*P)/2 : ℕ) : ℤ)-(min (n-2*P) P : ℕ)+
    (min (n-2*P-P-1) (2*P)/2 : ℕ)-(min (n-2*P-P-1-2*P) P : ℕ)
  else ((min n (2*P)/2 : ℕ) : ℤ)-(min (n-2*P-P) 1 : ℕ)-
    (min (n-2*P-P-1) (2*P)/2 : ℕ)+(min (n-2*P-P-1-2*P-P) 1 : ℕ)

theorem schedule_position (P : ℕ) (w : List Bool) (c : State) (n : ℕ)
    (hn : n≤ticks P) (t : Fin 2) :
    (trajectory (schedule P) w c n).work.pos t=c.work.pos t+path P t n := by
  have hr (p : Fin 2) (d : State) (m : ℕ) :
      (trajectory (fun _ => action p ⟨none,.left⟩) w d m).work.pos t=
        d.work.pos t+(-(if t=p then (m : ℤ) else 0)) := by
    by_cases ht : t=p <;> simpa [rewind,ht,sub_eq_add_neg] using rewind_position p w d m t
  have hf (d : State) (m : ℕ) :
      (trajectory (ScheduledTransfer.schedule false false false read write (false,false)) w d m).work.pos t=
        d.work.pos t+(m/2 : ℕ) := by
    have h := ScheduledTransfer.schedule_positions false false false read write (false,false) w d m
    fin_cases t
    · simpa [ScheduledTransfer.source,ScheduledTransfer.offset] using h.1
    · simpa [ScheduledTransfer.target] using h.2
  have hb (d : State) (m : ℕ) :
      (trajectory (ScheduledTransfer.schedule true true true read write (false,false)) w d m).work.pos t=
        d.work.pos t+(if t=0 then ((m/2 : ℕ) : ℤ) else -(m/2 : ℕ)) := by
    have h := ScheduledTransfer.schedule_positions true true true read write (false,false) w d m
    fin_cases t
    · simpa [ScheduledTransfer.target] using h.2
    · simpa [ScheduledTransfer.source,ScheduledTransfer.offset] using h.1
  have he (d : State) (m : ℕ) (hm : m≤1) :
      (trajectory (fun _ => action 1 ⟨none,.right⟩) w d m).work.pos t=
        d.work.pos t+(if t=1 then (m : ℤ) else 0) := by
    by_cases ht : t=1 <;>
      interval_cases m <;> simp [trajectory,step_position,ht,NativeMicrocode.direction,Transpose.Dir.shift]
  have h5 := append_position _ _ P 1 w t _ _ (fun d m _ => hr 0 d m) he
  have h4 := append_position _ _ (2*P) (P+1) w t _ _ (fun d m _ => hb d m) h5
  have h3 := append_position _ _ 1 (2*P+(P+1)) w t _ _ (fun d m _ => hr 1 d m) h4
  have h2 := append_position _ _ P (1+(2*P+(P+1))) w t _ _ (fun d m _ => hr 0 d m) h3
  have h1 := append_position _ _ (2*P) (P+(1+(2*P+(P+1)))) w t _ _ (fun d m _ => hf d m) h2
  have h := h1 c n hn
  change (trajectory (schedule P) w c n).work.pos t=_ at h
  have hl : n-2*P-P-1-2*P-P≤1 := by rw [ticks_eq] at hn; omega
  fin_cases t <;> simpa [path,Nat.min_eq_left hl,sub_eq_add_neg,add_assoc] using h

theorem path_frozen (P : ℕ) (t : Fin 2) (n : ℕ) : path P t (min n (ticks P))=path P t n := by
  have ht := ticks_eq P
  have h0 : min (min n (ticks P)) (2*P)=min n (2*P) := by omega
  have h1 : min (min n (ticks P)-2*P) P=min (n-2*P) P := by omega
  have h2 : min (min n (ticks P)-2*P-P) 1=min (n-2*P-P) 1 := by omega
  have h3 : min (min n (ticks P)-2*P-P-1) (2*P)=min (n-2*P-P-1) (2*P) := by omega
  have h4 : min (min n (ticks P)-2*P-P-1-2*P) P=min (n-2*P-P-1-2*P) P := by omega
  have h5 : min (min n (ticks P)-2*P-P-1-2*P-P) 1=min (n-2*P-P-1-2*P-P) 1 := by omega
  simp only [path,h0,h1,h2,h3,h4,h5]

theorem path_zero (P : ℕ) (t : Fin 2) : path P t 0=0 := by simp [path]

theorem path_after (P : ℕ) (t : Fin 2) (n : ℕ) (hn : ticks P≤n) : path P t n=0 := by
  rw [ticks_eq] at hn
  have h0 : min n (2*P)=2*P := by omega
  have h1 : min (n-2*P) P=P := by omega
  have h2 : min (n-2*P-P) 1=1 := by omega
  have h3 : min (n-2*P-P-1) (2*P)=2*P := by omega
  have h4 : min (n-2*P-P-1-2*P) P=P := by omega
  have h5 : min (n-2*P-P-1-2*P-P) 1=1 := by omega
  simp [path,h0,h1,h2,h3,h4,h5]

end TransposeFollowup.BankReversal
