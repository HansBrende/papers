import TransposeFollowup.BankSymbolRotation
import TransposeFollowup.BankBlockReversalMotion

/-! Constant-error motion for the shared symbol rotation. Each of the
three width-one reversals contributes at most five cells of error. Paid
seeks and the stationary padding use the existing append estimate. -/
namespace TransposeFollowup.BankSymbolRotation
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open SharedBankSymbols
set_option autoImplicit false

def path (P R : ℕ) (t : Fin 2) (n : ℕ) : ℤ :=
  BankBlockReversal.path P t n+
    BankBlockReversal.path (P-R) t (n-10*P)+
    BankBlockReversal.path R t (n-10*P-10*(P-R)-(P-R))+
    if t=0 then ((min (n-10*P-10*(P-R)) (P-R) : ℕ) : ℤ)-
      (min (n-10*P-10*(P-R)-(P-R)-10*R) (P-R) : ℕ)
    else 0

theorem path_zero (P R : ℕ) (t : Fin 2) : path P R t 0=0 := by
  simp [path,BankBlockReversal.path_zero]

theorem reverse_path_error (Q : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (m : ℕ) (hm : m ≤ 10*Q) (t : Fin 2) :
    |(trajectory (RawBlockReversal.schedule 1 Q) w c m).work.pos t-c.work.pos t-
      BankBlockReversal.path Q t m| ≤ 5 := by
  simpa only [BankBlockReversal.ticks_eq,mul_one,Nat.cast_one,RawBlockReversal.schedule] using
    BankBlockReversal.schedule_path_error read write reset 1 Q (by decide) w c m
      (by simpa only [BankBlockReversal.ticks_eq,mul_one] using hm) t

def tailPath (L R : ℕ) (t : Fin 2) (n : ℕ) : ℤ :=
  BankBlockReversal.path R t (n-L)+
    if t=0 then ((min n L : ℕ) : ℤ)-(min (n-L-10*R) L : ℕ) else 0

theorem tail_path_error (L R : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (n : ℕ) (hn : n ≤ L+(10*R+L)) (t : Fin 2) :
    |(trajectory (append (fun _ => action 0 ⟨none,.right⟩)
        (append (RawBlockReversal.schedule 1 R) (fun _ => action 0 ⟨none,.left⟩) (10*R)) L)
      w c n).work.pos t-c.work.pos t-tailPath L R t n| ≤ 5 := by
  have hf (d : SharedRowBank.State) (m : ℕ) :
      |(trajectory (fun _ => action 0 ⟨none,.right⟩) w d m).work.pos t-d.work.pos t-
        (if t=0 then (m : ℤ) else 0)| ≤ 0 := by
    change |(advance 0 w d m).work.pos t-d.work.pos t-_| ≤ 0
    rw [advance_position]
    simp
  have hr (d : SharedRowBank.State) (m : ℕ) :
      |(trajectory (fun _ => action 0 ⟨none,.left⟩) w d m).work.pos t-d.work.pos t-
        (-(if t=0 then (m : ℤ) else 0))| ≤ 0 := by
    change |(rewind 0 w d m).work.pos t-d.work.pos t-_| ≤ 0
    rw [rewind_position]
    simp
  have h4 := append_position_error _ _ (10*R) L w t
    (BankBlockReversal.path R t) (fun m => -(if t=0 then (m : ℤ) else 0)) 5 0 le_rfl
    (by simp) (fun d m hm => reverse_path_error R w d m hm t) (fun d m _ => hr d m)
  have h3 := append_position_error _ _ L (10*R+L) w t
    (fun m => if t=0 then (m : ℤ) else 0) _ 0 (5+0) (by norm_num)
    (by simp [BankBlockReversal.path_zero]) (fun d m _ => hf d m) h4 c n hn
  have hl : n-L-10*R ≤ L := by omega
  fin_cases t <;>
    simpa [tailPath,BankBlockReversal.path_frozen,Nat.min_eq_left hl,sub_eq_add_neg,
      add_assoc,add_comm,add_left_comm] using h3

theorem base_path_error (P R : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (n : ℕ) (hn : n ≤ baseTicks P R) (t : Fin 2) :
    |(trajectory (baseSchedule P R) w c n).work.pos t-c.work.pos t-path P R t n| ≤ 15 := by
  have h2 := append_position_error _ _ (10*(P-R)) ((P-R)+(10*R+(P-R))) w t
    (BankBlockReversal.path (P-R) t) (tailPath (P-R) R t) 5 5 (by norm_num)
    (by simp [tailPath,BankBlockReversal.path_zero])
    (fun d m hm => reverse_path_error (P-R) w d m hm t)
    (fun d m hm => tail_path_error (P-R) R w d m hm t)
  have h1 := append_position_error _ _ (10*P) (10*(P-R)+((P-R)+(10*R+(P-R)))) w t
    (BankBlockReversal.path P t) _ 5 (5+5) (by norm_num)
    (by simp [tailPath,BankBlockReversal.path_zero])
    (fun d m hm => reverse_path_error P w d m hm t) h2 c n hn
  simpa only [baseSchedule,path,tailPath,BankBlockReversal.path_frozen,add_assoc,
    show (5+(5+5) : ℤ)=15 by norm_num] using h1

theorem path_after (P R : ℕ) (t : Fin 2) (n : ℕ) (hn : baseTicks P R ≤ n) :
    path P R t n=0 := by
  unfold baseTicks at hn
  have h1 : 10*P ≤ n := by omega
  have h2 : 10*(P-R) ≤ n-10*P := by omega
  have h3 : 10*R ≤ n-10*P-10*(P-R)-(P-R) := by omega
  have h4 : min (n-10*P-10*(P-R)) (P-R)=P-R := by omega
  have h5 : min (n-10*P-10*(P-R)-(P-R)-10*R) (P-R)=P-R := by omega
  simp [path,BankBlockReversal.path_after P t n h1,
    BankBlockReversal.path_after (P-R) t _ h2,BankBlockReversal.path_after R t _ h3,h4,h5]

theorem path_frozen_base (P R : ℕ) (t : Fin 2) (n : ℕ) :
    path P R t (min n (baseTicks P R))=path P R t n := by
  by_cases hn : n ≤ baseTicks P R
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega),path_after P R t _ le_rfl,path_after P R t n (by omega)]

theorem path_frozen (P R : ℕ) (t : Fin 2) (n : ℕ) :
    path P R t (min n (ticks P R))=path P R t n := by
  have hb : baseTicks P R ≤ ticks P R := by unfold ticks; omega
  by_cases hn : n ≤ ticks P R
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega),path_after P R t _ hb,path_after P R t n (by omega)]

theorem schedule_path_error (P R : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (n : ℕ) (hn : n ≤ ticks P R) (t : Fin 2) :
    |(trajectory (schedule P R) w c n).work.pos t-c.work.pos t-path P R t n| ≤ 15 := by
  have h := append_position_error (baseSchedule P R) (fun _ => idle) (baseTicks P R) (2*R)
    w t (path P R t) (fun _ => 0) 15 0 le_rfl rfl
    (fun d m hm => base_path_error P R w d m hm t)
    (fun d m _ => by rw [idle_exact]; simp) c n hn
  simpa only [schedule,path_frozen_base,add_zero] using h

end TransposeFollowup.BankSymbolRotation
