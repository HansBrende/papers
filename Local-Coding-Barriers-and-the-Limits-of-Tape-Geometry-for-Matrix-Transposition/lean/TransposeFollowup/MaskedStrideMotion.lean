import TransposeFollowup.MaskedStrideExecution

/-! Exact, data-independent processing-head coordinates. These are derived
from the paid schedule, including padding and every scratch rewind. -/
namespace TransposeFollowup.MaskedStrideGroup
open Classical FixedTapeCompiler ScheduledNativeIO
open MaskedStrideCell (Mode State)
set_option autoImplicit false

theorem positions_simple (isPrefix : Bool) (mask : ℕ → Bool) {S g : ℕ} (hg : g≤S)
    (w : List Bool) (c : State) (n : ℕ) :
    (trajectory (schedule isPrefix mask S g) w c n).work.pos 0=c.work.pos 0+(min (n/3) g : ℕ) ∧
    (trajectory (schedule isPrefix mask S g) w c n).work.pos 1=
      c.work.pos 1+(min (n/3) S : ℕ)-(n-3*S : ℕ) := by
  have h := group_positions isPrefix mask S g w c n
  by_cases hn : n≤3*S
  · have hd : n/3≤S := by omega
    simpa only [ite_eq_left hn,Nat.min_eq_left hd,Nat.sub_eq_zero_of_le hn,Nat.cast_zero,sub_zero] using h
  · have hd : S≤n/3 := by omega
    simpa only [ite_eq_right hn,Nat.min_eq_right hg,Nat.min_eq_right hd,
      Nat.min_eq_right (hg.trans hd)] using h

end TransposeFollowup.MaskedStrideGroup

namespace TransposeFollowup.MaskedStrideScan
open Classical FixedTapeCompiler ScheduledNativeIO
open MaskedStrideCell (Mode State)
set_option autoImplicit false

theorem groups_positions (isPrefix : Bool) (mask : ℕ → Bool) (S : ℕ)
    (w : List Bool) (c : State) (r : ℕ) :
    (groups isPrefix mask S w c r).work.pos 0=c.work.pos 0+(r*S : ℕ) ∧
    (groups isPrefix mask S w c r).work.pos 1=c.work.pos 1 := by
  induction r with
  | zero => simp [groups]
  | succ r ih =>
    have h := MaskedStrideGroup.result_positions isPrefix (fun j => mask (r*S+j)) (S:=S) (g:=S) le_rfl w
      (groups isPrefix mask S w c r)
    refine ⟨?_,h.2.trans ih.2⟩
    change (MaskedStrideGroup.result _ _ _ _ _ _).work.pos 0=_
    rw [h.1,ih.1]
    push_cast
    ring

theorem schedule_tail (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) (c : State) (n : ℕ) :
    trajectory (schedule isPrefix mask P S) w c (P/S*(4*S)+n)=
      trajectory (MaskedStrideGroup.schedule isPrefix (fun j => mask (P/S*S+j)) S (P%S)) w
        (groups isPrefix mask S w c (P/S)) n := by
  rw [trajectory_add,schedule_prefix _ _ _ _ _ _ _ le_rfl,full_exact isPrefix mask hS]
  apply trajectory_congr
  intro i _
  simp only [schedule,ite_eq_right (show ¬P/S*(4*S)+i<P/S*(4*S) by omega),Nat.add_sub_cancel_left]

def bankPosition (P S n : ℕ) : ℕ :=
  if n < P/S*(4*S) then n/(4*S)*S+min ((n%(4*S))/3) S
  else P/S*S+min ((n-P/S*(4*S))/3) (P%S)

def scratchPosition (P S n : ℕ) : ℤ :=
  let s := if n < P/S*(4*S) then n%(4*S) else n-P/S*(4*S)
  (min (s/3) S : ℕ)-(s-3*S : ℕ)

theorem schedule_positions (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) (c : State) (n : ℕ) :
    (trajectory (schedule isPrefix mask P S) w c n).work.pos 0=c.work.pos 0+bankPosition P S n ∧
    (trajectory (schedule isPrefix mask P S) w c n).work.pos 1=c.work.pos 1+scratchPosition P S n := by
  by_cases hn : n<P/S*(4*S)
  · have he := full_prefix isPrefix mask hS w c (n/(4*S)) (n%(4*S)) (Nat.mod_lt n (by omega)).le
    rw [Nat.div_add_mod'] at he
    rw [schedule_prefix _ _ _ _ _ _ _ hn.le,he]
    have h := MaskedStrideGroup.positions_simple isPrefix (fun j => mask (n/(4*S)*S+j)) (S:=S) (g:=S) le_rfl w
      (groups isPrefix mask S w c (n/(4*S))) (n%(4*S))
    have hp := groups_positions isPrefix mask S w c (n/(4*S))
    simpa [bankPosition,scratchPosition,hn,hp.1,hp.2,Nat.cast_add,add_assoc,add_sub_assoc] using h
  · have he := schedule_tail isPrefix mask P hS w c (n-P/S*(4*S))
    rw [Nat.add_sub_cancel' (by omega)] at he
    rw [he]
    have h := MaskedStrideGroup.positions_simple isPrefix (fun j => mask (P/S*S+j)) (Nat.mod_lt P hS).le w
      (groups isPrefix mask S w c (P/S)) (n-P/S*(4*S))
    have hp := groups_positions isPrefix mask S w c (P/S)
    simpa [bankPosition,scratchPosition,hn,hp.1,hp.2,Nat.cast_add,add_assoc,add_sub_assoc] using h

theorem native_positions {P S q : ℕ} (hS : 0<S)
    (e : NativeMicrocode.Encoding (Fin 2) (Fin (ticks P S+1) × Mode) 2 q)
    (isPrefix : Bool) (mask : ℕ → Bool) (w : List Bool) (c : State) (n : ℕ) (hn : n≤ticks P S) :
    ∃ d, Transpose.stepN (NativeIO.machine e (program (schedule isPrefix mask P S) (ticks P S))) w n
      ((lift (⟨0,by omega⟩ : Fin (ticks P S+1)) c).denote e (program (schedule isPrefix mask P S) (ticks P S)))=some d ∧
      d.workPos (e.port 0)=c.work.pos 0+bankPosition P S n ∧
      d.workPos (e.port 1)=c.work.pos 1+scratchPosition P S n := by
  refine ⟨_,native_prefix e (schedule isPrefix mask P S) w c
    (fun i _ => schedule_active isPrefix mask P S i _) n hn,?_⟩
  simpa only [NativeIO.Config.denote,lift,Equiv.symm_apply_apply] using
    schedule_positions isPrefix mask P hS w c n

end TransposeFollowup.MaskedStrideScan
