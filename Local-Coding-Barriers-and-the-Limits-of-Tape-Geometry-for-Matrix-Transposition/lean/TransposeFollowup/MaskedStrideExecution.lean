import TransposeFollowup.MaskedStrideBank

/-! One public schedule executes every full group and the final partial
group. All scratch rewinds and padding cost native transitions. This
processing phase starts from a prepared bank; loading, emitting and final
scratch clearing are not hidden in its cost. -/
namespace TransposeFollowup.MaskedStrideScan
open Classical FixedTapeCompiler ScheduledNativeIO
open MaskedStrideCell (Mode State)
set_option autoImplicit false

def fullSchedule (isPrefix : Bool) (mask : ℕ → Bool) (S i : ℕ) : NativeIO.Program (Fin 2) Mode :=
  MaskedStrideGroup.schedule isPrefix (fun j => mask (i/(4*S)*S+j)) S S (i%(4*S))

theorem fullSchedule_block (isPrefix : Bool) (mask : ℕ → Bool) {S : ℕ} (hS : 0 < S)
    (r i : ℕ) (hi : i < 4*S) :
    fullSchedule isPrefix mask S (r*(4*S)+i)=
      MaskedStrideGroup.schedule isPrefix (fun j => mask (r*S+j)) S S i := by
  have hd : (r*(4*S)+i)/(4*S)=r := by
    rw [Nat.mul_comm r (4*S),Nat.mul_add_div (by omega),Nat.div_eq_of_lt hi,Nat.add_zero]
  simp only [fullSchedule,hd,Nat.mul_add_mod_of_lt hi]

theorem full_exact (isPrefix : Bool) (mask : ℕ → Bool) {S : ℕ} (hS : 0 < S)
    (w : List Bool) (c : State) (r : ℕ) :
    trajectory (fullSchedule isPrefix mask S) w c (r*(4*S))=groups isPrefix mask S w c r := by
  induction r with
  | zero => simp [trajectory,groups]
  | succ r ih =>
    rw [Nat.succ_mul,trajectory_add,ih,
      trajectory_congr (fun i => fullSchedule isPrefix mask S (r*(4*S)+i))
        (MaskedStrideGroup.schedule isPrefix (fun j => mask (r*S+j)) S S) w _ (4*S)
        (fun i hi => fullSchedule_block isPrefix mask hS r i hi),
      MaskedStrideGroup.group_exact]
    rfl

theorem full_prefix (isPrefix : Bool) (mask : ℕ → Bool) {S : ℕ} (hS : 0 < S)
    (w : List Bool) (c : State) (r n : ℕ) (hn : n ≤ 4*S) :
    trajectory (fullSchedule isPrefix mask S) w c (r*(4*S)+n)=
      trajectory (MaskedStrideGroup.schedule isPrefix (fun j => mask (r*S+j)) S S) w
        (groups isPrefix mask S w c r) n := by
  rw [trajectory_add,full_exact isPrefix mask hS]
  apply trajectory_congr
  intro i hi
  exact fullSchedule_block isPrefix mask hS r i (by omega)

def ticks (P S : ℕ) : ℕ := (P/S+1)*(4*S)

def schedule (isPrefix : Bool) (mask : ℕ → Bool) (P S i : ℕ) : NativeIO.Program (Fin 2) Mode :=
  if i < (P/S)*(4*S) then fullSchedule isPrefix mask S i
  else MaskedStrideGroup.schedule isPrefix (fun j => mask (P/S*S+j)) S (P%S) (i-(P/S)*(4*S))

theorem schedule_active (isPrefix : Bool) (mask : ℕ → Bool) (P S i : ℕ) (c : State) :
    NativeIO.Active (schedule isPrefix mask P S i) c := by
  unfold schedule
  split_ifs
  · exact MaskedStrideGroup.active_schedule _ _ _ _ _ _
  · exact MaskedStrideGroup.active_schedule _ _ _ _ _ _

theorem schedule_prefix (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ)
    (w : List Bool) (c : State) (n : ℕ) (hn : n ≤ (P/S)*(4*S)) :
    trajectory (schedule isPrefix mask P S) w c n=trajectory (fullSchedule isPrefix mask S) w c n := by
  apply trajectory_congr
  intro i hi
  simp only [schedule,ite_eq_left (show i < (P/S)*(4*S) by omega)]

theorem schedule_exact (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0 < S)
    (w : List Bool) (c : State) :
    trajectory (schedule isPrefix mask P S) w c (ticks P S)=result isPrefix mask P S w c := by
  rw [ticks,Nat.add_mul,Nat.one_mul,trajectory_add,schedule_prefix _ _ _ _ _ _ _ le_rfl,
    full_exact isPrefix mask hS]
  rw [trajectory_congr (fun i => schedule isPrefix mask P S (P/S*(4*S)+i))
    (MaskedStrideGroup.schedule isPrefix (fun j => mask (P/S*S+j)) S (P%S)) w _ (4*S) (by
      intro i _
      simp only [schedule,ite_eq_right (show ¬P/S*(4*S)+i < P/S*(4*S) by omega),
        Nat.add_sub_cancel_left]),MaskedStrideGroup.group_exact]
  rfl

theorem native_run {P S q : ℕ} (hS : 0 < S)
    (e : NativeMicrocode.Encoding (Fin 2) (Fin (ticks P S+1) × Mode) 2 q)
    (isPrefix : Bool) (mask : ℕ → Bool) (w : List Bool) (c : State) :
    Transpose.stepN (NativeIO.machine e (program (schedule isPrefix mask P S) (ticks P S))) w (ticks P S)
      ((lift (⟨0,by omega⟩ : Fin (ticks P S+1)) c).denote e (program (schedule isPrefix mask P S) (ticks P S)))=
      some ((lift (⟨ticks P S,by omega⟩ : Fin (ticks P S+1)) (result isPrefix mask P S w c)).denote e
        (program (schedule isPrefix mask P S) (ticks P S))) ∧
    Transpose.step (NativeIO.machine e (program (schedule isPrefix mask P S) (ticks P S))) w
      ((lift (⟨ticks P S,by omega⟩ : Fin (ticks P S+1)) (result isPrefix mask P S w c)).denote e
        (program (schedule isPrefix mask P S) (ticks P S)))=none := by
  simpa only [schedule_exact isPrefix mask P hS] using native_run_and_halt e
    (schedule isPrefix mask P S) w c (fun i _ => schedule_active isPrefix mask P S i _)

theorem ticks_le (P S : ℕ) (hSP : S ≤ P) : ticks P S ≤ 8*P := by
  have hd := Nat.div_mul_le_self P S
  unfold ticks
  nlinarith

theorem state_count (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) :
    (NativeIO.machine (NativeMicrocode.initialEncoding (T:=Fin 2)
      ((⟨0,by omega⟩,(false,false)) : Fin (ticks P S+1) × Mode))
      (program (schedule isPrefix mask P S) (ticks P S))).q+1=(ticks P S+1)*4 := by
  exact native_state_count (schedule isPrefix mask P S) (ticks P S) (false,false)

end TransposeFollowup.MaskedStrideScan
