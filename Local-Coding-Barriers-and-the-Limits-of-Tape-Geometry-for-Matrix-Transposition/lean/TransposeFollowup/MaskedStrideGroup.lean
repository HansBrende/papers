import TransposeFollowup.MaskedStrideCell

/-! A fixed 4*S-tick masked group slab. Its first g<=S slots update real
bank bits; padded slots move only the scratch head. All S scratch positions
are then physically rewound. The return state is an exact iteration of the
proved cell update; cross-group recurrence and raw IO remain separate. -/
namespace TransposeFollowup.MaskedStrideGroup
open Classical FixedTapeCompiler
open ScheduledNativeIO
open MaskedStrideCell (Mode State)
set_option autoImplicit false

def moveBuffer (d : Microcode.Move) : NativeIO.Program (Fin 2) Mode := fun m =>
  .work (.act (fun t => ⟨none,if t=1 then d else .stay⟩) m)

theorem moveBuffer_active (d : Microcode.Move) (c : State) : NativeIO.Active (moveBuffer d) c := by
  simp [moveBuffer,NativeIO.Active]

theorem moveBuffer_positions (d : Microcode.Move) (w : List Bool) (c : State) :
    (NativeIO.step (moveBuffer d) w c).work.pos 0=c.work.pos 0 ∧
    (NativeIO.step (moveBuffer d) w c).work.pos 1=(NativeMicrocode.direction d).shift (c.work.pos 1) := by
  constructor <;> rfl

def padding : ℕ → NativeIO.Program (Fin 2) Mode
  | 0 | 1 => fun m => .work (.jump m)
  | _+2 => moveBuffer .right

def padResult (w : List Bool) (c : State) : State := NativeIO.step (moveBuffer .right) w c

theorem padding_three (w : List Bool) (c : State) : trajectory padding w c 3=padResult w c := rfl

def slotSchedule (isPrefix : Bool) (mask : ℕ → Bool) (g j : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  if j < g then MaskedStrideCell.schedule isPrefix (mask j) else padding

theorem slot_active (isPrefix : Bool) (mask : ℕ → Bool) (g j i : ℕ) (c : State) :
    NativeIO.Active (slotSchedule isPrefix mask g j i) c := by
  by_cases h : j < g
  · simpa only [slotSchedule,ite_eq_left h] using MaskedStrideCell.active_schedule isPrefix (mask j) i c
  · simp only [slotSchedule,ite_eq_right h]
    cases i with
    | zero => simp [padding,NativeIO.Active]
    | succ i => cases i <;> simp [padding,NativeIO.Active,moveBuffer]

theorem slot_early_positions (isPrefix : Bool) (mask : ℕ → Bool) (g j : ℕ)
    (w : List Bool) (c : State) (r : ℕ) (hr : r < 3) :
    (trajectory (slotSchedule isPrefix mask g j) w c r).work.pos=c.work.pos := by
  by_cases h : j < g
  · simp only [slotSchedule,ite_eq_left h]
    interval_cases r <;> rfl
  · simp only [slotSchedule,ite_eq_right h]
    interval_cases r <;> rfl

def slots (isPrefix : Bool) (mask : ℕ → Bool) (g : ℕ) (w : List Bool) (c : State) : ℕ → State
  | 0 => c
  | n+1 => if n < g then MaskedStrideCell.result isPrefix (mask n) (slots isPrefix mask g w c n)
      else padResult w (slots isPrefix mask g w c n)

def processSchedule (isPrefix : Bool) (mask : ℕ → Bool) (g : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  fun i => slotSchedule isPrefix mask g (i/3) (i%3)

theorem process_exact (isPrefix : Bool) (mask : ℕ → Bool) (g : ℕ) (w : List Bool) (c : State) (n : ℕ) :
    trajectory (processSchedule isPrefix mask g) w c (3*n)=slots isPrefix mask g w c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3*n+3 by omega,trajectory_add,ih]
    rw [trajectory_congr (fun i => processSchedule isPrefix mask g (3*n+i))
      (slotSchedule isPrefix mask g n) w _ 3 (by
        intro i hi
        have hd : (3*n+i)/3=n := by omega
        have hm : (3*n+i)%3=i := by omega
        simp only [processSchedule,hd,hm])]
    by_cases h : n < g
    · simp only [slotSchedule,ite_eq_left h,MaskedStrideCell.trajectory_three,slots]
    · simp only [slotSchedule,ite_eq_right h,padding_three,slots]

theorem slots_positions (isPrefix : Bool) (mask : ℕ → Bool) (g : ℕ)
    (w : List Bool) (c : State) (n : ℕ) :
    (slots isPrefix mask g w c n).work.pos 0=c.work.pos 0+(min n g : ℕ) ∧
    (slots isPrefix mask g w c n).work.pos 1=c.work.pos 1+n := by
  induction n with
  | zero => simp [slots]
  | succ n ih =>
    by_cases h : n < g
    · have hm : min (n+1) g=min n g+1 := by omega
      rw [slots,ite_eq_left h]
      constructor
      · rw [MaskedStrideCell.result_positions,ih.1,hm]
        push_cast
        omega
      · rw [MaskedStrideCell.result_positions,ih.2]
        push_cast
        omega
    · have hm : min (n+1) g=min n g := by omega
      rw [slots,ite_eq_right h]
      constructor
      · exact ((moveBuffer_positions .right w _).1.trans ih.1).trans (by rw [hm])
      · change (NativeIO.step (moveBuffer .right) w _).work.pos 1=_
        rw [(moveBuffer_positions .right w _).2,ih.2]
        simp only [NativeMicrocode.direction,Transpose.Dir.shift,Int.natCast_add,Int.natCast_one]
        omega

theorem rewind_positions (w : List Bool) (c : State) (n : ℕ) :
    (trajectory (fun _ => moveBuffer .left) w c n).work.pos 0=c.work.pos 0 ∧
    (trajectory (fun _ => moveBuffer .left) w c n).work.pos 1=c.work.pos 1-n := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    change (NativeIO.step (moveBuffer .left) w _).work.pos 0=_ ∧
      (NativeIO.step (moveBuffer .left) w _).work.pos 1=_
    constructor
    · exact (moveBuffer_positions .left w _).1.trans ih.1
    · rw [(moveBuffer_positions .left w _).2,ih.2]
      simp only [NativeMicrocode.direction,Transpose.Dir.shift,Int.natCast_add,Int.natCast_one]
      omega

theorem process_positions (isPrefix : Bool) (mask : ℕ → Bool) (g : ℕ)
    (w : List Bool) (c : State) (n : ℕ) :
    (trajectory (processSchedule isPrefix mask g) w c n).work.pos 0=c.work.pos 0+(min (n/3) g : ℕ) ∧
    (trajectory (processSchedule isPrefix mask g) w c n).work.pos 1=c.work.pos 1+(n/3 : ℕ) := by
  have hstate : trajectory (processSchedule isPrefix mask g) w c n=
      trajectory (slotSchedule isPrefix mask g (n/3)) w
        (slots isPrefix mask g w c (n/3)) (n%3) := by
    calc
      trajectory (processSchedule isPrefix mask g) w c n =
          trajectory (processSchedule isPrefix mask g) w c (3*(n/3)+n%3) := by congr 1; omega
      _ = _ := by
        rw [trajectory_add,process_exact]
        apply trajectory_congr
        intro i hi
        have hd : (3*(n/3)+i)/3=n/3 := by omega
        have hm : (3*(n/3)+i)%3=i := by omega
        simp only [processSchedule,hd,hm]
  rw [hstate,slot_early_positions isPrefix mask g (n/3) w _ (n%3) (by omega)]
  exact slots_positions isPrefix mask g w c (n/3)

def schedule (isPrefix : Bool) (mask : ℕ → Bool) (S g : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  fun i => if i < 3*S then processSchedule isPrefix mask g i else moveBuffer .left

def result (isPrefix : Bool) (mask : ℕ → Bool) (S g : ℕ) (w : List Bool) (c : State) : State :=
  trajectory (fun _ => moveBuffer .left) w (slots isPrefix mask g w c S) S

theorem group_prefix (isPrefix : Bool) (mask : ℕ → Bool) (S g : ℕ)
    (w : List Bool) (c : State) (n : ℕ) :
    trajectory (schedule isPrefix mask S g) w c n =
      if n ≤ 3*S then trajectory (processSchedule isPrefix mask g) w c n
      else trajectory (fun _ => moveBuffer .left) w (slots isPrefix mask g w c S) (n-3*S) := by
  by_cases hn : n ≤ 3*S
  · rw [ite_eq_left hn]
    exact trajectory_congr _ _ w c n (by intro i hi; simp only [schedule,ite_eq_left (show i<3*S by omega)])
  · rw [ite_eq_right hn]
    calc
      trajectory (schedule isPrefix mask S g) w c n =
          trajectory (schedule isPrefix mask S g) w c (3*S+(n-3*S)) := by congr 1; omega
      _ = _ := by
        rw [trajectory_add]
        rw [trajectory_congr (schedule isPrefix mask S g) (processSchedule isPrefix mask g) w c (3*S)
          (by intro i hi; simp only [schedule,ite_eq_left hi]),process_exact]
        exact trajectory_congr _ _ w _ _ (by
          intro i _
          simp only [schedule,ite_eq_right (show ¬3*S+i<3*S by omega)])

theorem group_positions (isPrefix : Bool) (mask : ℕ → Bool) (S g : ℕ)
    (w : List Bool) (c : State) (n : ℕ) :
    (trajectory (schedule isPrefix mask S g) w c n).work.pos 0 =
      c.work.pos 0+(if n ≤ 3*S then min (n/3) g else min S g : ℕ) ∧
    (trajectory (schedule isPrefix mask S g) w c n).work.pos 1 =
      if n ≤ 3*S then c.work.pos 1+(n/3 : ℕ) else c.work.pos 1+S-(n-3*S : ℕ) := by
  rw [group_prefix]
  by_cases hn : n ≤ 3*S
  · simpa only [ite_eq_left hn] using process_positions isPrefix mask g w c n
  · have h := rewind_positions w (slots isPrefix mask g w c S) (n-3*S)
    have hs := slots_positions isPrefix mask g w c S
    simpa only [ite_eq_right hn,hs.1,hs.2] using h

theorem group_exact (isPrefix : Bool) (mask : ℕ → Bool) (S g : ℕ) (w : List Bool) (c : State) :
    trajectory (schedule isPrefix mask S g) w c (4*S)=result isPrefix mask S g w c := by
  by_cases hS : S=0
  · subst S
    rfl
  · rw [group_prefix,ite_eq_right (show ¬4*S ≤ 3*S by omega),show 4*S-3*S=S by omega]
    rfl

theorem active_schedule (isPrefix : Bool) (mask : ℕ → Bool) (S g i : ℕ) (c : State) :
    NativeIO.Active (schedule isPrefix mask S g i) c := by
  by_cases h : i < 3*S
  · simpa only [schedule,ite_eq_left h,processSchedule] using slot_active isPrefix mask g (i/3) (i%3) c
  · simpa only [schedule,ite_eq_right h] using moveBuffer_active .left c

theorem result_positions (isPrefix : Bool) (mask : ℕ → Bool) {S g : ℕ} (hg : g ≤ S)
    (w : List Bool) (c : State) :
    (result isPrefix mask S g w c).work.pos 0=c.work.pos 0+g ∧
    (result isPrefix mask S g w c).work.pos 1=c.work.pos 1 := by
  have h := rewind_positions w (slots isPrefix mask g w c S) S
  have hs := slots_positions isPrefix mask g w c S
  simpa only [result,hs.1,hs.2,Nat.min_eq_right hg,add_sub_cancel_right] using h

theorem native_group {S g q : ℕ}
    (e : NativeMicrocode.Encoding (Fin 2) (Fin (4*S+1) × Mode) 2 q)
    (isPrefix : Bool) (mask : ℕ → Bool) (w : List Bool) (c : State) :
    Transpose.stepN (NativeIO.machine e (program (schedule isPrefix mask S g) (4*S))) w (4*S)
      ((lift ⟨0,by omega⟩ c).denote e (program (schedule isPrefix mask S g) (4*S))) =
      some ((lift ⟨4*S,by omega⟩ (result isPrefix mask S g w c)).denote e
        (program (schedule isPrefix mask S g) (4*S))) ∧
    Transpose.step (NativeIO.machine e (program (schedule isPrefix mask S g) (4*S))) w
      ((lift ⟨4*S,by omega⟩ (result isPrefix mask S g w c)).denote e
        (program (schedule isPrefix mask S g) (4*S)))=none := by
  simpa only [group_exact] using native_run_and_halt e (schedule isPrefix mask S g) w c
    (fun i _ => active_schedule isPrefix mask S g i _)

end TransposeFollowup.MaskedStrideGroup
