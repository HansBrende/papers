import TransposeFollowup.ScheduledTransferCell

/-! Public-length, paid transfers between the two work tapes. Reads may
advance in either direction; writes advance right. The proof tracks both
the copied cells and the cells cleared at the source. -/
namespace TransposeFollowup.ScheduledTransfer
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
set_option autoImplicit false
variable {M : Type*}
variable (fromScratch clear left : Bool) (read : CopyMachine.Sym Bool → M)
  (write : M → CopyMachine.Sym Bool) (reset : M)

def copied (c : NativeIO.Config (Fin 2) M) : ℕ → NativeIO.Config (Fin 2) M
  | 0 => c
  | n+1 => cellResult fromScratch clear left read write reset (copied c n)

theorem copied_io (c : NativeIO.Config (Fin 2) M) (n : ℕ) :
    (copied fromScratch clear left read write reset c n).inputPos=c.inputPos ∧
    (copied fromScratch clear left read write reset c n).outRev=c.outRev := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => exact ih

theorem copied_positions (c : NativeIO.Config (Fin 2) M) (n : ℕ) :
    (copied fromScratch clear left read write reset c n).work.pos (source fromScratch)=
      c.work.pos (source fromScratch)+offset left n ∧
    (copied fromScratch clear left read write reset c n).work.pos (target fromScratch)=
      c.work.pos (target fromScratch)+n := by
  induction n with
  | zero => simp [copied,offset]
  | succ n ih =>
    have h := cell_positions fromScratch clear left read write reset
      (copied fromScratch clear left read write reset c n)
    constructor
    · rw [copied,h.1,ih.1,offset_succ left n]; omega
    · rw [copied,h.2,ih.2]; omega

theorem copied_source_away (c : NativeIO.Config (Fin 2) M) (n : ℕ) (z : ℤ)
    (hz : ∀ j < n, z≠c.work.pos (source fromScratch)+offset left j) :
    cells (copied fromScratch clear left read write reset c n) (source fromScratch) z=
      cells c (source fromScratch) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [copied,cell_source,(copied_positions fromScratch clear left read write reset c n).1,
      ite_eq_right (by intro h; exact hz n (by omega) h.2)]
    exact ih (fun j hj => hz j (by omega))

theorem copied_source_next (c : NativeIO.Config (Fin 2) M) (n : ℕ) :
    cells (copied fromScratch clear left read write reset c n) (source fromScratch)
      (c.work.pos (source fromScratch)+offset left n)=
      cells c (source fromScratch) (c.work.pos (source fromScratch)+offset left n) := by
  apply copied_source_away
  intro j hj he
  have h := offset_injective left (add_left_cancel he)
  omega

theorem copied_source_preserved (c : NativeIO.Config (Fin 2) M) (n : ℕ) (z : ℤ) :
    cells (copied fromScratch false left read write reset c n) (source fromScratch) z=
      cells c (source fromScratch) z := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [copied,cell_source,Bool.false_eq_true,false_and,ite_false] using ih

theorem copied_target (c : NativeIO.Config (Fin 2) M) (n j : ℕ) (hj : j<n) :
    cells (copied fromScratch clear left read write reset c n) (target fromScratch)
      (c.work.pos (target fromScratch)+j)=
      write (read (cells c (source fromScratch) (c.work.pos (source fromScratch)+offset left j))) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [copied,cell_target,(copied_positions fromScratch clear left read write reset c n).2]
    by_cases h : j=n
    · subst j
      rw [ite_eq_left rfl,(copied_positions fromScratch clear left read write reset c n).1,
        copied_source_next]
    · rw [ite_eq_right (by omega)]
      exact ih (by omega)

theorem copied_target_outside (c : NativeIO.Config (Fin 2) M) (n : ℕ) (z : ℤ)
    (hz : z<c.work.pos (target fromScratch) ∨ c.work.pos (target fromScratch)+n≤z) :
    cells (copied fromScratch clear left read write reset c n) (target fromScratch) z=
      cells c (target fromScratch) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [copied,cell_target,(copied_positions fromScratch clear left read write reset c n).2,
      ite_eq_right (by omega)]
    exact ih (by omega)

theorem copied_source_cleared (c : NativeIO.Config (Fin 2) M) (n j : ℕ) (hj : j<n) :
    cells (copied fromScratch true left read write reset c n) (source fromScratch)
      (c.work.pos (source fromScratch)+offset left j)=.blank := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [copied,cell_source,(copied_positions fromScratch true left read write reset c n).1]
    by_cases h : j=n
    · subst j; exact ite_eq_left ⟨rfl,rfl⟩
    · rw [ite_eq_right (by intro he; exact h (offset_injective left (add_left_cancel he.2)))]
      exact ih (by omega)

def schedule (i : ℕ) : NativeIO.Program (Fin 2) M :=
  cellSchedule fromScratch clear left read write reset (i%2)

theorem schedule_active (i : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (schedule fromScratch clear left read write reset i) c :=
  cell_active _ _ _ _ _ _ _ _

theorem schedule_exact (w : List Bool) (c : NativeIO.Config (Fin 2) M) (n : ℕ) :
    trajectory (schedule fromScratch clear left read write reset) w c (2*n)=
      copied fromScratch clear left read write reset c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,trajectory_add,ih,
      trajectory_congr (fun i => schedule fromScratch clear left read write reset (2*n+i))
        (cellSchedule fromScratch clear left read write reset) w _ 2 (by
          intro i hi; simp only [schedule,show (2*n+i)%2=i by omega]),cell_exact]
    rfl

theorem schedule_positions (w : List Bool) (c : NativeIO.Config (Fin 2) M) (n : ℕ) :
    (trajectory (schedule fromScratch clear left read write reset) w c n).work.pos (source fromScratch)=
      c.work.pos (source fromScratch)+offset left (n/2) ∧
    (trajectory (schedule fromScratch clear left read write reset) w c n).work.pos (target fromScratch)=
      c.work.pos (target fromScratch)+n/2 := by
  have hp : (trajectory (schedule fromScratch clear left read write reset) w c n).work.pos=
      (copied fromScratch clear left read write reset c (n/2)).work.pos := by
    conv_lhs => rw [show n=2*(n/2)+n%2 by omega]
    rw [trajectory_add,schedule_exact]
    rcases Nat.mod_two_eq_zero_or_one n with he | he
    · rw [he]; rfl
    · rw [he]
      change (NativeIO.step (schedule fromScratch clear left read write reset (2*(n/2))) w
        (copied fromScratch clear left read write reset c (n/2))).work.pos=_
      simp only [schedule,show (2*(n/2))%2=0 by omega,cellSchedule]
      rfl
  rw [hp]
  exact copied_positions fromScratch clear left read write reset c (n/2)

end TransposeFollowup.ScheduledTransfer
