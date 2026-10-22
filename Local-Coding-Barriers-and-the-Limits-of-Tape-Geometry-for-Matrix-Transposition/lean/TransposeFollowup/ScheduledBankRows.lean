import TransposeFollowup.RawRowBankInvariant
import TransposeFollowup.ScheduledAdvance
import TransposeFollowup.RepeatedScheduleMotion

/-! Sequential independent row updates, with paid advances and a final
rewind. Each update supplies an actual native schedule, a local symbol
specification, and a frame theorem. Clean scratch is preserved between
rows. No symbolic row update is counted as a machine instruction. -/
namespace TransposeFollowup.ScheduledBankRows
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym)
set_option autoImplicit false
variable {M : Type*} {W : ℕ}

structure Update (M : Type*) (W : ℕ) where
  cost : ℕ
  code : ℕ → NativeIO.Program (Fin 2) M
  value : (ℕ → Sym Bool) → ℕ → Sym Bool
  congruent : BankWord.Congruent W value
  active : ∀ i c, NativeIO.Active (code i) c
  endpoint : ∀ w c t, (trajectory code w c cost).work.pos t=c.work.pos t
  represents : ∀ w c, BankWord.symbols.clean c →
    BankWord.Represents BankWord.symbols W c (trajectory code w c cost)
      (value (BankWord.input BankWord.symbols c))
  frame : ∀ (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ),
    z<c.work.pos 0 ∨ c.work.pos 0+W ≤ z →
    cells (trajectory code w c cost) 0 z=cells c 0 z

variable (U : Update M W)

def step (w : List Bool) (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  advance 0 w (trajectory U.code w c U.cost) W

def stepSchedule : ℕ → NativeIO.Program (Fin 2) M :=
  append U.code (fun _ => action 0 ⟨none,.right⟩) U.cost

theorem step_exact (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    trajectory (stepSchedule U) w c (U.cost+W)=step U w c := by
  rw [stepSchedule,append_exact]
  rfl

theorem step_active (i : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (stepSchedule U i) c := by
  apply append_active
  · intro j; exact U.active j c
  · intro _; exact active _ _ _

theorem step_position (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) :
    (step U w c).work.pos t=c.work.pos t+if t=0 then W else 0 := by
  rw [step,advance_position,U.endpoint]

theorem step_frame (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+W ≤ z) :
    cells (step U w c) 0 z=cells c 0 z := by
  rw [step,advance_cells]
  exact U.frame w c z hz

theorem step_value (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) (j : ℕ) (hj : j<W) :
    cells (step U w c) 0 (c.work.pos 0+j)=U.value (BankWord.input BankWord.symbols c) j := by
  rw [step,advance_cells]
  exact (U.represents w c hc).2.1 j hj

theorem step_clean (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) : BankWord.symbols.clean (step U w c) := by
  intro z
  change cells (advance 0 w (trajectory U.code w c U.cost) W) 1 z=.blank
  rw [advance_cells]
  exact (U.represents w c hc).2.2.1 z

theorem step_io (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) :
    (step U w c).inputPos=c.inputPos ∧ (step U w c).outRev=c.outRev := by
  have h := advance_io 0 w (trajectory U.code w c U.cost) W
  have hh := U.represents w c hc
  exact ⟨h.1.trans hh.2.2.2.1,h.2.trans hh.2.2.2.2⟩

def rows (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  (step U w)^[r] c

def rowsSchedule (r : ℕ) : ℕ → NativeIO.Program (Fin 2) M :=
  repeatSchedule (stepSchedule U) (action 0 ⟨none,.stay⟩) (U.cost+W) r

theorem rows_exact (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    trajectory (rowsSchedule U r) w c (r*(U.cost+W))=rows U r w c := by
  simpa only [rowsSchedule,rows,step_exact] using
    repeat_exact (stepSchedule U) (action 0 ⟨none,.stay⟩) (U.cost+W) r w c

theorem rows_active (r i : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (rowsSchedule U r i) c := by
  apply ScheduledWord.schedule_active
  · exact active _ _ _
  · intro _ _ j; exact step_active U j c

theorem rows_position (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) :
    (rows U r w c).work.pos t=c.work.pos t+if t=0 then r*W else 0 := by
  have h := repeat_endpoint (stepSchedule U) (action 0 ⟨none,.stay⟩) (U.cost+W) w t
    (if t=0 then (W : ℤ) else 0) (fun d => by
      rw [step_exact,step_position]
      by_cases ht : t=0 <;> simp [ht]) r c
  rw [← rows_exact]
  by_cases ht : t=0 <;> simpa [rowsSchedule,ht] using h

theorem rows_clean (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) : BankWord.symbols.clean (rows U r w c) := by
  induction r with
  | zero => exact hc
  | succ r ih =>
    change BankWord.symbols.clean ((step U w)^[r+1] c)
    rw [Function.iterate_succ_apply']
    exact step_clean U w _ ih

theorem rows_io (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) :
    (rows U r w c).inputPos=c.inputPos ∧ (rows U r w c).outRev=c.outRev := by
  induction r with
  | zero => exact ⟨rfl,rfl⟩
  | succ r ih =>
    simp only [rows,Function.iterate_succ_apply']
    have h := step_io U w (rows U r w c) (rows_clean U r w c hc)
    exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

theorem rows_frame (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+r*W ≤ z) :
    cells (rows U r w c) 0 z=cells c 0 z := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change cells ((step U w)^[r+1] c) 0 z=_
    rw [Function.iterate_succ_apply']
    change cells (step U w (rows U r w c)) 0 z=_
    rw [step_frame]
    · apply ih
      have : (r : ℤ)*W ≤ (r+1)*W := mul_le_mul_of_nonneg_right (by omega) (Nat.cast_nonneg W)
      push_cast at hz
      omega
    · rw [rows_position]
      simp only [ite_true,Nat.cast_mul]
      push_cast at hz
      have : (0 : ℤ) ≤ r*W := mul_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg W)
      rcases hz with hz | hz
      · left; omega
      · right; nlinarith

def ticks (r : ℕ) : ℕ := r*(U.cost+W)+r*W

def schedule (r : ℕ) : ℕ → NativeIO.Program (Fin 2) M :=
  append (rowsSchedule U r) (fun _ => action 0 ⟨none,.left⟩) (r*(U.cost+W))

def result (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  rewind 0 w (rows U r w c) (r*W)

theorem schedule_exact (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    trajectory (schedule U r) w c (ticks U r)=result U r w c := by
  rw [schedule,ticks,append_exact,rows_exact]
  rfl

theorem schedule_active (r i : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (schedule U r i) c := by
  apply append_active
  · intro j; exact rows_active U r j c
  · intro _; exact active _ _ _

theorem result_position (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) :
    (result U r w c).work.pos t=c.work.pos t := by
  rw [result,rewind_position,rows_position]
  by_cases ht : t=0 <;> simp [ht]

theorem result_cells (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) (z : ℤ) :
    cells (result U r w c) t z=cells (rows U r w c) t z := rewind_cells _ _ _ _ _ _

end TransposeFollowup.ScheduledBankRows
