import TransposeFollowup.ScheduledBankRows

/-! Public indexed row updates use the existing paid Update/step interface
and ScheduledWord compiler. Each row can have a different operation; its
actual cost is included in the clock. The constant family agrees with the
existing identical-row executor. -/
namespace TransposeFollowup.IndexedBankRows
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open ScheduledBankRows (Update step stepSchedule step_exact step_active step_position
  step_frame step_value step_clean step_io)
set_option autoImplicit false
variable {M : Type*} {W : ℕ} (U : ℕ → Update M W)

def rows (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  ScheduledWord.transform (fun k => step (U k) w) (List.range r) c

theorem rows_zero (w : List Bool) (c : NativeIO.Config (Fin 2) M) : rows U 0 w c=c := rfl

theorem rows_succ (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    rows U (r+1) w c=step (U r) w (rows U r w c) := by
  simp only [rows,ScheduledWord.transform,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem rows_constant (V : Update M W) (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    rows (fun _ => V) r w c=ScheduledBankRows.rows V r w c := by
  simp only [rows,ScheduledWord.transform,List.foldl_const,List.length_range,ScheduledBankRows.rows]

def rowsTicks (r : ℕ) : ℕ := ScheduledWord.ticks (fun k => (U k).cost+W) (List.range r)

def rowsSchedule (r : ℕ) : ℕ → NativeIO.Program (Fin 2) M :=
  ScheduledWord.schedule (fun k => (U k).cost+W) (fun k => stepSchedule (U k))
    (action 0 ⟨none,.stay⟩) (List.range r)

theorem rows_exact (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    trajectory (rowsSchedule U r) w c (rowsTicks U r)=rows U r w c :=
  ScheduledWord.schedule_exact _ _ _ _ _ w c (fun k _ d => step_exact (U k) w d)

theorem rows_active (r i : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (rowsSchedule U r i) c :=
  ScheduledWord.schedule_active _ _ _ _ c i (active _ _ _) (fun k _ j => step_active (U k) j c)

theorem rowsTicks_eq (r N : ℕ) (hc : ∀ k, (U k).cost+W=N) : rowsTicks U r=r*N := by
  simp only [rowsTicks,ScheduledWord.ticks]
  simp_rw [hc]
  simp only [List.map_const',List.length_range,List.sum_replicate,smul_eq_mul]

theorem rows_position (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) :
    (rows U r w c).work.pos t=c.work.pos t+if t=0 then (r*W : ℕ) else 0 := by
  induction r with
  | zero => simp [rows_zero]
  | succ r ih =>
    rw [rows_succ,step_position,ih]
    by_cases ht : t=0 <;> simp [ht,Nat.add_mul,add_assoc]

theorem rows_clean (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) : BankWord.symbols.clean (rows U r w c) := by
  induction r with
  | zero => exact hc
  | succ r ih => rw [rows_succ]; exact step_clean (U r) w _ ih

theorem rows_io (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) :
    (rows U r w c).inputPos=c.inputPos ∧ (rows U r w c).outRev=c.outRev := by
  induction r with
  | zero => exact ⟨rfl,rfl⟩
  | succ r ih =>
    rw [rows_succ]
    have h := step_io (U r) w (rows U r w c) (rows_clean U r w c hc)
    exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

theorem rows_frame (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ)
    (hz : z < c.work.pos 0 ∨ c.work.pos 0+r*W ≤ z) :
    cells (rows U r w c) 0 z=cells c 0 z := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [rows_succ,step_frame]
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

def ticks (r : ℕ) : ℕ := rowsTicks U r+r*W

def schedule (r : ℕ) : ℕ → NativeIO.Program (Fin 2) M :=
  append (rowsSchedule U r) (fun _ => action 0 ⟨none,.left⟩) (rowsTicks U r)

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

end TransposeFollowup.IndexedBankRows
