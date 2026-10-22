import TransposeFollowup.ScheduledRawInput

/-! A read-only bank emitter: read a cell, emit its decoded bit, advance.
The output order is proved against the original machine's reversed list. -/
namespace TransposeFollowup.ScheduledRawOutput
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
set_option autoImplicit false

def cellSchedule : ℕ → NativeIO.Program (Fin 2) Mode
  | 0 => fun _ => .work (.read 0 (fun s => (bit s,false)))
  | 1 => fun m => .output m.1 m
  | _+2 => action 0 ⟨none,.right⟩

def cellResult (w : List Bool) (c : State) : State :=
  let b := bit (c.work.core.tapes 0).head
  {NativeIO.setLabel (NativeIO.step (action 0 ⟨none,.right⟩) w c) (b,false)
    with outRev:=b::c.outRev}

theorem cell_exact (w : List Bool) (c : State) : trajectory cellSchedule w c 3=cellResult w c := rfl

theorem cell_active (i : ℕ) (c : State) : NativeIO.Active (cellSchedule i) c := by
  cases i with
  | zero => simp [cellSchedule,NativeIO.Active]
  | succ i => cases i with
    | zero => trivial
    | succ _ => exact ScheduledTapeAction.active _ _ _

theorem cell_position (w : List Bool) (c : State) (t : Fin 2) :
    (cellResult w c).work.pos t=c.work.pos t+if t=0 then 1 else 0 := by
  have h := step_position 0 ⟨none,.right⟩ w c t
  by_cases ht : t=0 <;>
    simpa [cellResult,NativeIO.setLabel,ht,NativeMicrocode.direction,Transpose.Dir.shift] using h

theorem cell_cells (w : List Bool) (c : State) (t : Fin 2) (z : ℤ) :
    cells (cellResult w c) t z=cells c t z := by
  change cells (NativeIO.step (action 0 ⟨none,.right⟩) w c) t z=_
  simpa only [Option.getD_none,ite_self] using step_cells 0 ⟨none,.right⟩ w c t z

def emitted (w : List Bool) (c : State) : ℕ → State
  | 0 => c
  | n+1 => cellResult w (emitted w c n)

theorem emitted_position (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) :
    (emitted w c n).work.pos t=c.work.pos t+if t=0 then n else 0 := by
  induction n with
  | zero => simp [emitted]
  | succ n ih =>
    rw [emitted,cell_position,ih]
    by_cases h : t=0 <;> simp [h]
    omega

theorem emitted_cells (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) (z : ℤ) :
    cells (emitted w c n) t z=cells c t z := by
  induction n with
  | zero => rfl
  | succ n ih => exact (cell_cells w _ t z).trans ih

theorem emitted_input (w : List Bool) (c : State) (n : ℕ) : (emitted w c n).inputPos=c.inputPos := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem emitted_output (w : List Bool) (c : State) (n : ℕ) :
    (emitted w c n).outRev=
      ((List.range n).map (fun j : ℕ => bit (cells c 0 (c.work.pos 0+j)))).reverse++c.outRev := by
  induction n with
  | zero => simp [emitted]
  | succ n ih =>
    have hr : bit ((emitted w c n).work.core.tapes 0).head=
        bit (cells c 0 (c.work.pos 0+n)) := by
      rw [← AbsoluteTape.scanned _ ((emitted w c n).work.pos 0)]
      change bit (cells (emitted w c n) 0 ((emitted w c n).work.pos 0))=_
      rw [emitted_position,ite_eq_left rfl,emitted_cells]
    change bit ((emitted w c n).work.core.tapes 0).head::(emitted w c n).outRev=_
    rw [hr,ih,List.range_succ,List.map_append,List.reverse_append]
    simp

def schedule (i : ℕ) : NativeIO.Program (Fin 2) Mode := cellSchedule (i%3)

theorem schedule_exact (w : List Bool) (c : State) (n : ℕ) :
    trajectory schedule w c (3*n)=emitted w c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3*n+3 by omega,trajectory_add,ih,
      trajectory_congr (fun i => schedule (3*n+i)) cellSchedule w _ 3 (by
        intro i hi
        simp only [schedule,show (3*n+i)%3=i by omega]),cell_exact]
    rfl

end TransposeFollowup.ScheduledRawOutput
