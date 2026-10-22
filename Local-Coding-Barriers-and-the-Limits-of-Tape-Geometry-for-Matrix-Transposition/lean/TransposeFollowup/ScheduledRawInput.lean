import TransposeFollowup.ScheduledTapeAction
import TransposeFollowup.MaskedStrideCell
import Transpose.Tape.Encode

/-! Exact-length raw input loading: read input, write/advance bank, advance
input. The input symbol is read at runtime and is not part of the schedule. -/
namespace TransposeFollowup.ScheduledRawInput
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State)
open CopyMachine (Sym)
set_option autoImplicit false

def inputBit (w : List Bool) (p : ℤ) : Bool := (Transpose.readInput w p).getD false

theorem inputBit_get (w : List Bool) (j : ℕ) (hj : j < w.length) : inputBit w j=w[j] := by
  simp only [inputBit,Transpose.Tape.Impl.readInput_natCast,Transpose.Tape.Impl.nth_eq_getElem?,
    List.getElem?_eq_getElem hj,Option.getD_some]

def cellSchedule : ℕ → NativeIO.Program (Fin 2) Mode
  | 0 => fun _ => .readInput (fun b => (b.getD false,false))
  | 1 => fun m => action 0 ⟨some (.data m.1),.right⟩ m
  | _+2 => fun _ => .moveInput .right (false,false)

def cellResult (w : List Bool) (c : State) : State :=
  {NativeIO.setLabel (NativeIO.step (action 0 ⟨some (.data (inputBit w c.inputPos)),.right⟩) w c)
      (false,false) with inputPos:=c.inputPos+1}

theorem cell_exact (w : List Bool) (c : State) : trajectory cellSchedule w c 3=cellResult w c := rfl

theorem cell_active (i : ℕ) (c : State) : NativeIO.Active (cellSchedule i) c := by
  cases i with
  | zero => trivial
  | succ i => cases i with
    | zero => exact ScheduledTapeAction.active _ _ _
    | succ _ => trivial

theorem cell_position (w : List Bool) (c : State) (t : Fin 2) :
    (cellResult w c).work.pos t=c.work.pos t+if t=0 then 1 else 0 := by
  have h := step_position 0 ⟨some (.data (inputBit w c.inputPos)),.right⟩ w c t
  by_cases ht : t=0 <;>
    simpa [cellResult,NativeIO.setLabel,ht,NativeMicrocode.direction,Transpose.Dir.shift] using h

theorem cell_cells (w : List Bool) (c : State) (t : Fin 2) (z : ℤ) :
    cells (cellResult w c) t z=
      if t=0 ∧ z=c.work.pos t then .data (inputBit w c.inputPos) else cells c t z := by
  exact step_cells 0 ⟨some (.data (inputBit w c.inputPos)),.right⟩ w c t z

def loaded (w : List Bool) (c : State) : ℕ → State
  | 0 => c
  | n+1 => cellResult w (loaded w c n)

theorem loaded_io (w : List Bool) (c : State) (n : ℕ) :
    (loaded w c n).inputPos=c.inputPos+n ∧ (loaded w c n).outRev=c.outRev := by
  induction n with
  | zero => simp [loaded]
  | succ n ih =>
    constructor
    · change (loaded w c n).inputPos+1=_
      rw [ih.1]
      push_cast
      omega
    · exact ih.2

theorem loaded_position (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) :
    (loaded w c n).work.pos t=c.work.pos t+if t=0 then n else 0 := by
  induction n with
  | zero => simp [loaded]
  | succ n ih =>
    rw [loaded,cell_position,ih]
    by_cases h : t=0 <;> simp [h]
    omega

theorem loaded_written (w : List Bool) (c : State) (n j : ℕ) (hj : j < n) :
    cells (loaded w c n) 0 (c.work.pos 0+j)=.data (inputBit w (c.inputPos+j)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [loaded,cell_cells]
    by_cases h : j=n
    · subst j
      have he : c.work.pos 0+(n : ℕ)=(loaded w c n).work.pos 0 := by
        simpa using (loaded_position w c n 0).symm
      rw [ite_eq_left ⟨rfl,he⟩,(loaded_io w c n).1]
    · have he : ¬((0 : Fin 2)=0 ∧ c.work.pos 0+(j : ℕ)=(loaded w c n).work.pos 0) := by
        rw [loaded_position]
        simp only [ite_true,true_and]
        omega
      rw [ite_eq_right he]
      exact ih (by omega)

theorem loaded_outside (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) (z : ℤ)
    (hz : t≠0 ∨ z<c.work.pos t ∨ c.work.pos t+n ≤ z) :
    cells (loaded w c n) t z=cells c t z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [loaded,cell_cells]
    have he : ¬(t=0 ∧ z=(loaded w c n).work.pos t) := by
      rw [loaded_position]
      by_cases ht : t=0
      · simp only [ht,ite_true,true_and]
        rcases hz with hz | hz | hz <;> simp_all <;> omega
      · simp [ht]
    rw [ite_eq_right he]
    exact ih (by rcases hz with hz | hz | hz; exact Or.inl hz; exact Or.inr (Or.inl hz); exact Or.inr (Or.inr (by omega)))

def schedule (i : ℕ) : NativeIO.Program (Fin 2) Mode := cellSchedule (i%3)

theorem schedule_exact (w : List Bool) (c : State) (n : ℕ) :
    trajectory schedule w c (3*n)=loaded w c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3*n+3 by omega,trajectory_add,ih,
      trajectory_congr (fun i => schedule (3*n+i)) cellSchedule w _ 3 (by
        intro i hi
        simp only [schedule,show (3*n+i)%3=i by omega]),cell_exact]
    rfl

end TransposeFollowup.ScheduledRawInput
