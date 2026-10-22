import TransposeFollowup.AbsoluteTape
import FixedTapeCompiler.Microcode

/-! Compile a fixed finite microinstruction program to the original TM.
Each active microinstruction costs exactly one native transition. Absolute
positions are tracked separately from the relative tape representation.
The compiler does not supply an input loader or an arithmetic algorithm. -/

namespace TransposeFollowup.NativeMicrocode

open FixedTapeCompiler
open CopyMachine (Sym)
open Microcode (Move Action Instruction Program ActualConfig)

set_option autoImplicit false

/-- Totalize one step of the unchanged original machine. This is definitionally
equal to `Transpose.Tape.Impl.next`; the bridge module supplies that vocabulary. -/
def totalStep (M : Transpose.TM) (w : List Bool) (c : Transpose.Config M) : Transpose.Config M :=
  (Transpose.step M w c).getD c

def symbolCode : Sym Bool → Fin 5
  | .blank => 0
  | .start => 1
  | .stop => 2
  | .data false => 3
  | .data true => 4

def symbolDecode (x : Fin 5) : Sym Bool :=
  match x.val with
  | 0 => .blank
  | 1 => .start
  | 2 => .stop
  | 3 => .data false
  | _ => .data true

@[simp] theorem symbolDecode_code (x : Sym Bool) : symbolDecode (symbolCode x) = x := by
  cases x with
  | blank => rfl
  | start => rfl
  | stop => rfl
  | data b => cases b <;> rfl

@[simp] theorem symbolCode_decode (x : Fin 5) : symbolCode (symbolDecode x) = x := by
  fin_cases x <;> rfl

def direction : Move → Transpose.Dir
  | .stay => .stay
  | .left => .left
  | .right => .right

theorem action_cells (a : Action) (t : Turing.Tape (Sym Bool)) (p z : ℤ) :
    AbsoluteTape.cells (a.actual t) ((direction a.move).shift p) z =
      if z = p then a.write.getD t.head else AbsoluteTape.cells t p z := by
  rcases a with ⟨w, d⟩
  have h : (match d with
      | .stay => (match w with | none => t | some x => t.write x)
      | .left => (match w with | none => t | some x => t.write x).move .left
      | .right => (match w with | none => t | some x => t.write x).move .right) =
      AbsoluteTape.move (direction d) (match w with | none => t | some x => t.write x) := by
    cases d <;> rfl
  change AbsoluteTape.cells _ ((direction d).shift p) z = _
  rw [show (Action.actual ⟨w, d⟩ t) = _ from h, AbsoluteTape.move_cells]
  cases w with
  | none =>
    by_cases hz : z = p
    · subst z; simp [AbsoluteTape.scanned]
    · simp [hz]
  | some x => exact AbsoluteTape.write_cells x t p z

variable {T L : Type*} {k q : ℕ}

/-- These are fixed finite enumerations, independent of the input size. -/
structure Encoding (T L : Type*) (k q : ℕ) where
  port : T ≃ Fin k
  label : L ≃ Fin (q + 1)

def delta (e : Encoding T L k q) (p : Program T L)
    (s : Fin (q + 1)) (_ : Option Bool) (scanned : Fin k → Fin 5) :
    Option (Fin (q + 1) × Transpose.Dir ×
      (Fin k → Fin 5 × Transpose.Dir) × Option Bool) :=
  match p (e.label.symm s) with
  | .read t next => some
      (e.label (next (symbolDecode (scanned (e.port t)))), .stay,
        fun i => (scanned i, .stay), none)
  | .act actions next => some
      (e.label next, .stay,
        fun i => ((actions (e.port.symm i)).write.map symbolCode |>.getD (scanned i),
          direction (actions (e.port.symm i)).move), none)
  | .jump next => some (e.label next, .stay, fun i => (scanned i, .stay), none)
  | .halt | .reject => none

abbrev machine (e : Encoding T L k q) (p : Program T L) : Transpose.TM where
  k := k
  g := 4
  q := q
  δ := delta e p

structure Config (T L : Type*) where
  core : ActualConfig T L
  pos : T → ℤ

def step (p : Program T L) (c : Config T L) : Config T L where
  core := Microcode.actualStep p c.core
  pos := match p c.core.pc with
    | .act actions _ => fun t => (direction (actions t).move).shift (c.pos t)
    | _ => c.pos

def Config.denote (e : Encoding T L k q) (p : Program T L) (inputPos : ℤ)
    (outRev : List Bool) (c : Config T L) : Transpose.Config (machine e p) where
  state := e.label c.core.pc
  inPos := inputPos
  work := fun i z => symbolCode (AbsoluteTape.cells (c.core.tapes (e.port.symm i))
    (c.pos (e.port.symm i)) z)
  workPos := fun i => c.pos (e.port.symm i)
  outRev := outRev

theorem step_denote_core (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (inputPos : ℤ) (outRev : List Bool) (c : Config T L) :
    NativeMicrocode.totalStep (machine e p) w (c.denote e p inputPos outRev) =
      (step p c).denote e p inputPos outRev := by
  cases hp : p c.core.pc with
  | act actions next =>
    simp only [NativeMicrocode.totalStep, Transpose.step, Config.denote, machine, delta,
      Equiv.symm_apply_apply, hp, AbsoluteTape.scanned, Option.getD_some,
      step, Microcode.actualStep]
    congr 1
    funext i z
    rw [action_cells]
    split_ifs with hz
    · cases (actions (e.port.symm i)).write <;> simp [hz]
    · simp [hz]
  | halt | reject =>
    simp [NativeMicrocode.totalStep, Transpose.step, Config.denote, machine, delta,
      hp, step, Microcode.actualStep]
  | _ =>
    simp only [NativeMicrocode.totalStep, Transpose.step, Config.denote, machine, delta,
      Equiv.symm_apply_apply, hp, AbsoluteTape.scanned, symbolDecode_code,
      Option.getD_some, step, Microcode.actualStep]
    congr 1
    funext i z
    split_ifs with hz
    · subst z; simp [AbsoluteTape.scanned]
    · simp [hz]

end TransposeFollowup.NativeMicrocode
