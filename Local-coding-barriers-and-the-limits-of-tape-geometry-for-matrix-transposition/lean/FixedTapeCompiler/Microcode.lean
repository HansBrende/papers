import FixedTapeCompiler.CopyMachine
import FixedTapeCompiler.OperationalTrace

/-! Finite microinstructions, matching affine_machine.py's runtime model.
The type of tape indices and program labels must be finite for a machine
instance. No payload, coordinate, or growing integer resides in control.
Zipper semantics are refined to actual infinite tapes, step for step. -/
namespace FixedTapeCompiler.Microcode
open CopyMachine (Sym Tape symbols)

inductive Move | stay | left | right
  deriving DecidableEq

instance : Fintype Move where
  elems := {.stay,.left,.right}
  complete := by intro x; cases x <;> simp

structure Action where
  write : Option (Sym Bool) := none
  move : Move := .stay
  deriving DecidableEq, Fintype

def Action.apply (a : Action) (t : Tape Bool) : Tape Bool :=
  let u := match a.write with | none => t | some x => t.write x
  match a.move with | .stay => u | .left => u.moveLeft | .right => u.moveRight

def Action.actual (a : Action) (t : Turing.Tape (Sym Bool)) : Turing.Tape (Sym Bool) :=
  let u := match a.write with | none => t | some x => t.write x
  match a.move with | .stay => u | .left => u.move .left | .right => u.move .right

theorem Action.refines (a : Action) (t : Tape Bool) :
    (a.apply t).denote = a.actual t.denote := by
  rcases a with ⟨w,m⟩
  cases w <;> cases m <;> simp [Action.apply,Action.actual]

inductive Instruction (T L : Type*)
  | read (tape : T) (next : Sym Bool → L)
  | act (actions : T → Action) (next : L)
  | jump (next : L)
  | halt
  | reject

abbrev Program (T L : Type*) := L → Instruction T L

structure Config (T L : Type*) where
  pc : L
  tapes : T → Tape Bool

structure ActualConfig (T L : Type*) where
  pc : L
  tapes : T → Turing.Tape (Sym Bool)

variable {T L : Type*}

def step (p : Program T L) (c : Config T L) : Config T L :=
  match p c.pc with
  | .read t next => ⟨next (c.tapes t).read,c.tapes⟩
  | .act actions next => ⟨next,fun t => (actions t).apply (c.tapes t)⟩
  | .jump next => ⟨next,c.tapes⟩
  | .halt | .reject => c

def actualStep (p : Program T L) (c : ActualConfig T L) : ActualConfig T L :=
  match p c.pc with
  | .read t next => ⟨next (c.tapes t).head,c.tapes⟩
  | .act actions next => ⟨next,fun t => (actions t).actual (c.tapes t)⟩
  | .jump next => ⟨next,c.tapes⟩
  | .halt | .reject => c

def Config.denote (c : Config T L) : ActualConfig T L :=
  ⟨c.pc,fun t => (c.tapes t).denote⟩

theorem step_refines (p : Program T L) (c : Config T L) :
    (step p c).denote = actualStep p c.denote := by
  cases h : p c.pc <;> simp [step,actualStep,Config.denote,h]
  case act a next =>
    funext t
    exact Action.refines (a t) (c.tapes t)

abbrev run (p : Program T L) := OperationalTrace.run (step p)
abbrev actualRun (p : Program T L) := OperationalTrace.run (actualStep p)

theorem run_add (p : Program T L) (n k : ℕ) (c : Config T L) :
    run p (n+k) c = run p k (run p n c) := OperationalTrace.run_add _ _ _ _

theorem actual_run_add (p : Program T L) (n k : ℕ) (c : ActualConfig T L) :
    actualRun p (n+k) c = actualRun p k (actualRun p n c) := OperationalTrace.run_add _ _ _ _

theorem run_refines (p : Program T L) (n : ℕ) (c : Config T L) :
    (run p n c).denote = actualRun p n c.denote := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [OperationalTrace.run,ih,step_refines]

/-- The action in an instruction is chosen before the tape contents are
supplied. Therefore writes and movements cannot depend on hidden data. -/
theorem head_local (p : Program T L) (c d : ActualConfig T L)
    (hpc : c.pc = d.pc) (hh : ∀ t, (c.tapes t).head = (d.tapes t).head) :
    (actualStep p c).pc = (actualStep p d).pc := by
  cases h : p c.pc <;> simp [actualStep,← hpc,h,hh]

variable [DecidableEq T]

def single (t : T) (a : Action) : T → Action :=
  fun i => if i=t then a else ⟨none,.stay⟩

def focus (pc : L) (t : T) (word : Tape Bool) (bank : T → Tape Bool) : Config T L :=
  ⟨pc,Function.update bank t word⟩

theorem single_apply (t : T) (a : Action) (word : Tape Bool) (bank : T → Tape Bool) :
    (fun i => (single t a i).apply (Function.update bank t word i)) =
      Function.update bank t (a.apply word) := by
  funext i
  by_cases hi : i=t
  · subst i; simp [single]
  · simp [single,hi,Action.apply]

theorem at_read (p : Program T L) (pc : L) (t : T) (next : Sym Bool → L)
    (hp : p pc = .read t next) (word : Tape Bool) (bank : T → Tape Bool) :
    step p (focus pc t word bank) = focus (next word.read) t word bank := by
  simp [step,focus,hp]

theorem at_act (p : Program T L) (pc next : L) (t : T) (a : Action)
    (hp : p pc = .act (single t a) next) (word : Tape Bool) (bank : T → Tape Bool) :
    step p (focus pc t word bank) = focus next t (a.apply word) bank := by
  simp [step,focus,hp,single_apply]

theorem at_jump (p : Program T L) (pc next : L) (t : T)
    (hp : p pc = .jump next) (word : Tape Bool) (bank : T → Tape Bool) :
    step p (focus pc t word bank) = focus next t word bank := by
  simp [step,focus,hp]

omit [DecidableEq T] in
/-- A label renaming that preserves every transition also preserves exact
runtime. This supports embedding verified fragments in a larger controller. -/
theorem rename_run {J : Type*} (p : Program T L) (q : Program T J)
    (rename : L → J)
    (hs : ∀ c : Config T L, step q ⟨rename c.pc,c.tapes⟩ =
      ⟨rename (step p c).pc,(step p c).tapes⟩)
    (n : ℕ) (c : Config T L) :
    run q n ⟨rename c.pc,c.tapes⟩ = ⟨rename (run p n c).pc,(run p n c).tapes⟩ := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simpa only [OperationalTrace.run,hs] using ih (step p c)

end FixedTapeCompiler.Microcode
