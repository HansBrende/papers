import Mathlib.Data.List.Basic
import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Tactic

/-! A concrete deterministic two-tape machine. Each transition inspects
only finite control and scanned symbols, writes at most one symbol per
tape, and moves each head at most one cell. Lists are the mathematical
zipper representation of a tape, not unit-cost list-processing instructions.
The input alphabet is finite whenever α is finite; α=Bool suffices here.

This file establishes one actual tape primitive. It does NOT yet supply
the digit-routing, affine, row-split or recursive compiler refinements. -/
namespace FixedTapeCompiler.CopyMachine

inductive Sym (α : Type*)
  | blank | start | stop | data (a : α)
  deriving DecidableEq, Fintype

instance : Inhabited (Sym α) := ⟨.blank⟩

structure Tape (α : Type*) where
  left : List (Sym α)
  right : List (Sym α)
  deriving DecidableEq

variable {α : Type*}

def Tape.read (t : Tape α) : Sym α := t.right.headD .blank
def Tape.write (t : Tape α) (a : Sym α) : Tape α :=
  ⟨t.left, a :: t.right.tail⟩
def Tape.moveRight (t : Tape α) : Tape α :=
  ⟨t.read :: t.left, t.right.tail⟩
def Tape.moveLeft (t : Tape α) : Tape α :=
  ⟨t.left.tail, t.left.headD .blank :: t.right⟩

inductive Phase | copy | back | done | reject
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.copy, .back, .done, .reject}
  complete := by intro x; cases x <;> simp

structure Config (α : Type*) where
  phase : Phase
  source : Tape α
  target : Tape α
  deriving DecidableEq

def step (c : Config α) : Config α :=
  match c.phase with
  | .done | .reject => c
  | .copy =>
      match c.source.read with
      | .data a => ⟨.copy, c.source.moveRight,
          (c.target.write (.data a)).moveRight⟩
      | .stop => ⟨.back, c.source, c.target.write .stop⟩
      | _ => ⟨.reject, c.source, c.target⟩
  | .back =>
      match c.source.read with
      | .start => ⟨.done, c.source.moveRight, c.target.moveRight⟩
      | _ => ⟨.back, c.source.moveLeft, c.target.moveLeft⟩

def run : ℕ → Config α → Config α
  | 0, c => c
  | n+1, c => run n (step c)

theorem run_add (n k : ℕ) (c : Config α) :
    run (n+k) c = run k (run n c) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    simp only [Nat.succ_add, run, ih]

def symbols (xs : List α) : List (Sym α) := xs.map Sym.data

def initial (xs : List α) : Config α :=
  ⟨.copy, ⟨[.start], symbols xs ++ [.stop]⟩, ⟨[.start], []⟩⟩

def finished (xs : List α) : Config α :=
  ⟨.done, ⟨[.start], symbols xs ++ [.stop]⟩,
    ⟨[.start], symbols xs ++ [.stop]⟩⟩

theorem forward_exact (xs : List α) (pre : List (Sym α)) :
    run xs.length
      ⟨.copy, ⟨pre, symbols xs ++ [.stop]⟩, ⟨pre, []⟩⟩ =
    ⟨.copy, ⟨(symbols xs).reverse ++ pre, [.stop]⟩,
      ⟨(symbols xs).reverse ++ pre, []⟩⟩ := by
  induction xs generalizing pre with
  | nil => simp [symbols, run]
  | cons a xs ih =>
    simpa [symbols, run, step, Tape.read, Tape.write, Tape.moveRight,
      List.reverse_cons, List.append_assoc] using ih (.data a :: pre)

/-- Starting with identical tapes, rewind both to the start marker.
`pre` is in reverse physical order, as required by the tape zipper. -/
theorem rewind_to_start (pre : List α) (suffix : List (Sym α))
    (h : suffix.headD .blank ≠ .start) :
    run (pre.length+1)
      ⟨.back, ⟨symbols pre ++ [.start], suffix⟩,
        ⟨symbols pre ++ [.start], suffix⟩⟩ =
    ⟨.back, ⟨[], .start :: (symbols pre.reverse ++ suffix)⟩,
      ⟨[], .start :: (symbols pre.reverse ++ suffix)⟩⟩ := by
  induction pre generalizing suffix with
  | nil =>
    cases suffix with
    | nil => simp [symbols, run, step, Tape.read, Tape.moveLeft]
    | cons a as =>
      cases a <;> simp_all [symbols, run, step, Tape.read, Tape.moveLeft]
  | cons a ps ih =>
    have hi := ih (.data a :: suffix) (by simp)
    have hs : step
        (⟨.back, ⟨symbols (a::ps) ++ [.start], suffix⟩,
          ⟨symbols (a::ps) ++ [.start], suffix⟩⟩ : Config α) =
        ⟨.back, ⟨symbols ps ++ [.start], .data a :: suffix⟩,
          ⟨symbols ps ++ [.start], .data a :: suffix⟩⟩ := by
      cases suffix with
      | nil => simp [symbols, step, Tape.read, Tape.moveLeft]
      | cons x xs =>
        cases x <;> simp_all [symbols, step, Tape.read, Tape.moveLeft]
    change run (ps.length+1) (step
      ⟨.back, ⟨symbols (a::ps) ++ [.start], suffix⟩,
        ⟨symbols (a::ps) ++ [.start], suffix⟩⟩) = _
    rw [hs]
    simpa [symbols, List.reverse_cons, List.map_append, List.append_assoc] using hi

/-- Output after an explicit linear number of unit transitions, with both
heads restored and source unchanged. This is also a runtime upper bound. -/
theorem copy_exact (xs : List α) :
    run (2*xs.length+3) (initial xs) = finished xs := by
  have hf := forward_exact xs [Sym.start]
  have hb := rewind_to_start xs.reverse [Sym.stop] (by simp)
  have hs : step
      (⟨.copy, ⟨(symbols xs).reverse ++ [.start], [.stop]⟩,
        ⟨(symbols xs).reverse ++ [.start], []⟩⟩ : Config α) =
      ⟨.back, ⟨(symbols xs).reverse ++ [.start], [.stop]⟩,
        ⟨(symbols xs).reverse ++ [.start], [.stop]⟩⟩ := by
    rfl
  rw [show 2*xs.length+3 = xs.length + (1 + ((xs.length+1)+1)) by omega]
  rw [run_add]
  change run (1 + ((xs.length+1)+1))
    (run xs.length ⟨.copy, ⟨[.start], symbols xs ++ [.stop]⟩,
      ⟨[.start], []⟩⟩) = _
  rw [hf, run_add]
  change run ((xs.length+1)+1)
    ⟨.back, ⟨(symbols xs).reverse ++ [.start], [.stop]⟩,
      ⟨(symbols xs).reverse ++ [.start], [.stop]⟩⟩ = _
  rw [run_add]
  have hb' : run (xs.length+1)
      (⟨.back, ⟨(symbols xs).reverse ++ [.start], [.stop]⟩,
        ⟨(symbols xs).reverse ++ [.start], [.stop]⟩⟩ : Config α) =
      ⟨.back, ⟨[], .start :: (symbols xs ++ [.stop])⟩,
        ⟨[], .start :: (symbols xs ++ [.stop])⟩⟩ := by
    simpa [symbols, List.map_reverse] using hb
  rw [hb']
  rfl

/-! Refinement into mathlib's two-sided, infinite-blank tape model.
The concrete transition below is a standard two-tape transition, rather
than a list operation accepted by convention. -/

def Tape.denote (t : Tape α) : Turing.Tape (Sym α) :=
  Turing.Tape.mk₂ t.left t.right

@[simp] theorem denote_read (t : Tape α) : t.denote.head = t.read := by
  cases t with
  | mk l r => cases r <;> rfl

@[simp] theorem denote_write (t : Tape α) (a : Sym α) :
    (t.write a).denote = t.denote.write a := by
  simp [Tape.denote, Tape.write, Turing.Tape.mk₂, Turing.Tape.write_mk']

@[simp] theorem denote_right (t : Tape α) :
    t.moveRight.denote = t.denote.move .right := by
  simp [Tape.denote, Tape.moveRight, Tape.read, Turing.Tape.mk₂,
    Turing.Tape.move_right_mk']
  cases t with
  | mk l r => cases r <;> rfl

@[simp] theorem denote_left (t : Tape α) :
    t.moveLeft.denote = t.denote.move .left := by
  simp [Tape.denote, Tape.moveLeft, Turing.Tape.mk₂,
    Turing.Tape.move_left_mk']
  cases t with
  | mk l r => cases l <;> rfl

structure ConcreteConfig (α : Type*) where
  phase : Phase
  source : Turing.Tape (Sym α)
  target : Turing.Tape (Sym α)

def Config.denote (c : Config α) : ConcreteConfig α :=
  ⟨c.phase, c.source.denote, c.target.denote⟩

def concreteStep (c : ConcreteConfig α) : ConcreteConfig α :=
  match c.phase with
  | .done | .reject => c
  | .copy =>
      match c.source.head with
      | .data a => ⟨.copy, c.source.move .right,
          (c.target.write (.data a)).move .right⟩
      | .stop => ⟨.back, c.source, c.target.write .stop⟩
      | _ => ⟨.reject, c.source, c.target⟩
  | .back =>
      match c.source.head with
      | .start => ⟨.done, c.source.move .right, c.target.move .right⟩
      | _ => ⟨.back, c.source.move .left, c.target.move .left⟩

theorem step_refines (c : Config α) :
    (step c).denote = concreteStep c.denote := by
  cases c with
  | mk phase source target =>
    cases phase <;> cases h : source.read <;>
      simp [step, Config.denote, concreteStep, h]

def concreteRun : ℕ → ConcreteConfig α → ConcreteConfig α
  | 0, c => c
  | n+1, c => concreteRun n (concreteStep c)

theorem run_refines (n : ℕ) (c : Config α) :
    (run n c).denote = concreteRun n c.denote := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run, concreteRun, ih, step_refines]

/-- Correctness and a linear physical-step bound on the standard tape model.
For α=Bool this is one fixed two-tape, five-symbol, four-state machine. -/
theorem copy_actual_tapes (xs : List α) :
    concreteRun (2*xs.length+3) (initial xs).denote = (finished xs).denote := by
  rw [← run_refines, copy_exact]

theorem fixed_resources :
    Fintype.card (Sym Bool) = 5 ∧ Fintype.card Phase = 4 := by decide

end FixedTapeCompiler.CopyMachine
