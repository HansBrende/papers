import TransposeFollowup.NativeZipper
import TransposeFollowup.BinaryCarryData

/-! A fixed three-tape controller for the shared carry recurrence.
Two operand tapes are read without modification; the third receives the
fixed-width result. Every head returns by an explicit synchronous rewind. -/

namespace TransposeFollowup.BinaryCarry

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open NativeZipper (Config run)
set_option autoImplicit false

inductive Label
  | scan (sub c : Bool)
  | second (sub c a : Bool)
  | emit (sub c digit : Bool)
  | ending (c : Bool)
  | seal (c : Bool)
  | back (c : Bool)
  | backMove (c : Bool)
  | finish (c : Bool)
  | done (c : Bool)
  | reject
  deriving DecidableEq, Fintype

def program : Microcode.Program (Fin 3) Label
  | .scan sub c => .read 0 (fun s => match s with
      | .data a => .second sub c a | .stop => .ending c | _ => .reject)
  | .second sub c a => .read 1 (fun s => match s with
      | .data b => .emit sub (carry c a (operandBit sub b)) (digit c a (operandBit sub b))
      | _ => .reject)
  | .emit sub c v => .act (fun t => ⟨if t = 2 then some (.data v) else none, .right⟩)
      (.scan sub c)
  | .ending c => .read 1 (fun s => match s with | .stop => .seal c | _ => .reject)
  | .seal c => .act (fun t => ⟨if t = 2 then some .stop else none, .stay⟩) (.back c)
  | .back c => .read 0 (fun s => match s with | .start => .finish c | _ => .backMove c)
  | .backMove c => .act (fun _ => ⟨none, .left⟩) (.back c)
  | .finish c => .act (fun _ => ⟨none, .right⟩) (.done c)
  | .done _ => .halt
  | .reject => .reject

def bank (a b out : Tape Bool) : Fin 3 → Tape Bool :=
  fun t => if t = 0 then a else if t = 1 then b else out

def cfg (pc : Label) (a b out : Tape Bool) (pos : Fin 3 → ℤ) : Config (Fin 3) Label :=
  ⟨⟨pc, bank a b out⟩, pos⟩

abbrev shifted := @NativeZipper.shiftPositions (Fin 3)

def execute (n : ℕ) (c : Config (Fin 3) Label) : Config (Fin 3) Label := run program n c

theorem execute_add (n m : ℕ) (c : Config (Fin 3) Label) :
    execute (n + m) c = execute m (execute n c) := NativeZipper.run_add program n m c

theorem scan_digit (sub c a b : Bool) (la lb lo ra rb : List (Sym Bool))
    (pos : Fin 3 → ℤ) :
    execute 3 (cfg (.scan sub c) ⟨la, .data a :: ra⟩ ⟨lb, .data b :: rb⟩ ⟨lo, []⟩ pos) =
      cfg (.scan sub (carry c a (operandBit sub b)))
        ⟨.data a :: la, ra⟩ ⟨.data b :: lb, rb⟩
        ⟨.data (digit c a (operandBit sub b)) :: lo, []⟩ (shifted pos 1) := by
  simp only [execute, run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, bank, Microcode.Action.apply, Tape.read, List.headD_cons, ite_true,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, NativeMicrocode.direction, Transpose.Dir.shift]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem at_ends (sub c : Bool) (la lb lo : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    execute 3 (cfg (.scan sub c) ⟨la, [.stop]⟩ ⟨lb, [.stop]⟩ ⟨lo, []⟩ pos) =
      cfg (.back c) ⟨la, [.stop]⟩ ⟨lb, [.stop]⟩ ⟨lo, [.stop]⟩ pos := by
  simp only [execute, run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, bank, Microcode.Action.apply, Tape.read, List.headD_cons, ite_true,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, NativeMicrocode.direction, Transpose.Dir.shift]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem back_three (c : Bool) (a b out : Tape Bool) (pos : Fin 3 → ℤ)
    (h : a.read ≠ .start) :
    execute 2 (cfg (.back c) a b out pos) =
      cfg (.back c) a.moveLeft b.moveLeft out.moveLeft (shifted pos (-1)) := by
  have hm : (match a.read with | .start => Label.finish c | _ => .backMove c) =
      .backMove c := by cases hs : a.read <;> simp_all
  have hs : NativeZipper.step program (cfg (.back c) a b out pos) =
      cfg (.backMove c) a b out pos := by
    change cfg (match a.read with | .start => .finish c | _ => .backMove c) a b out pos = _
    rw [hm]
  change NativeZipper.step program (NativeZipper.step program _) = _
  rw [hs]
  simp only [NativeZipper.step, Microcode.step, program, cfg, bank, Microcode.Action.apply,
    NativeMicrocode.direction, Transpose.Dir.shift]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem return_three (c : Bool) (ra rb ro : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    execute 2 (cfg (.back c) ⟨[], .start :: ra⟩ ⟨[], .start :: rb⟩ ⟨[], .start :: ro⟩ pos) =
      cfg (.done c) ⟨[.start], ra⟩ ⟨[.start], rb⟩ ⟨[.start], ro⟩ (shifted pos 1) := by
  simp only [execute, run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, bank, Microcode.Action.apply, Tape.read, List.headD_cons, ite_true,
    NativeMicrocode.direction, Transpose.Dir.shift]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem fixed_resources : Fintype.card (Fin 3) = 3 ∧
    Fintype.card (Sym Bool) = 5 ∧ Fintype.card Label = 33 := by decide +kernel

end TransposeFollowup.BinaryCarry
