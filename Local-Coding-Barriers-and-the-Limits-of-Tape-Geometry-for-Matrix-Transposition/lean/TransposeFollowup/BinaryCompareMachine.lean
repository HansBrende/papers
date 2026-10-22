import TransposeFollowup.NativeZipper
import TransposeFollowup.BinaryCompareData

/-! Fixed two-tape binary comparator. Each forward digit takes two reads
and one simultaneous head move. Backward scanning restores both heads.
There are no word-sized integers in the finite control. -/

namespace TransposeFollowup.BinaryCompare

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open NativeZipper (Config run)
set_option autoImplicit false

inductive Label
  | scan (r : Result)
  | second (r : Result) (a : Bool)
  | advance (r : Result)
  | ending (r : Result)
  | back (r : Result)
  | backMove (r : Result)
  | finish (r : Result)
  | done (r : Result)
  | reject
  deriving DecidableEq, Fintype

def program : Microcode.Program (Fin 2) Label
  | .scan r => .read 0 (fun s => match s with
      | .data a => .second r a | .stop => .ending r | _ => .reject)
  | .second r a => .read 1 (fun s => match s with
      | .data b => .advance (update r a b) | _ => .reject)
  | .advance r => .act (fun _ => ⟨none, .right⟩) (.scan r)
  | .ending r => .read 1 (fun s => match s with
      | .stop => .back r | _ => .reject)
  | .back r => .read 0 (fun s => match s with
      | .start => .finish r | _ => .backMove r)
  | .backMove r => .act (fun _ => ⟨none, .left⟩) (.back r)
  | .finish r => .act (fun _ => ⟨none, .right⟩) (.done r)
  | .done _ => .halt
  | .reject => .reject

def bank (a b : Tape Bool) : Fin 2 → Tape Bool := fun i => if i = 0 then a else b

def cfg (pc : Label) (a b : Tape Bool) (pos : Fin 2 → ℤ) : Config (Fin 2) Label :=
  ⟨⟨pc, bank a b⟩, pos⟩

abbrev shifted := @NativeZipper.shiftPositions (Fin 2)

/-- A named execution wrapper keeps recursive semantics opaque to rewrites. -/
def execute (n : ℕ) (c : Config (Fin 2) Label) : Config (Fin 2) Label :=
  run program n c

theorem execute_add (n m : ℕ) (c : Config (Fin 2) Label) :
    execute (n + m) c = execute m (execute n c) := NativeZipper.run_add program n m c

@[simp] theorem shifted_zero (pos : Fin 2 → ℤ) : shifted pos 0 = pos := by
  exact NativeZipper.shiftPositions_zero pos

theorem shifted_shifted (pos : Fin 2 → ℤ) (a b : ℤ) :
    shifted (shifted pos a) b = shifted pos (a + b) := by
  exact NativeZipper.shiftPositions_add pos a b

theorem scan_digit (r : Result) (a b : Bool) (la lb ra rb : List (Sym Bool))
    (pos : Fin 2 → ℤ) :
    execute 3 (cfg (.scan r) ⟨la, .data a :: ra⟩ ⟨lb, .data b :: rb⟩ pos) =
      cfg (.scan (update r a b)) ⟨.data a :: la, ra⟩ ⟨.data b :: lb, rb⟩
        (shifted pos 1) := by
  simp only [execute, run, OperationalTrace.run, NativeZipper.step, Microcode.step, program,
    cfg, bank, Microcode.Action.apply, Tape.read, List.headD_cons, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false,
    NativeMicrocode.direction, Transpose.Dir.shift]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem at_ends (r : Result) (la lb : List (Sym Bool)) (pos : Fin 2 → ℤ) :
    execute 2 (cfg (.scan r) ⟨la, [.stop]⟩ ⟨lb, [.stop]⟩ pos) =
      cfg (.back r) ⟨la, [.stop]⟩ ⟨lb, [.stop]⟩ pos := by
  rfl

theorem back_pair (r : Result) (a b : Tape Bool) (pos : Fin 2 → ℤ)
    (h : a.read ≠ .start) :
    execute 2 (cfg (.back r) a b pos) =
      cfg (.back r) a.moveLeft b.moveLeft (shifted pos (-1)) := by
  have hm : (match a.read with | .start => Label.finish r | _ => .backMove r) =
      .backMove r := by cases hs : a.read <;> simp_all
  have hs : NativeZipper.step program (cfg (.back r) a b pos) =
      cfg (.backMove r) a b pos := by
    change cfg (match a.read with | .start => .finish r | _ => .backMove r) a b pos = _
    rw [hm]
  change NativeZipper.step program (NativeZipper.step program _) = _
  rw [hs]
  simp only [NativeZipper.step, Microcode.step, program,
    cfg, bank, Microcode.Action.apply, NativeMicrocode.direction,
    Transpose.Dir.shift]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem return_pair (r : Result) (ra rb : List (Sym Bool)) (pos : Fin 2 → ℤ) :
    execute 2 (cfg (.back r) ⟨[], .start :: ra⟩ ⟨[], .start :: rb⟩ pos) =
      cfg (.done r) ⟨[.start], ra⟩ ⟨[.start], rb⟩ (shifted pos 1) := by
  simp only [execute, run, OperationalTrace.run, NativeZipper.step, Microcode.step, program,
    cfg, bank, Microcode.Action.apply, Tape.read, List.headD_cons, ite_true,
    NativeMicrocode.direction, Transpose.Dir.shift]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem fixed_resources : Fintype.card (Fin 2) = 2 ∧
    Fintype.card (Sym Bool) = 5 ∧ Fintype.card Label = 28 := by decide +kernel

end TransposeFollowup.BinaryCompare
