import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeCountedLoop
import TransposeFollowup.NativeBuffer
import TransposeFollowup.SignedPairData

/-! Two cross-sum additions, comparison, and two scratch recycling calls.
The comparison result stays in finite labels through cleanup. All five
transfers are actual jumps; input loading remains a separate obligation. -/

namespace TransposeFollowup.SignedPair

open FixedTapeCompiler
open CopyMachine (Tape)
open BinaryCompare (Result)
set_option autoImplicit false

inductive Port | a | b | c | d | left | right
  deriving DecidableEq

instance : Fintype Port where
  elems := {.a, .b, .c, .d, .left, .right}
  complete := by intro p; cases p <;> simp

def singleBinding (t : Port) : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => t, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun u => if u = t then some 0 else none
  decode_spec := by
    intro u i
    change (if u = t then some 0 else none) = some i ↔ t = u
    fin_cases i
    by_cases h : u = t
    · subst u; simp
    · simp [h, Ne.symm h]

def leftBinding : FinitePortBinding (Fin 3) Port where
  ports := ⟨![.a, .d, .left], by decide +kernel⟩
  decode := fun u => match u with
    | .a => some 0 | .d => some 1 | .left => some 2 | _ => none
  decode_spec := by intro u i; cases u <;> fin_cases i <;> decide +kernel

def rightBinding : FinitePortBinding (Fin 3) Port where
  ports := ⟨![.c, .b, .right], by decide +kernel⟩
  decode := fun u => match u with
    | .c => some 0 | .b => some 1 | .right => some 2 | _ => none
  decode_spec := by intro u i; cases u <;> fin_cases i <;> decide +kernel

def compareBinding : FinitePortBinding (Fin 2) Port where
  ports := ⟨![.left, .right], by decide +kernel⟩
  decode := fun u => match u with | .left => some 0 | .right => some 1 | _ => none
  decode_spec := by intro u i; cases u <;> fin_cases i <;> decide +kernel

def addBinding (right : Bool) : FinitePortBinding (Fin 3) Port :=
  if right then rightBinding else leftBinding

def clearBinding (right : Bool) : FinitePortBinding (Fin 1) Port :=
  singleBinding (if right then .right else .left)

inductive Label
  | add (right : Bool) (pc : BinaryCarry.Label)
  | compare (pc : BinaryCompare.Label)
  | clear (right : Bool) (r : Result) (pc : NativeBuffer.Label)
  | done (r : Result)
  deriving DecidableEq, Fintype

def program : Microcode.Program Port Label
  | .add false (.done _) => .jump (.add true (.scan false false))
  | .add true (.done _) => .jump (.compare (.scan .equal))
  | .add right pc => (addBinding right).instruction (Label.add right) (BinaryCarry.program pc)
  | .compare (.done r) => .jump (.clear false r (.erase 2))
  | .compare pc => compareBinding.instruction Label.compare (BinaryCompare.program pc)
  | .clear false r .done => .jump (.clear true r (.erase 2))
  | .clear true r .done => .jump (.done r)
  | .clear right r pc =>
      (clearBinding right).instruction (Label.clear right r) (NativeBuffer.program pc)
  | .done _ => .halt

theorem add_code (right : Bool) (pc : BinaryCarry.Label)
    (hh : BinaryCarry.program pc ≠ .halt) (_ : BinaryCarry.program pc ≠ .reject) :
    program (.add right pc) = MicrocodeEmbedding.instruction (addBinding right).ports
      (Label.add right) (BinaryCarry.program pc) := by
  cases right <;> cases pc <;>
    simp_all [program, BinaryCarry.program, FinitePortBinding.instruction_eq]

theorem compare_code (pc : BinaryCompare.Label)
    (hh : BinaryCompare.program pc ≠ .halt) (_ : BinaryCompare.program pc ≠ .reject) :
    program (.compare pc) = MicrocodeEmbedding.instruction compareBinding.ports
      Label.compare (BinaryCompare.program pc) := by
  cases pc <;> simp_all [program, BinaryCompare.program, FinitePortBinding.instruction_eq]

theorem clear_code (right : Bool) (r : Result) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc ≠ .halt) (_ : NativeBuffer.program pc ≠ .reject) :
    program (.clear right r pc) = MicrocodeEmbedding.instruction (clearBinding right).ports
      (Label.clear right r) (NativeBuffer.program pc) := by
  cases right <;> cases pc <;>
    simp_all [program, NativeBuffer.program, FinitePortBinding.instruction_eq]

structure Bank where
  a : Tape Bool
  b : Tape Bool
  c : Tape Bool
  d : Tape Bool
  left : Tape Bool
  right : Tape Bool

def Bank.tapes (s : Bank) : Port → Tape Bool
  | .a => s.a | .b => s.b | .c => s.c | .d => s.d | .left => s.left | .right => s.right

def Bank.set (s : Bank) (t : Port) (w : Tape Bool) : Bank :=
  match t with
  | .a => {s with a := w} | .b => {s with b := w}
  | .c => {s with c := w} | .d => {s with d := w}
  | .left => {s with left := w} | .right => {s with right := w}

def cfg (pc : Label) (b : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc, fun t => (b.tapes t).denote⟩, pos⟩

def zipperCfg (pc : Label) (b : Bank) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc, b.tapes⟩, pos⟩

def frame (b : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun t => (b.tapes t).denote, pos⟩

def ready (a b c d : List Bool) : Bank where
  a := BinaryCarry.marked a
  b := BinaryCarry.marked b
  c := BinaryCarry.marked c
  d := BinaryCarry.marked d
  left := BinaryCarry.preparedOutput
  right := BinaryCarry.preparedOutput

noncomputable def nativeEncoding :=
  NativeMicrocode.initialEncoding (T := Port) (Label.add false (.scan false false))

noncomputable def nativeMachine : Transpose.TM := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k = 6 ∧ nativeMachine.g + 1 = 5 ∧
    nativeMachine.q + 1 = 157 ∧ nativeEncoding.label (.add false (.scan false false)) = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 6
    decide +kernel
  · change Fintype.card Label - 1 + 1 = 157
    decide +kernel

end TransposeFollowup.SignedPair
