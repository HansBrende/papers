import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeCountedLoop
import TransposeFollowup.NativeBuffer
import TransposeFollowup.RepeatedAddData

/-! One fixed caller for repeated addition. All five jumps between the
counter, two arithmetic calls and two buffer calls are actual instructions. -/

namespace TransposeFollowup.RepeatedAdd

open FixedTapeCompiler
open CopyMachine (Tape Sym)
set_option autoImplicit false

inductive Port | fuel | acc | factor | scratch | zero
  deriving DecidableEq

instance : Fintype Port where
  elems := {.fuel, .acc, .factor, .scratch, .zero}
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

def addBinding : FinitePortBinding (Fin 3) Port where
  ports := ⟨![.acc, .factor, .scratch], by decide +kernel⟩
  decode := fun u => match u with
    | .acc => some 0 | .factor => some 1 | .scratch => some 2 | _ => none
  decode_spec := by intro u i; cases u <;> fin_cases i <;> decide +kernel

def copyBinding : FinitePortBinding (Fin 3) Port where
  ports := ⟨![.scratch, .zero, .acc], by decide +kernel⟩
  decode := fun u => match u with
    | .scratch => some 0 | .zero => some 1 | .acc => some 2 | _ => none
  decode_spec := by intro u i; cases u <;> fin_cases i <;> decide +kernel

def arithmeticBinding (copy : Bool) : FinitePortBinding (Fin 3) Port :=
  if copy then copyBinding else addBinding

def clearBinding (scratch : Bool) : FinitePortBinding (Fin 1) Port :=
  singleBinding (if scratch then .scratch else .acc)

inductive Label
  | counter (pc : Microcode.DecrementFamily.Label)
  | arithmetic (copy : Bool) (pc : BinaryCarry.Label)
  | clear (scratch : Bool) (pc : NativeBuffer.Label)
  deriving DecidableEq, Fintype

def program : Microcode.Program Port Label
  | .counter pc => if pc = 11 then .jump (.arithmetic false (.scan false false))
      else (singleBinding .fuel).instruction Label.counter (Microcode.DecrementFamily.program pc)
  | .arithmetic copy (.done _) => .jump (.clear copy (.erase 2))
  | .arithmetic copy pc =>
      (arithmeticBinding copy).instruction (Label.arithmetic copy) (BinaryCarry.program pc)
  | .clear true .done => .jump (.counter 0)
  | .clear false .done => .jump (.arithmetic true (.scan false false))
  | .clear scratch pc =>
      (clearBinding scratch).instruction (Label.clear scratch) (NativeBuffer.program pc)

theorem counter_code (pc : Microcode.DecrementFamily.Label)
    (hh : Microcode.DecrementFamily.program pc ≠ .halt)
    (_ : Microcode.DecrementFamily.program pc ≠ .reject) :
    program (.counter pc) = MicrocodeEmbedding.instruction (singleBinding .fuel).ports
      Label.counter (Microcode.DecrementFamily.program pc) := by
  have hn : pc ≠ 11 := by
    intro h; subst pc
    exact hh rfl
  simp [program, hn, FinitePortBinding.instruction_eq]

theorem arithmetic_code (copy : Bool) (pc : BinaryCarry.Label)
    (hh : BinaryCarry.program pc ≠ .halt) (_ : BinaryCarry.program pc ≠ .reject) :
    program (.arithmetic copy pc) = MicrocodeEmbedding.instruction (arithmeticBinding copy).ports
      (Label.arithmetic copy) (BinaryCarry.program pc) := by
  cases pc <;> simp_all [program, BinaryCarry.program, FinitePortBinding.instruction_eq]

theorem clear_code (scratch : Bool) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc ≠ .halt) (_ : NativeBuffer.program pc ≠ .reject) :
    program (.clear scratch pc) = MicrocodeEmbedding.instruction (clearBinding scratch).ports
      (Label.clear scratch) (NativeBuffer.program pc) := by
  cases scratch <;> cases pc <;>
    simp_all [program, NativeBuffer.program, FinitePortBinding.instruction_eq]

structure Bank where
  fuel : Tape Bool
  acc : Tape Bool
  factor : Tape Bool
  scratch : Tape Bool
  zero : Tape Bool

def Bank.tapes (b : Bank) : Port → Tape Bool
  | .fuel => b.fuel | .acc => b.acc | .factor => b.factor
  | .scratch => b.scratch | .zero => b.zero

def Bank.set (b : Bank) (t : Port) (w : Tape Bool) : Bank :=
  match t with
  | .fuel => {b with fuel := w} | .acc => {b with acc := w}
  | .factor => {b with factor := w} | .scratch => {b with scratch := w}
  | .zero => {b with zero := w}

def cfg (pc : Label) (b : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc, fun t => (b.tapes t).denote⟩, pos⟩

def zipperCfg (pc : Label) (b : Bank) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc, b.tapes⟩, pos⟩

def frame (b : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun t => (b.tapes t).denote, pos⟩

def ready (fuel a x : List Bool) : Bank where
  fuel := Counter.marked fuel
  acc := BinaryCarry.marked a
  factor := BinaryCarry.marked x
  scratch := BinaryCarry.preparedOutput
  zero := BinaryCarry.marked (List.replicate x.length false)

noncomputable def nativeEncoding :=
  NativeMicrocode.initialEncoding (T := Port) (Label.counter 0)

noncomputable def nativeMachine : Transpose.TM := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k = 5 ∧ nativeMachine.g + 1 = 5 ∧
    nativeMachine.q + 1 = 99 ∧ nativeEncoding.label (.counter 0) = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 5
    decide +kernel
  · change Fintype.card Label - 1 + 1 = 99
    decide +kernel

end TransposeFollowup.RepeatedAdd
