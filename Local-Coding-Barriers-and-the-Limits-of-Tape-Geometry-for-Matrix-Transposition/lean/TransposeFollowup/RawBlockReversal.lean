import TransposeFollowup.BankBlockReversalInvariant
import TransposeFollowup.RawRowProgram

/-! The exact-symbol reversal on the shared 200-mode controller and raw
native IO shell. The same symbol field can serve later integer/trit
permutations. Reading a symbol and writing it back is an exact identity. -/
namespace TransposeFollowup.SharedBankSymbols
open FixedTapeCompiler
open CopyMachine (Sym)
set_option autoImplicit false

def read (s : Sym Bool) : SharedRowBank.Mode := ((false,false),(false,s,.blank))
def write (m : SharedRowBank.Mode) : Sym Bool := m.2.2.1
def reset : SharedRowBank.Mode := ((false,false),SharedRowBank.initialRowMode)
theorem write_read : Function.LeftInverse write read := fun _ => rfl

end TransposeFollowup.SharedBankSymbols

namespace TransposeFollowup.RawBlockReversal
open Classical FixedTapeCompiler ScheduledNativeIO
open SharedBankSymbols
set_option autoImplicit false

def schedule (B n : ℕ) : ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode :=
  BankBlockReversal.schedule read write reset B n

theorem schedule_active (B n i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (schedule B n i) c := BankBlockReversal.schedule_active _ _ _ _ _ _ _

theorem represents (B n : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (n*B) c
      (trajectory (schedule B n) w c (BankBlockReversal.ticks B n))
      (BankBlockReversal.value B n (BankWord.input BankWord.symbols c)) := by
  rw [schedule,BankBlockReversal.schedule_exact]
  exact BankBlockReversal.represents read write reset write_read B n w c hc

def ticks (B n : ℕ) : ℕ := RawProgramShell.ticks (n*B) (BankBlockReversal.ticks B n)

noncomputable def machine (B n : ℕ) :=
  RawProgramShell.machine SharedRowBank.initialRowMode (n*B) (BankBlockReversal.ticks B n) (schedule B n)

def output (B n : ℕ) (w : List Bool) : List Bool :=
  (List.range (n*B)).map (fun j => ScheduledRawInput.inputBit w (BankBlockReversal.index B n j))

theorem ticks_eq (B n : ℕ) : ticks B n=17*(n*B) := by
  rw [ticks,RawProgramShell.ticks_eq,BankBlockReversal.ticks_eq]
  omega

theorem native_correct (B n : ℕ) (w : List Bool) :
    ∃ d : Transpose.Config (machine B n),
      Transpose.stepN (machine B n) w (ticks B n) (Transpose.init (machine B n))=some d ∧
      Transpose.step (machine B n) w d=none ∧ d.outRev=(output B n w).reverse ∧
      ∀ z, d.work ((RawProgramShell.encoding SharedRowBank.initialRowMode (n*B)
        (BankBlockReversal.ticks B n)).port 1) z=0 := by
  exact RawProgramShell.native_correct SharedRowBank.initialRowMode (n*B) (BankBlockReversal.ticks B n)
    (schedule B n) (schedule_active B n) (BankBlockReversal.value B n)
    (BankBlockReversal.value_congr B n) (fun w c hc => represents B n w c hc) w

theorem resources (B n : ℕ) :
    (machine B n).k=2 ∧ (machine B n).g+1=5 ∧ (machine B n).q+1=(ticks B n+1)*200 := by
  have h := RawProgramShell.fixed_resources SharedRowBank.initialRowMode (n*B)
    (BankBlockReversal.ticks B n) (schedule B n)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

end TransposeFollowup.RawBlockReversal
