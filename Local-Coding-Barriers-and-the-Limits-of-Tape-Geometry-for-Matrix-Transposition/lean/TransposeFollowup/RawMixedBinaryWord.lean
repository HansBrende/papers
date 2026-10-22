import TransposeFollowup.MixedBinaryWord
import TransposeFollowup.RawBankProgram
import Transpose.Tape.Run

/-! One native executor for an entire finite word. It loads raw input once,
executes all internal stages on the same bank, and emits output once.
Every primitive, clearing pass, rewind and IO instruction is paid. -/
namespace TransposeFollowup.RawMixedBinaryWord
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
open BinaryBankOperation (Operation)
open MixedBinaryWord (Valid)
set_option autoImplicit false

def body (P : ℕ) (ops : List Operation) : RawBankProgram.Body :=
  ⟨MixedBinaryWord.ticks P ops,MixedBinaryWord.schedule P ops,
    MixedBinaryWord.result P ops,MixedBinaryWord.transform P ops⟩

theorem body_correct (P : ℕ) (ops : List Operation) (hv : Valid P ops) :
    RawBankProgram.Correct P (body P ops) where
  active := MixedBinaryWord.schedule_active P ops
  exact := MixedBinaryWord.schedule_exact P ops hv
  represents := MixedBinaryWord.result_spec P ops hv
  congr := MixedBinaryWord.transform_congr P ops hv

def ticks (P : ℕ) (ops : List Operation) : ℕ := RawBankProgram.ticks P (body P ops)

def schedule (P : ℕ) (ops : List Operation) : ℕ → NativeIO.Program (Fin 2) Mode := RawBankProgram.schedule P (body P ops)

def ready (P : ℕ) (ops : List Operation) (w : List Bool) : State := RawBankProgram.ready P (body P ops) w

def result (P : ℕ) (ops : List Operation) (w : List Bool) : State := RawBankProgram.result P (body P ops) w

def outputWord (P : ℕ) (ops : List Operation) (w : List Bool) : List Bool := RawBankProgram.outputWord P (body P ops) w

theorem schedule_active (P : ℕ) (ops : List Operation) (i : ℕ) (c : State) :
    NativeIO.Active (schedule P ops i) c :=
  RawBankProgram.schedule_active P (body P ops) (MixedBinaryWord.schedule_active P ops) i c

theorem schedule_exact (P : ℕ) (ops : List Operation) (hv : Valid P ops) (w : List Bool) :
    trajectory (schedule P ops) w RawMaskedStride.initial (ticks P ops) = result P ops w :=
  RawBankProgram.schedule_exact P (body P ops) (body_correct P ops hv) w

theorem ticks_le (P : ℕ) (hP : 0<P) (ops : List Operation) (hv : Valid P ops) :
    ticks P ops ≤ (7+27*ops.length)*P := by
  have h := MixedBinaryWord.ticks_le hP ops hv
  change 3*P+(P+(MixedBinaryWord.ticks P ops+3*P)) ≤ _
  nlinarith

theorem ready_spec (P : ℕ) (ops : List Operation) (hv : Valid P ops) (w : List Bool) :
    (∀ t, (ready P ops w).work.pos t = 0) ∧
    (∀ j < P, bit (cells (ready P ops w) 0 j) =
      MixedBinaryWord.transform P ops (fun i : ℕ => ScheduledRawInput.inputBit w i) j) ∧
    (∀ z, cells (ready P ops w) 1 z = .blank) ∧
    (ready P ops w).inputPos = P ∧ (ready P ops w).outRev = [] :=
  RawBankProgram.ready_spec P (body P ops) (body_correct P ops hv) w

theorem result_output (P : ℕ) (ops : List Operation) (hv : Valid P ops) (w : List Bool) :
    (result P ops w).outRev = (outputWord P ops w).reverse :=
  RawBankProgram.result_output P (body P ops) (body_correct P ops hv) w

noncomputable def encoding (P : ℕ) (ops : List Operation) := RawBankProgram.encoding P (body P ops)

noncomputable def machine (P : ℕ) (ops : List Operation) := RawBankProgram.machine P (body P ops)

theorem fixed_resources (P : ℕ) (ops : List Operation) :
    (machine P ops).k = 2 ∧ (machine P ops).g+1 = 5 ∧ (machine P ops).q+1 = (ticks P ops+1)*4 :=
  RawBankProgram.fixed_resources P (body P ops)

theorem native_complete (P : ℕ) (ops : List Operation) (hv : Valid P ops) (w : List Bool) :
    Transpose.stepN (machine P ops) w (ticks P ops) (Transpose.init (machine P ops)) =
      some ((lift (⟨ticks P ops,by omega⟩ : Fin (ticks P ops+1)) (result P ops w)).denote
        (encoding P ops) (program (schedule P ops) (ticks P ops))) ∧
    Transpose.step (machine P ops) w
      ((lift (⟨ticks P ops,by omega⟩ : Fin (ticks P ops+1)) (result P ops w)).denote
        (encoding P ops) (program (schedule P ops) (ticks P ops))) = none :=
  RawBankProgram.native_complete P (body P ops) (body_correct P ops hv) w

theorem native_halts (P : ℕ) (ops : List Operation) (hv : Valid P ops) (w : List Bool) :
    Transpose.Tape.HaltsAt (machine P ops) w (ticks P ops) :=
  RawBankProgram.native_halts P (body P ops) (body_correct P ops hv) w

theorem native_correct (P : ℕ) (hP : 0<P) (ops : List Operation) (hv : Valid P ops) (w : List Bool) :
    ticks P ops ≤ (7+27*ops.length)*P ∧
    Transpose.Tape.HaltsAt (machine P ops) w (ticks P ops) ∧
    (Transpose.Tape.run (machine P ops) w (ticks P ops)).outRev.reverse = outputWord P ops w ∧
    ∀ z, (Transpose.Tape.run (machine P ops) w (ticks P ops)).work ((encoding P ops).port 1) z = 0 :=
  ⟨ticks_le P hP ops hv,RawBankProgram.native_correct P (body P ops) (body_correct P ops hv) w⟩

end TransposeFollowup.RawMixedBinaryWord
