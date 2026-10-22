import TransposeFollowup.MatrixPermutationPalette
import TransposeFollowup.RawTernaryVertical
import TransposeFollowup.RawTernaryMatrixHorizontal
import TransposeFollowup.TernaryPhase
import TransposeFollowup.RawEntryShift

/-! Exactly the full b-trit F3 palette. A whole word keeps exact symbols
on its bank; only the final output definition projects to raw bits. -/
namespace TransposeFollowup.TernaryMatrixPalette
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
set_option autoImplicit false

inductive Operation where
  | permutation (op : MatrixPermutationPalette.Operation)
  | vertical (difference : Bool)
  | horizontal (difference : Bool)
  | phase
  | shift (right : Bool)

noncomputable def cost (b d : ℕ) : Operation → ℕ
  | .permutation op => MatrixPermutationPalette.cost b d op
  | .vertical _ => RawTernaryVertical.internalTicks b d
  | .horizontal _ => RawTernaryMatrixHorizontal.internalTicks b d d
  | .phase => RawSymbolMap.internalTicks (TernaryPhase.table b d) (d*(d*b))
  | .shift right => BankSymbolRotation.ticks (d*(d*b)) (RawEntryShift.offset right b (d*d))

noncomputable def code (b d : ℕ) : Operation → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode
  | .permutation op => MatrixPermutationPalette.code b d op
  | .vertical sub => RawTernaryVertical.schedule sub b d
  | .horizontal sub => RawTernaryMatrixHorizontal.schedule sub b d d
  | .phase => RawSymbolMap.schedule (TernaryPhase.table b d) (d*(d*b))
  | .shift right => BankSymbolRotation.schedule (d*(d*b)) (RawEntryShift.offset right b (d*d))

def value (b d : ℕ) : Operation → (ℕ → Sym Bool) → ℕ → Sym Bool
  | .permutation op => MatrixPermutationPalette.value b d op
  | .vertical sub => RawTernaryVertical.value sub b d
  | .horizontal sub => RawTernaryMatrixHorizontal.value sub b d
  | .phase => RawSymbolMap.value (TernaryPhase.table b d)
  | .shift right => BankSymbolRotation.value (d*(d*b)) (RawEntryShift.offset right b (d*d))

theorem shift_le (right : Bool) (b d : ℕ) : RawEntryShift.offset right b (d*d) ≤ d*(d*b) := by
  simpa only [Nat.mul_assoc] using RawEntryShift.offset_le right b (d*d)

theorem correct (b d : ℕ) :
    RawSymbolWord.Correct (d*(d*b)) (cost b d) (code b d) (value b d) where
  active := by
    intro op i c
    cases op with
    | permutation op => exact (MatrixPermutationPalette.correct b d).active op i c
    | vertical sub => exact SharedRowBank.rule_active (TernaryBank.bufferRule sub) (d*b) d i c
    | horizontal sub => exact RawTernaryMatrixHorizontal.schedule_active sub b d d i c
    | phase => exact RawSymbolMap.schedule_active (TernaryPhase.table b d) (d*(d*b)) i c
    | shift right => exact BankSymbolRotation.schedule_active (d*(d*b)) (RawEntryShift.offset right b (d*d)) i c
  congruent := by
    intro op
    cases op with
    | permutation op => exact (MatrixPermutationPalette.correct b d).congruent op
    | vertical sub => exact RawTernaryVertical.value_congr sub b d
    | horizontal sub => exact RawTernaryMatrixHorizontal.value_congr sub b d d
    | phase => exact RawSymbolMap.value_congr (TernaryPhase.table b d) (d*(d*b))
    | shift right => exact BankSymbolRotation.value_congr (d*(d*b)) (RawEntryShift.offset right b (d*d))
  represents := by
    intro op w c hc
    cases op with
    | permutation op => exact (MatrixPermutationPalette.correct b d).represents op w c hc
    | vertical sub => exact RawTernaryVertical.represents sub b d w c hc
    | horizontal sub => exact RawTernaryMatrixHorizontal.represents sub b d d w c hc
    | phase => exact RawSymbolMap.represents (TernaryPhase.table b d) (d*(d*b)) w c hc
    | shift right =>
      change BankWord.Represents BankWord.symbols (d*(d*b)) c
        (trajectory (BankSymbolRotation.schedule (d*(d*b)) (RawEntryShift.offset right b (d*d))) w c
          (BankSymbolRotation.ticks (d*(d*b)) (RawEntryShift.offset right b (d*d)))) _
      rw [BankSymbolRotation.schedule_exact]
      exact BankSymbolRotation.represents (d*(d*b)) (RawEntryShift.offset right b (d*d))
        (shift_le right b d) w c hc

theorem cost_le (b d : ℕ) (hb : 0<b) (hd : 0<d) (op : Operation) :
    cost b d op ≤ 24*(d*(d*b)) := by
  cases op with
  | permutation op => exact MatrixPermutationPalette.cost_le b d op
  | vertical sub => exact (BufferedRows.bank_ticks_linear (d*b) d (Nat.mul_pos hd hb) hd).trans (by omega)
  | horizontal sub =>
    change RawTernaryMatrixHorizontal.internalTicks b d d ≤ _
    rw [RawTernaryMatrixHorizontal.internal_ticks_eq b d d hb hd]; omega
  | phase =>
    change RawSymbolMap.internalTicks (TernaryPhase.table b d) (d*(d*b)) ≤ _
    rw [RawSymbolMap.internal_ticks_eq]; omega
  | shift right =>
    change BankSymbolRotation.ticks (d*(d*b)) (RawEntryShift.offset right b (d*d)) ≤ _
    rw [BankSymbolRotation.ticks_eq _ _ (shift_le right b d)]; omega

def output (b d : ℕ) (ops : List Operation) (w : List Bool) : List Bool :=
  RawSymbolWord.output (d*(d*b)) (value b d) ops w

end TransposeFollowup.TernaryMatrixPalette
