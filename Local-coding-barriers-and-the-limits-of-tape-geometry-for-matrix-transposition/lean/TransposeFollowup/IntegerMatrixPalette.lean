import TransposeFollowup.MatrixPermutationPalette
import TransposeFollowup.RawRowXor
import TransposeFollowup.RawUnitArithmeticNative

/-! Exactly the declared integer palette, on a d-by-d matrix of b bits.
The integer and ternary operation types are separate; integer arithmetic
is never declared to be an operation on ternary values. -/
namespace TransposeFollowup.IntegerMatrixPalette
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
set_option autoImplicit false

inductive Operation where
  | permutation (op : MatrixPermutationPalette.Operation)
  | addRows (subtract : Bool)
  | xorRows (isPrefix : Bool)
  | unit (subtract : Bool)

noncomputable def cost (b d : ℕ) : Operation → ℕ
  | .permutation op => MatrixPermutationPalette.cost b d op
  | .addRows _ => BufferedRows.bankTicks (d*b) d
  | .xorRows _ => MaskedStrideBankStage.ticks (d*(d*b)) (d*b)
  | .unit _ => RawCarryBank.ticks (d*(d*b))

noncomputable def code (b d : ℕ) : Operation → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode
  | .permutation op => MatrixPermutationPalette.code b d op
  | .addRows sub => SharedRowBank.ruleSchedule (RawRowArithmetic.rule sub) (d*b) d
  | .xorRows isPrefix => RawRowXor.schedule isPrefix (d*(d*b)) (d*b)
  | .unit sub => RawUnitArithmetic.schedule sub (d*(d*b))

def value (b d : ℕ) : Operation → (ℕ → Sym Bool) → ℕ → Sym Bool
  | .permutation op => MatrixPermutationPalette.value b d op
  | .addRows sub => BufferedRows.bankValue (RawRowArithmetic.rule sub) (d*b) d
  | .xorRows isPrefix => RawRowXor.value isPrefix (d*b)
  | .unit sub => RawUnitArithmetic.value sub (d*(d*b))

theorem correct (b d : ℕ) (hb : 0<b) (hd : 0<d) :
    RawSymbolWord.Correct (d*(d*b)) (cost b d) (code b d) (value b d) where
  active := by
    intro op i c
    cases op with
    | permutation op => exact (MatrixPermutationPalette.correct b d).active op i c
    | addRows sub => exact SharedRowBank.rule_active (RawRowArithmetic.rule sub) (d*b) d i c
    | xorRows isPrefix => exact RawRowXor.schedule_active isPrefix (d*(d*b)) (d*b) i c
    | unit sub => exact RawUnitArithmetic.schedule_active sub (d*(d*b)) i c
  congruent := by
    intro op
    cases op with
    | permutation op => exact (MatrixPermutationPalette.correct b d).congruent op
    | addRows sub => exact BufferedRows.bankValue_congr (RawRowArithmetic.rule sub) (d*b) d
    | xorRows isPrefix => exact RawRowXor.value_congr isPrefix (d*(d*b)) (Nat.mul_pos hd hb)
    | unit sub => exact RawUnitArithmetic.value_congr sub (d*(d*b))
  represents := by
    intro op w c hc
    cases op with
    | permutation op => exact (MatrixPermutationPalette.correct b d).represents op w c hc
    | addRows sub =>
      change BankWord.Represents BankWord.symbols (d*(d*b)) c
        (trajectory (SharedRowBank.ruleSchedule (RawRowArithmetic.rule sub) (d*b) d) w c
          (BufferedRows.bankTicks (d*b) d)) _
      rw [SharedRowBank.rule_exact]
      exact SharedRowBank.rule_represents (RawRowArithmetic.rule sub) (d*b) d w c hc
    | xorRows isPrefix => exact RawRowXor.represents isPrefix (d*(d*b)) (Nat.mul_pos hd hb) w c hc
    | unit sub => exact RawUnitArithmetic.represents sub (d*(d*b)) w c hc

theorem cost_le (b d : ℕ) (hb : 0<b) (hd : 0<d) (op : Operation) :
    cost b d op ≤ 24*(d*(d*b)) := by
  cases op with
  | permutation op => exact MatrixPermutationPalette.cost_le b d op
  | addRows sub => exact (BufferedRows.bank_ticks_linear (d*b) d (Nat.mul_pos hd hb) hd).trans (by omega)
  | xorRows isPrefix =>
    exact (MaskedStrideBankStage.ticks_le (d*(d*b)) (d*b) (Nat.le_mul_of_pos_left _ hd)).trans (by omega)
  | unit sub =>
    change RawCarryBank.ticks (d*(d*b)) ≤ _
    rw [RawCarryBank.ticks_eq _ (Nat.mul_pos hd (Nat.mul_pos hd hb))]
    omega

def output (b d : ℕ) (ops : List Operation) (w : List Bool) : List Bool :=
  RawSymbolWord.output (d*(d*b)) (value b d) ops w

end TransposeFollowup.IntegerMatrixPalette
