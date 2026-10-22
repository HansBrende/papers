import TransposeFollowup.RawSymbolWord
import TransposeFollowup.RawEntryReversal
import TransposeFollowup.RawEntryRotation

/-! The shared R,C,E/e part of the two declared matrix palettes. These
are exact symbol permutations, preserving every bit or trit within entries. -/
namespace TransposeFollowup.MatrixPermutationPalette
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
set_option autoImplicit false

inductive Operation where
  | rows
  | entries
  | rotate (inverse : Bool)

def cost (b d : ℕ) : Operation → ℕ
  | .rows => BankBlockReversal.ticks (d*b) d
  | .entries => RawEntryReversal.internalTicks b d d
  | .rotate sub => RawEntryRotation.internalTicks sub b d d

noncomputable def code (b d : ℕ) : Operation → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode
  | .rows => RawBlockReversal.schedule (d*b) d
  | .entries => RawEntryReversal.schedule b d d
  | .rotate sub => RawEntryRotation.schedule sub b d d

def value (b d : ℕ) : Operation → (ℕ → Sym Bool) → ℕ → Sym Bool
  | .rows => BankBlockReversal.value (d*b) d
  | .entries => RawEntryReversal.value b d
  | .rotate sub => RawEntryRotation.value sub b d

theorem correct (b d : ℕ) : RawSymbolWord.Correct (d*(d*b)) (cost b d) (code b d) (value b d) where
  active := by
    intro op i c
    cases op with
    | rows => exact RawBlockReversal.schedule_active (d*b) d i c
    | entries => exact RawEntryReversal.schedule_active b d d i c
    | rotate sub => exact RawEntryRotation.schedule_active sub b d d i c
  congruent := by
    intro op
    cases op with
    | rows => exact BankBlockReversal.value_congr (d*b) d
    | entries => exact RawEntryReversal.value_congr b d d
    | rotate sub => exact RawEntryRotation.value_congr sub b d d
  represents := by
    intro op w c hc
    cases op with
    | rows => exact RawBlockReversal.represents (d*b) d w c hc
    | entries => exact RawEntryReversal.represents b d d w c hc
    | rotate sub => exact RawEntryRotation.represents sub b d d w c hc

theorem cost_le (b d : ℕ) (op : Operation) : cost b d op ≤ 24*(d*(d*b)) := by
  cases op with
  | rows => rw [cost,BankBlockReversal.ticks_eq]; omega
  | entries => rw [cost,RawEntryReversal.internal_ticks_eq]; omega
  | rotate sub => rw [cost,RawEntryRotation.internal_ticks_eq]

end TransposeFollowup.MatrixPermutationPalette
