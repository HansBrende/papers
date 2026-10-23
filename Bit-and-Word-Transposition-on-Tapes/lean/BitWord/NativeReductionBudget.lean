import BitWord.CanonicalBounds
import BitWord.NativeCanonicalGeneratorRun

/-! A coarse linear bound for the six paid phases of the fixed wrapper. -/
namespace BitWord.NativeReductionBudget
open Transpose

def total (P V h wordLength κ : ℕ) : ℕ :=
  40000*P + 2*(200*V+200) + 200*(V+wordLength+1) +
    13*((κ+300)*V+24*(2*h+2)+101) + (3*P+1) + 6

theorem total_le (P V h wordLength κ : ℕ) (hP : 1≤P) (hh : h≤P)
    (hV : V≤16*P) (hw : wordLength≤4*h+8) :
    total P V h wordLength κ≤(200000+208*κ)*P := by
  have hm := Nat.mul_le_mul_left (13*(κ+300)) hV
  unfold total
  nlinarith

def volume (d : ℕ) : ℕ := 2^(2*entryBits d+tailBits (entryBits d))

theorem volume_eq (d : ℕ) :
    volume d=(2^entryBits d)*(2^entryBits d)*(2^tailBits (entryBits d)) := by
  unfold volume
  rw [pow_add,show 2*entryBits d=entryBits d+entryBits d by omega,pow_add]

theorem volume_le {d : ℕ} (hd : 1≤d) : volume d≤16*inputLength d := by
  rw [volume_eq]
  exact canonical_padded_volume hd

theorem canonical_bound {d : ℕ} (hd : 1≤d) (κ : ℕ) :
    total (inputLength d) (volume d) (entryBits d)
      (NativeCanonicalGenerator.fieldWord (entryBits d) .n).length κ ≤
      (200000+208*κ)*inputLength d := by
  exact total_le _ _ _ _ _ (canonical_input_bounds hd).1
    (canonical_input_bounds hd).2.2.1 (volume_le hd)
    (NativeCanonicalGenerator.field_word_length _ _)

end BitWord.NativeReductionBudget
