import TransposeFollowup.RawSymbolRotation

/-! Whole-entry S/s uses the already verified arbitrary symbol rotation.
Offsets are b and (n-1)b for n entries of width b. All entry lanes retain
their order. The older one-symbol shift corollaries are the b=1 case. -/
namespace TransposeFollowup.RawEntryShift
open FixedTapeCompiler
open CopyMachine (Sym)
set_option autoImplicit false

def offset (right : Bool) (b n : ℕ) : ℕ :=
  RawSymbolRotation.shiftOffset right n*b

theorem offset_le (right : Bool) (b n : ℕ) : offset right b n ≤ n*b :=
  Nat.mul_le_mul_right b (RawSymbolRotation.shiftOffset_le right n)

theorem index_entry (right : Bool) (b n k l : ℕ) (hk : k<n) (hl : l<b) :
    (k*b+l+offset right b n)%(n*b)=
      ((k+RawSymbolRotation.shiftOffset right n)%n)*b+l := by
  have hn : 0<n := Nat.zero_lt_of_lt hk
  have hrem : ((k+RawSymbolRotation.shiftOffset right n)%n)*b+l<n*b := by
    have := Nat.mul_le_mul_right b (Nat.mod_lt (k+RawSymbolRotation.shiftOffset right n) hn)
    nlinarith
  rw [offset,show k*b+l+RawSymbolRotation.shiftOffset right n*b=
      (k+RawSymbolRotation.shiftOffset right n)*b+l by ring,
    Nat.add_mod,Nat.mul_mod_mul_right,
    Nat.mod_eq_of_lt (hl.trans_le (Nat.le_mul_of_pos_left b hn)),Nat.mod_eq_of_lt hrem]

theorem left_value_entry (b n : ℕ) (x : ℕ → Sym Bool) (k l : ℕ) (hk : k<n) (hl : l<b) :
    BankSymbolRotation.value (n*b) (offset false b n) x (k*b+l)=x (((k+1)%n)*b+l) := by
  rw [BankSymbolRotation.value,index_entry false b n k l hk hl,
    RawSymbolRotation.left_shift_index n k hk]

theorem right_value_entry (b n : ℕ) (x : ℕ → Sym Bool) (k l : ℕ) (hk : k<n) (hl : l<b) :
    BankSymbolRotation.value (n*b) (offset true b n) x (k*b+l)=
      x ((if k=0 then n-1 else k-1)*b+l) := by
  rw [BankSymbolRotation.value,index_entry true b n k l hk hl,
    RawSymbolRotation.right_shift_index n k hk]

end TransposeFollowup.RawEntryShift
