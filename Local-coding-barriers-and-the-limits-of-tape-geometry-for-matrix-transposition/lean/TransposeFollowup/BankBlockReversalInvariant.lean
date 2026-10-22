import TransposeFollowup.BankBlockReversal
import TransposeFollowup.RawRowBankInvariant

/-! The exact-symbol, clean-bank composition interface for block reversal.
The permutation reflects the block coordinate and keeps the symbol offset.
The quotient/remainder operations here specify the result; the machine
executes the already charged sequential schedule, not random access. -/
namespace TransposeFollowup.BankBlockReversal
open FixedTapeCompiler ScheduledTapeAction
open CopyMachine (Sym)
set_option autoImplicit false
variable {M : Type*}

def index (B n j : ℕ) : ℕ := (n-1-j/B)*B+j%B

theorem index_lt (B n j : ℕ) (hj : j<n*B) : index B n j<n*B := by
  have hB : 0<B := by nlinarith
  have hk : j/B<n := (Nat.div_lt_iff_lt_mul hB).mpr hj
  have hm := Nat.mod_lt j hB
  have hn : n-1-j/B+1≤n := by
    calc
      _ ≤ (n-1)+1 := Nat.add_le_add_right (Nat.sub_le _ _) 1
      _ = n := Nat.sub_add_cancel (Nat.zero_lt_of_lt hk)
  have hmul := Nat.mul_le_mul_right B hn
  unfold index
  nlinarith

def value (B n : ℕ) (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool := x (index B n j)

theorem value_congr (B n : ℕ) : BankWord.Congruent (n*B) (value B n) := by
  intro x y h j hj
  exact h _ (index_lt B n j hj)

theorem result_value (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (hinv : Function.LeftInverse write read) (B n : ℕ) (w : List Bool)
    (c : NativeIO.Config (Fin 2) M) (j : ℕ) (hj : j<n*B) :
    cells (result read write reset B n w c) 0 (c.work.pos 0+j)=
      cells c 0 (c.work.pos 0+index B n j) := by
  have hB : 0<B := by nlinarith
  have hk : j/B<n := (Nat.div_lt_iff_lt_mul hB).mpr hj
  have h := result_blocks read write reset hinv B n w c (j/B) (j%B) hk (Nat.mod_lt j hB)
  have he : (j/B)*B+j%B=j := Nat.div_add_mod' j B
  have hez : ((j/B : ℕ) : ℤ)*B+(j%B : ℕ)=j := by exact_mod_cast he
  simpa only [index,Nat.cast_add,Nat.cast_mul,add_assoc,hez] using h

theorem represents (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (hinv : Function.LeftInverse write read) (B n : ℕ) (w : List Bool)
    (c : NativeIO.Config (Fin 2) M) (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (n*B) c (result read write reset B n w c)
      (value B n (BankWord.input BankWord.symbols c)) := by
  refine ⟨result_positions read write reset B n w c,?_,
    result_scratch read write reset B n w c hc,
    (result_io read write reset B n w c).1,(result_io read write reset B n w c).2⟩
  intro j hj
  exact result_value read write reset hinv B n w c j hj

end TransposeFollowup.BankBlockReversal
