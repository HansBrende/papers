import TransposeFollowup.IndexedBankRowsInvariant

/-! The identical-row interface is the constant-family specialization of
 the indexed frame invariant. Existing statements are preserved. -/
namespace TransposeFollowup.ScheduledBankRows
open Classical FixedTapeCompiler ScheduledTapeAction
open CopyMachine (Sym)
set_option autoImplicit false
variable {M : Type*} {W : ℕ} (U : Update M W)

theorem rows_value (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) (k j : ℕ) (hk : k<r) (hj : j<W) :
    cells (rows U r w c) 0 (c.work.pos 0+k*W+j)=
      U.value (fun i => cells c 0 (c.work.pos 0+k*W+i)) j := by
  simpa only [IndexedBankRows.rows_constant] using
    IndexedBankRows.rows_value (fun _ => U) r w c hc k j hk hj

def value (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool :=
  U.value (fun i => x ((j/W)*W+i)) (j%W)

theorem value_congr (r : ℕ) : BankWord.Congruent (r*W) (value U) :=
  IndexedBankRows.value_congr (fun _ => U) r

theorem represents (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (r*W) c (result U r w c)
      (value U (BankWord.input BankWord.symbols c)) := by
  change BankWord.Represents BankWord.symbols (r*W) c (result U r w c)
    (IndexedBankRows.value (fun _ => U) (BankWord.input BankWord.symbols c))
  simpa only [IndexedBankRows.result,IndexedBankRows.rows_constant,result]
    using IndexedBankRows.represents (fun _ => U) r w c hc

theorem result_frame (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+r*W ≤ z) :
    cells (result U r w c) 0 z=cells c 0 z := by
  simpa only [IndexedBankRows.result,IndexedBankRows.rows_constant,result] using
    IndexedBankRows.result_frame (fun _ => U) r w c z hz

end TransposeFollowup.ScheduledBankRows
