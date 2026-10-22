import TransposeFollowup.NormalizedBatchRun
import TransposeFollowup.FamilyReaderRun
import TransposeFollowup.LinearGenerationBudget

namespace TransposeFollowup.NormalizedBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem row_records_length_le (F : RationalMobius) (xs : List Bool) (i : Fin (Counter.value xs)) :
    (RowEnumeration.rowRecords F xs i).length ≤ Counter.value xs := by
  unfold RowEnumeration.rowRecords
  rw [RowConsumer.records_length]
  exact List.count_le_length.trans_eq (F.denseRow_length i)

theorem rows_records_length_le (F : RationalMobius) (xs : List Bool) (r i : ℕ) :
    (RowEnumeration.rowsRecords F xs r i).length ≤ r*Counter.value xs := by
  induction r generalizing i with
  | zero => simp [RowEnumeration.rowsRecords]
  | succ r ih =>
    by_cases hi : i<Counter.value xs
    · simp only [RowEnumeration.rowsRecords,hi,↓reduceDIte,List.length_append]
      have ha:=row_records_length_le F xs ⟨i,hi⟩
      have hb:=ih (i+1)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · simp [RowEnumeration.rowsRecords,hi]

theorem linear_budget (small large n : ℕ) (h : small≤large) (hn : 1≤n) (xs : List Bool)
    (hx : xs.length≤(n+1).size) (rs : List (List Bool × List Bool)) (hr : rs.length≤n*n) :
    batchBudget small (large-small) xs rs ≤ (74*large+648)*Transpose.inputLength n := by
  have hc : rs.length+1≤n*(n+1) := by nlinarith
  have hw : 80*xs.length+37*large+84 ≤ 37*large+84+80*(n+1).size := by omega
  calc
    _ ≤ (rs.length+1)*(80*xs.length+37*large+84) := common_budget small large h xs rs
    _ ≤ (n*(n+1))*(37*large+84+80*(n+1).size) := Nat.mul_le_mul hc hw
    _ ≤ (74*large+648)*Transpose.inputLength n := by
      have he : 2*((37*large+84)+3*80)=74*large+648 := by ring
      simpa only [Nat.mul_assoc,he] using linear_repetition_budget (37*large+84) 80 n hn

theorem map_linear_budget (F : RationalMobius) (large : ℕ) (hc : PaddedWord.commonConstant F≤large)
    (xs : List Bool) (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size) :
    batchBudget (PaddedWord.commonConstant F) (large-PaddedWord.commonConstant F) xs
      (RowEnumeration.rowsRecords F xs (Counter.value xs) 0) ≤ (74*large+648)*Transpose.inputLength (Counter.value xs) :=
  linear_budget _ _ _ hc hn xs hx _ (rows_records_length_le F xs _ _)

end TransposeFollowup.NormalizedBatch
