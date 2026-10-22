import TransposeFollowup.RawNormalizationMeaning

/-! The actual stored record stream is sparse,even though generation uses
a dense scan. This is the bound needed to pay later pairwise canonical scans. -/
namespace TransposeFollowup.FamilyNormalization
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

theorem row_record_count (F : RationalMobius) (xs : List Bool) (i : Fin (Counter.value xs)) :
    (RowEnumeration.rowRecords F xs i).length=(F.neighbors i).card := by
  have ht : (RowConsumer.targets (F.denseRow i) 0).toFinset=(F.neighbors i).image Fin.val := by
    ext j
    constructor
    · intro hj
      have hj':=List.mem_toFinset.mp hj
      have hb:=(RowConsumer.targets_bounds (F.denseRow i) 0 j hj').2
      have hjn : j<Counter.value xs := by simpa only [Nat.zero_add,F.denseRow_length] using hb
      exact Finset.mem_image.mpr ⟨⟨j,hjn⟩,(RowConsumer.dense_targets F i ⟨j,hjn⟩).mp hj',rfl⟩
    · intro hj
      obtain ⟨j,hmem,rfl⟩:=Finset.mem_image.mp hj
      exact List.mem_toFinset.mpr ((RowConsumer.dense_targets F i j).mpr hmem)
  have hl:=congrArg List.length (RowEnumeration.row_values F xs i)
  simp only [List.length_map] at hl
  rw [hl,← List.toFinset_card_of_nodup (RowConsumer.targets_nodup (F.denseRow i) 0),ht]
  exact Finset.card_image_of_injective _ Fin.val_injective

theorem sparse_rows_count (F : RationalMobius) (xs : List Bool) (q k : ℕ) :
    (RowEnumeration.rowsRecords F xs q k).length≤q*(F.distortion+1) := by
  induction q generalizing k with
  | zero => simp [RowEnumeration.rowsRecords]
  | succ q ih =>
    by_cases hk : k<Counter.value xs
    · simp only [RowEnumeration.rowsRecords,hk,↓reduceDIte,List.length_append,row_record_count,Nat.add_mul,Nat.one_mul]
      have ha:=F.neighbors_card_le (⟨k,hk⟩ : Fin (Counter.value xs))
      have hb:=ih (k+1)
      omega
    · simp [RowEnumeration.rowsRecords,hk]

theorem normalized_records_count (F : Fin c → RationalMobius) (xs : List Bool) (i : Fin c) :
    (normalizedRecords F xs i).length≤Counter.value xs*((F i).distortion+1) := by
  simpa only [normalizedRecords,NormalizedBatch.normalizedRecords,List.length_map,records] using sparse_rows_count (F i) xs (Counter.value xs) 0

theorem total_records_count (F : Fin c → RationalMobius) (xs : List Bool) :
    (List.ofFn (normalizedRecords F xs)).flatten.length≤Counter.value xs*(∑ i : Fin c,((F i).distortion+1)) := by
  calc
    _ = ∑ i : Fin c,(normalizedRecords F xs i).length := by simp [Fin.sum_ofFn]
    _ ≤ ∑ i : Fin c,Counter.value xs*((F i).distortion+1) := Finset.sum_le_sum (fun i _ => normalized_records_count F xs i)
    _ = _ := by rw [Finset.mul_sum]

end TransposeFollowup.FamilyNormalization
