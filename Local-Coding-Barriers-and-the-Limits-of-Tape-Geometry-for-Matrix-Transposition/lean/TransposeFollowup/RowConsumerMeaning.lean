import TransposeFollowup.RowConsumerRun
import TransposeFollowup.SeedMultipleMeaning

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler
set_option autoImplicit false

theorem values_zero (row unit flags : List Bool) (hu : BinaryCompare.value unit=1)
    (hfit : flags.length<2^unit.length) :
    (records row unit flags (zeroWord unit)).map
      (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2)) =
      (targets flags 0).map (fun j => (BinaryCompare.value row,j)) := by
  simpa only [zeroWord,RepeatedAdd.zero_value,Nat.zero_add] using
    records_values row unit flags (zeroWord unit) (List.length_replicate ..) hu
      (by simpa only [zeroWord,RepeatedAdd.zero_value,Nat.zero_add] using hfit)

theorem dense_targets (F : RationalMobius) {N : ℕ} (i j : Fin N) :
    j.val ∈ targets (F.denseRow i) 0 ↔ j ∈ F.neighbors i := by
  rw [F.denseRow_eq_range,mem_targets_range,F.mem_neighbors]
  exact (and_iff_right j.isLt).trans (F.denseHit_spec i j)

theorem dense_record_values (F : RationalMobius) {N : ℕ} (i : Fin N)
    (row unit : List Bool) (hu : BinaryCompare.value unit=1)
    (hi : BinaryCompare.value row=i.val) (hfit : N<2^unit.length) :
    (records row unit (F.denseRow i) (zeroWord unit)).map
      (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2)) =
      (targets (F.denseRow i) 0).map (fun j => (i.val,j)) := by
  simpa only [hi] using values_zero row unit (F.denseRow i) hu (by simpa only [F.denseRow_length] using hfit)

theorem dense_record_mem (F : RationalMobius) {N : ℕ} (i j : Fin N)
    (row unit : List Bool) (hu : BinaryCompare.value unit=1)
    (hi : BinaryCompare.value row=i.val) (hfit : N<2^unit.length) :
    (i.val,j.val) ∈ (records row unit (F.denseRow i) (zeroWord unit)).map
      (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2)) ↔ j ∈ F.neighbors i := by
  rw [dense_record_values F i row unit hu hi hfit]
  simpa only [List.mem_map,Prod.mk.injEq,true_and,exists_eq_right] using dense_targets F i j

theorem dense_record_nodup (F : RationalMobius) {N : ℕ} (i : Fin N)
    (row unit : List Bool) (hu : BinaryCompare.value unit=1)
    (hi : BinaryCompare.value row=i.val) (hfit : N<2^unit.length) :
    ((records row unit (F.denseRow i) (zeroWord unit)).map
      (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2))).Nodup := by
  rw [dense_record_values F i row unit hu hi hfit]
  exact (targets_nodup (F.denseRow i) 0).map (fun _ _ h => congrArg Prod.snd h)

theorem common_index_fit (F : RationalMobius) (source : List Bool) :
    Counter.value source<2^(PaddedWord.word (PaddedWord.commonConstant F) id source).length := by
  rw [← PaddedWord.common_value F source,NativeCounter.word_value]
  exact BinaryCarry.value_lt _

theorem total_budget (F : RationalMobius) (N : ℕ) (source flags : List Bool)
    (hN : 1 ≤ N) (hl : source.length ≤ (N+1).size) (hf : flags.length=N) :
    N*budget (PaddedWord.word (PaddedWord.commonConstant F) id source).length flags ≤
      (72*(F.integerOperandConstant^2).size+920)*Transpose.inputLength N := by
  let m := (PaddedWord.word (PaddedWord.commonConstant F) id source).length
  have hc := budget_le m flags
  rw [hf] at hc
  have hmore : 10*m+30 ≤ N*(10*m+30) := Nat.le_mul_of_pos_left _ hN
  have hstep : budget m flags ≤ N*(36*m+100) := by nlinarith
  have hm : 36*m+100 ≤ (36*PaddedWord.commonConstant F+100)+72*(N+1).size := by
    dsimp [m]; rw [PaddedWord.word_length]; omega
  have h := dense_scan_budget (36*PaddedWord.commonConstant F+100) 72 N hN
  have he : 2*(36*PaddedWord.commonConstant F+100+3*72)=72*(F.integerOperandConstant^2).size+920 := by
    unfold PaddedWord.commonConstant; ring
  calc
    _ ≤ N*(N*(36*m+100)) := Nat.mul_le_mul_left _ hstep
    _ ≤ N*(N*((36*PaddedWord.commonConstant F+100)+72*(N+1).size)) := by gcongr
    _ ≤ _ := by simpa only [he] using h

end TransposeFollowup.RowConsumer
