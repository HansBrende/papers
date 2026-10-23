import BitWord.ResizeLayout

namespace BitWord
open Transpose

/-- Full rows are contiguous records, with columns and lanes in their raw order. -/
def rowBits (d b : ℕ) (A : Matrix) (i : ℕ) : List Bool :=
  (List.ofFn (fun j : Fin d => List.ofFn (fun t : Fin b => A i j t))).flatten

def matrixRows (d b : ℕ) (A : Matrix) : List (List Bool) :=
  List.ofFn (fun i : Fin d => rowBits d b A i)

 theorem matrixRows_flatten (d b : ℕ) (A : Matrix) :
     (matrixRows d b A).flatten=encode d b A := by
   simpa only [entryLists,List.flatten_flatten,List.map_ofFn,Function.comp_def,
     matrixRows,rowBits] using entryLists_flatten d b A

 theorem rowBits_length (d b : ℕ) (A : Matrix) (i : ℕ) :
     (rowBits d b A i).length=d*b := by
   simp [rowBits,List.length_flatten,List.map_ofFn,Function.comp_def]

/-- All entries outside the original top-left square are zero. -/
def padSquare (d : ℕ) (A : Matrix) : Matrix :=
  fun i j t => if i<d ∧ j<d then A i j t else false

 theorem padSquare_transpose (d : ℕ) (A : Matrix) :
     transpose (padSquare d A)=padSquare d (transpose A) := by
   funext i j t
   simp [transpose,padSquare,and_comm]

 theorem padSquare_row {d D b i : ℕ} (hd : d≤D) (hi : i<d) (A : Matrix) :
     rowBits D b (padSquare d A) i = rowBits d b A i ++ List.replicate ((D-d)*b) false := by
   have he : d+(D-d)=D := Nat.add_sub_of_le hd
   unfold rowBits
   rw [← ofFn_castLength he (fun j : Fin D => List.ofFn (fun t : Fin b => padSquare d A i j t)),
     List.ofFn_add,List.flatten_append]
   congr 1
   · apply congrArg List.flatten
     apply congrArg List.ofFn
     funext j
     apply congrArg List.ofFn
     funext t
     simp [padSquare,hi,j.isLt]
   · simp [padSquare,hi,List.ofFn_const]

 theorem padSquare_zero_row {d D b i : ℕ} (hi : d ≤ i) (A : Matrix) :
     rowBits D b (padSquare d A) i=List.replicate (D*b) false := by
   simp [rowBits,padSquare,Nat.not_lt.mpr hi,List.ofFn_const]

/-- First expansion pass: pad each of the original rows with zero columns. -/
def squareRowRecords (d D b : ℕ) (A : Matrix) : List (List Bool × List Bool) :=
  (matrixRows d b A).map (fun xs => (xs,List.replicate ((D-d)*b) false))

 theorem squareRowRecords_lengths (d D b : ℕ) (A : Matrix) :
     ∀ r ∈ squareRowRecords d D b A, r.1.length=d*b ∧ r.2.length=(D-d)*b := by
   intro r hr
   obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hr
   obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
   subst xs
   exact ⟨rowBits_length d b A i,by simp⟩

 theorem squareRowRecords_input (d D b : ℕ) (A : Matrix) :
     NativeResizeScan.inputRows true (squareRowRecords d D b A)=encode d b A := by
   simpa [NativeResizeScan.inputRows,NativeResizeScan.inputRecord,NativeResizeScan.consumed,
     squareRowRecords,List.flatMap_map,List.flatMap_def,Function.comp_def] using matrixRows_flatten d b A

 theorem squareRowRecords_output {d D b : ℕ} (hd : d≤D) (A : Matrix) :
     NativeResizeScan.outputRows true (squareRowRecords d D b A)=
       (List.ofFn (fun i : Fin d => rowBits D b (padSquare d A) i)).flatten := by
   simp only [NativeResizeScan.outputRows,NativeResizeScan.outputRecord,
     NativeResizeScan.tailOutput,squareRowRecords,List.flatMap_def,
     Function.comp_def,List.length_replicate,matrixRows,List.map_ofFn]
   apply congrArg List.flatten
   apply congrArg List.ofFn
   funext i
   exact (padSquare_row hd i.isLt A).symm

/-- Second expansion pass: append the zero bottom rows as one contiguous tail. -/
 theorem square_padding_two_pass {d D b : ℕ} (hd : d≤D) (A : Matrix) :
     NativeResizeScan.outputRows true (squareRowRecords d D b A) ++
       List.replicate ((D-d)*(D*b)) false = encode D b (padSquare d A) := by
   rw [squareRowRecords_output hd,← matrixRows_flatten]
   have he : d+(D-d)=D := Nat.add_sub_of_le hd
   unfold matrixRows
   rw [← ofFn_castLength he (fun i : Fin D => rowBits D b (padSquare d A) i),
     List.ofFn_add,List.flatten_append]
   congr 1
   simp only [Fin.val_cast,Fin.val_natAdd]
   simp [padSquare_zero_row (by omega : d ≤ d+_),List.ofFn_const]

/-- Cropping is exact even after transposition, since zero padding commutes with
transposition.  This is the semantic fact used by the two physical crop passes. -/
 theorem padSquare_encode_original (d b : ℕ) (A : Matrix) :
     encode d b (padSquare d A)=encode d b A := by
   apply encode_eq_of_pointwise
   intro i j t hi hj _
   simp [padSquare,hi,hj]

end BitWord

namespace BitWord
open Transpose

 theorem squareRowRecords_crop_input (d D b : ℕ) (A : Matrix) :
     NativeResizeScan.inputRows false (squareRowRecords d D b A)=
       NativeResizeScan.outputRows true (squareRowRecords d D b A) := by
   simp [NativeResizeScan.inputRows,NativeResizeScan.outputRows,NativeResizeScan.inputRecord,
     NativeResizeScan.outputRecord,NativeResizeScan.consumed,NativeResizeScan.tailOutput,
     squareRowRecords,List.flatMap_map]

 theorem squareRowRecords_crop_output (d D b : ℕ) (A : Matrix) :
     NativeResizeScan.outputRows false (squareRowRecords d D b A)=encode d b A := by
   simpa [NativeResizeScan.outputRows,NativeResizeScan.outputRecord,NativeResizeScan.tailOutput,
     squareRowRecords,List.flatMap_map,List.flatMap_def,Function.comp_def] using matrixRows_flatten d b A

 theorem square_crop_record_input {d D b : ℕ} (hd : d≤D) (A : Matrix) :
     NativeResizeScan.inputRecord false
       (NativeResizeScan.inputRows false (squareRowRecords d D b A))
       (List.replicate ((D-d)*(D*b)) false)=encode D b (padSquare d A) := by
   simpa [NativeResizeScan.inputRecord,NativeResizeScan.consumed,
     squareRowRecords_crop_input] using square_padding_two_pass hd A

 theorem squareRowRecords_count (d D b : ℕ) (A : Matrix) :
     (squareRowRecords d D b A).length=d := by simp [squareRowRecords,matrixRows]

 theorem squareRowRecords_padded_length {d D b : ℕ} (hd : d≤D) (A : Matrix) :
     (NativeResizeScan.inputRows false (squareRowRecords d D b A)).length=d*(D*b) := by
   rw [squareRowRecords_crop_input,squareRowRecords_output hd]
   simp [List.length_flatten,List.map_ofFn,Function.comp_def,rowBits_length]

end BitWord

namespace BitWord
open Transpose

def squareExtraRows (d D b : ℕ) : List (List Bool) :=
  List.replicate (D-d) (List.replicate (D*b) false)

 theorem squareExtraRows_count (d D b : ℕ) : (squareExtraRows d D b).length=D-d := by simp [squareExtraRows]

 theorem squareExtraRows_width (d D b : ℕ) :
     ∀ xs ∈ squareExtraRows d D b, xs.length=D*b := by
   intro xs hx
   have he : xs=List.replicate (D*b) false := (List.mem_replicate.mp hx).2
   simp [he]

 theorem square_extra_consumed (d D b : ℕ) :
     (squareExtraRows d D b).flatMap (NativeResizeScan.consumed true)=[] ∧
     (squareExtraRows d D b).flatMap (NativeResizeScan.consumed false)=
       List.replicate ((D-d)*(D*b)) false := by
   simp [squareExtraRows,NativeResizeScan.consumed,List.flatMap_replicate]

 theorem square_extra_output (d D b : ℕ) :
     (squareExtraRows d D b).flatMap (NativeResizeScan.tailOutput false)=[] ∧
     (squareExtraRows d D b).flatMap (NativeResizeScan.tailOutput true)=
       List.replicate ((D-d)*(D*b)) false := by
   simp [squareExtraRows,NativeResizeScan.tailOutput,List.flatMap_replicate]

 theorem square_expansion_layout {d D b : ℕ} (hd : d≤D) (A : Matrix) :
     NativeResizeScan.inputRows true (squareRowRecords d D b A) ++
         (squareExtraRows d D b).flatMap (NativeResizeScan.consumed true)=encode d b A ∧
     NativeResizeScan.outputRows true (squareRowRecords d D b A) ++
         (squareExtraRows d D b).flatMap (NativeResizeScan.tailOutput true)=encode D b (padSquare d A) := by
   rw [(square_extra_consumed d D b).1,(square_extra_output d D b).2,List.append_nil]
   exact ⟨squareRowRecords_input d D b A,square_padding_two_pass hd A⟩

 theorem square_cropping_layout {d D b : ℕ} (hd : d≤D) (A : Matrix) :
     NativeResizeScan.inputRows false (squareRowRecords d D b A) ++
         (squareExtraRows d D b).flatMap (NativeResizeScan.consumed false)=encode D b (padSquare d A) ∧
     NativeResizeScan.outputRows false (squareRowRecords d D b A) ++
         (squareExtraRows d D b).flatMap (NativeResizeScan.tailOutput false)=encode d b A := by
   rw [(square_extra_consumed d D b).2,(square_extra_output d D b).1,List.append_nil,
     squareRowRecords_crop_input]
   exact ⟨square_padding_two_pass hd A,squareRowRecords_crop_output d D b A⟩

end BitWord
