import BitWord.NativeResizeRows
import BitWord.AddressFields

namespace BitWord
open Transpose

 theorem concatUpTo_ofFn (f : ℕ → List Bool) (n : ℕ) :
     concatUpTo f n = (List.ofFn (fun i : Fin n => f i)).flatten := by
   induction n with
   | zero => rfl
   | succ n ih =>
     rw [concatUpTo, List.ofFn_succ']
     simpa only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using congrArg (fun xs => xs++f n) ih

/-- Entry records in exactly the order seen by a row-major tape scan. -/
def entryLists (d b : ℕ) (A : Matrix) : List (List Bool) :=
  (List.ofFn (fun i : Fin d => List.ofFn (fun j : Fin d =>
    List.ofFn (fun t : Fin b => A i j t)))).flatten

 theorem flatten_ofFn_singletons {n : ℕ} (f : Fin n → Bool) :
     (List.ofFn (fun i => [f i])).flatten=List.ofFn f := by
   simpa [List.flatMap,List.map_ofFn,Function.comp_def] using List.flatMap_singleton' (List.ofFn f)

 theorem entryLists_flatten (d b : ℕ) (A : Matrix) :
     (entryLists d b A).flatten = encode d b A := by
   simp only [encode, concatUpTo_ofFn, entryLists, List.flatten_flatten,
     List.map_ofFn, Function.comp_def, flatten_ofFn_singletons]

 theorem entryLists_length (d b : ℕ) (A : Matrix) : (entryLists d b A).length=d*d := by
   simp [entryLists, List.length_flatten, List.map_ofFn, Function.comp_def]

 theorem entryLists_width (d b : ℕ) (A : Matrix) :
     ∀ xs ∈ entryLists d b A, xs.length=b := by
   intro xs hx
   simp only [entryLists, List.mem_flatten, List.mem_ofFn] at hx
   obtain ⟨ys,hy,hxs⟩ := hx
   obtain ⟨i,hi⟩ := hy
   subst ys
   obtain ⟨j,hj⟩ := List.mem_ofFn.mp hxs
   subst xs
   simp

/-- The matrix with every entry extended to the right by zeros. -/
def widenMatrix (a : ℕ) (A : Matrix) : Matrix :=
  fun i j t => if t<a then A i j t else false

def expansionRecords (d a b : ℕ) (A : Matrix) : List (List Bool × List Bool) :=
  (entryLists d a A).map (fun xs => (xs,List.replicate (b-a) false))

theorem expansionRecords_lengths (d a b : ℕ) (A : Matrix) :
    ∀ r ∈ expansionRecords d a b A, r.1.length=a ∧ r.2.length=b-a := by
  intro r hr
  obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hr
  exact ⟨entryLists_width d a A xs hx, by simp⟩

theorem expansionRecords_input (d a b : ℕ) (A : Matrix) :
    NativeResizeScan.inputRows true (expansionRecords d a b A) = encode d a A := by
  simpa [NativeResizeScan.inputRows, NativeResizeScan.inputRecord,
    NativeResizeScan.consumed, expansionRecords, List.flatMap_map,
    List.flatten] using entryLists_flatten d a A

end BitWord

namespace BitWord
open Transpose

 theorem widenEntry (a b : ℕ) (hab : a≤b) (A : Matrix) (i j : ℕ) :
     List.ofFn (fun t : Fin b => widenMatrix a A i j t) =
       List.ofFn (fun t : Fin a => A i j t) ++ List.replicate (b-a) false := by
   have hlen : a+(b-a)=b := Nat.add_sub_of_le hab
   rw [← ofFn_castLength hlen (fun t : Fin b => widenMatrix a A i j t),List.ofFn_add]
   congr 1
   · apply congrArg List.ofFn
     funext t
     simp [widenMatrix,t.isLt]
   · rw [← List.ofFn_const (b-a) false]
     apply congrArg List.ofFn
     funext t
     simp [widenMatrix]

 theorem entryLists_widen (d a b : ℕ) (hab : a≤b) (A : Matrix) :
     entryLists d b (widenMatrix a A) =
       (entryLists d a A).map (fun xs => xs++List.replicate (b-a) false) := by
   simp only [entryLists,List.map_flatten,List.map_ofFn,Function.comp_def]
   apply congrArg List.flatten
   apply congrArg List.ofFn
   funext i
   apply congrArg List.ofFn
   funext j
   exact widenEntry a b hab A i j

 theorem expansionRecords_output (d a b : ℕ) (hab : a≤b) (A : Matrix) :
     NativeResizeScan.outputRows true (expansionRecords d a b A) =
       encode d b (widenMatrix a A) := by
   have he := entryLists_flatten d b (widenMatrix a A)
   rw [entryLists_widen d a b hab A] at he
   simpa [NativeResizeScan.outputRows,NativeResizeScan.outputRecord,
     NativeResizeScan.tailOutput,expansionRecords,List.flatMap_map,List.flatMap_def,Function.comp_def] using he

 theorem widen_transpose (a : ℕ) (A : Matrix) :
     transpose (widenMatrix a A)=widenMatrix a (transpose A) := rfl

 theorem widen_encode_original (d a : ℕ) (A : Matrix) :
     encode d a (widenMatrix a A)=encode d a A := by
   apply encode_eq_of_pointwise
   intro i j t _ _ ht
   simp [widenMatrix,ht]

end BitWord

namespace BitWord
open Transpose

def cropRecords (d a b : ℕ) (A : Matrix) : List (List Bool × List Bool) :=
  (entryLists d b A).map (fun xs => (xs.take a,xs.drop a))

 theorem cropRecords_lengths (d a b : ℕ) (hab : a≤b) (A : Matrix) :
     ∀ r ∈ cropRecords d a b A, r.1.length=a ∧ r.2.length=b-a := by
   intro r hr
   obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hr
   have h := entryLists_width d b A xs hx
   simp [h,Nat.min_eq_left hab]

 theorem cropRecords_input (d a b : ℕ) (A : Matrix) :
     NativeResizeScan.inputRows false (cropRecords d a b A)=encode d b A := by
   simpa [NativeResizeScan.inputRows,NativeResizeScan.inputRecord,
     NativeResizeScan.consumed,cropRecords,List.flatMap_map,List.flatMap_def,Function.comp_def] using entryLists_flatten d b A

 theorem take_entry (a b : ℕ) (hab : a≤b) (A : Matrix) (i j : ℕ) :
     (List.ofFn (fun t : Fin b => A i j t)).take a=List.ofFn (fun t : Fin a => A i j t) := by
   apply List.ext_getElem (by simp [Nat.min_eq_left hab])
   intro t ht ht'
   simp only [List.getElem_take,List.getElem_ofFn]

 theorem entryLists_take (d a b : ℕ) (hab : a≤b) (A : Matrix) :
     (entryLists d b A).map (fun xs => xs.take a)=entryLists d a A := by
   simp only [entryLists,List.map_flatten,List.map_ofFn,Function.comp_def]
   apply congrArg List.flatten
   apply congrArg List.ofFn
   funext i
   apply congrArg List.ofFn
   funext j
   exact take_entry a b hab A i j

 theorem cropRecords_output (d a b : ℕ) (hab : a≤b) (A : Matrix) :
     NativeResizeScan.outputRows false (cropRecords d a b A)=encode d a A := by
   have he := entryLists_flatten d a A
   rw [← entryLists_take d a b hab A] at he
   simpa [NativeResizeScan.outputRows,NativeResizeScan.outputRecord,
     NativeResizeScan.tailOutput,cropRecords,List.flatMap_map,List.flatMap_def,Function.comp_def] using he

 theorem expansionRecords_count (d a b : ℕ) (A : Matrix) :
     (expansionRecords d a b A).length=d*d := by
   simp [expansionRecords,entryLists_length]

 theorem cropRecords_count (d a b : ℕ) (A : Matrix) :
     (cropRecords d a b A).length=d*d := by simp [cropRecords,entryLists_length]

end BitWord
