import TransposeFollowup.OpcodeGeneratorMeaning
import TransposeFollowup.MatchingXorMasksSemantics

/-! Exact decoding of the generated opcode tape into the row-mask caller.
The target half is generated in descending row order and is physically
written leftward by that caller; this interface records both orders. -/
namespace TransposeFollowup.ExpanderShearOpcodeBridge
open Classical
set_option autoImplicit false

def pair : PageOpcode → Bool × Bool
  | .idle => (false,false)
  | .openEdge => (true,false)
  | .closeEdge => (true,true)

theorem pair_bits (a : PageOpcode) : [ (pair a).1, (pair a).2 ]=PageLoop.opcodeBits a := by
  cases a <;> rfl

def row {c m : ℕ} (F : Fin c → RationalMobius) (u : Fin (2*m)) : List (Bool×Bool) :=
  List.ofFn (fun p => pair (rationalPageOpcode F u p))

def sourceRows {c : ℕ} (F : Fin c → RationalMobius) (m : ℕ) : List (List (Bool×Bool)) :=
  List.ofFn (fun i : Fin m => row F (OrderedBipartite.left i))

def targetRows {c : ℕ} (F : Fin c → RationalMobius) (m : ℕ) : List (List (Bool×Bool)) :=
  List.ofFn (fun j : Fin m => row F (OrderedBipartite.right j.rev))

@[simp] theorem row_length {c m : ℕ} (F : Fin c → RationalMobius) (u : Fin (2*m)) :
    (row F u).length=rationalPageCount F := by simp [row]
@[simp] theorem sourceRows_length {c : ℕ} (F : Fin c → RationalMobius) (m : ℕ) :
    (sourceRows F m).length=m := by simp [sourceRows]
@[simp] theorem targetRows_length {c : ℕ} (F : Fin c → RationalMobius) (m : ℕ) :
    (targetRows F m).length=m := by simp [targetRows]

theorem sourceRows_width {c : ℕ} (F : Fin c → RationalMobius) (m : ℕ) :
    ∀ xs ∈ sourceRows F m, xs.length=rationalPageCount F := by
  intro xs hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact row_length F _

theorem targetRows_width {c : ℕ} (F : Fin c → RationalMobius) (m : ℕ) :
    ∀ xs ∈ targetRows F m, xs.length=rationalPageCount F := by
  intro xs hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact row_length F _

theorem encode_row {c m : ℕ} (F : Fin c → RationalMobius) (u : Fin (2*m)) :
    NativeMatchingXorMaskRow.encode (row F u)=
      (List.ofFn (rationalPageOpcode F u)).flatMap PageLoop.opcodeBits := by
  unfold NativeMatchingXorMaskRow.encode row
  simp only [List.ofFn_eq_map,List.flatMap_map,pair_bits]

theorem encoded_tape {c : ℕ} (F : Fin c → RationalMobius) (m : ℕ) :
    (rationalOpcodeTape F m).flatMap PageLoop.opcodeBits=
      NativeMatchingXorMasks.encode (sourceRows F m ++ targetRows F m) := by
  have ht : (rationalOpcodeTape F m).flatMap PageLoop.opcodeBits=
      (List.finRange (2*m)).flatMap
        (fun u => (List.ofFn (rationalPageOpcode F u)).flatMap PageLoop.opcodeBits) := by
    unfold rationalOpcodeTape rationalOpcodeTable
    simp only [List.Vector.toList_ofFn,List.flatten_eq_flatMap,
      List.flatMap_assoc,List.flatMap_map,List.ofFn_eq_map,Function.comp_def,List.map_map,id_eq]
  rw [ht,←VertexScheduler.vertex_order m,List.flatMap_append]
  unfold NativeMatchingXorMasks.encode sourceRows targetRows
  rw [List.flatMap_append]
  simp only [List.ofFn_eq_map,List.flatMap_map,encode_row]

theorem flags_source {c : ℕ} (F : Fin c → RationalMobius) (m : ℕ)
    (p : Fin (rationalPageCount F)) :
    MatchingXorMasksSemantics.flags (sourceRows F m) p=
      (List.finRange m).map (fun i => rationalOutgoingOn F i p) := by
  unfold MatchingXorMasksSemantics.flags sourceRows
  rw [List.map_ofFn,←List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext i
  cases h : rationalOutgoingOn F i p <;> simp [row,List.getD,rationalPageOpcode_left,h,pair]

theorem flags_target_reverse {c : ℕ} (F : Fin c → RationalMobius) (m : ℕ)
    (p : Fin (rationalPageCount F)) :
    (MatchingXorMasksSemantics.flags (targetRows F m) p).reverse=
      (List.finRange m).map (fun j => rationalIncomingOn F j p) := by
  unfold MatchingXorMasksSemantics.flags targetRows
  rw [List.map_ofFn,VertexScheduler.reverse_ofFn,←List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext j
  cases h : rationalIncomingOn F j p <;> simp [row,List.getD,rationalPageOpcode_right,h,pair]

end TransposeFollowup.ExpanderShearOpcodeBridge
