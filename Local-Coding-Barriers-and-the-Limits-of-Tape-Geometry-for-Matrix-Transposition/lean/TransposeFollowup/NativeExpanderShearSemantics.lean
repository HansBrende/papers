import TransposeFollowup.NativeMatchingXorPages
import TransposeFollowup.ExpanderShearRationalBridge
import TransposeFollowup.ExpanderShearOpcodeBridge
import Mathlib.Algebra.BigOperators.Fin

/-! Connect the actual successive native page applications to the shear
matrix of the generated rational matching family. -/
namespace TransposeFollowup.NativeExpanderShearSemantics
open ExpanderShear MatchingXorStream
open scoped BigOperators
set_option autoImplicit false

def tagBits {m : ℕ} (W : ℕ) (a : Fin m → Bool) : List Bool :=
  (List.finRange m).flatMap (fun i => List.replicate W (a i))

@[simp] theorem tagBits_length {m : ℕ} (W : ℕ) (a : Fin m → Bool) :
    (tagBits W a).length=m*W := by simp [tagBits]

theorem zip_tagged {m W : ℕ} (a : Fin m → Bool) (A : Fin m → ExpanderShearRowStream.Word W) :
    (tagBits W a).zip (rawHalf A)=taggedHalf a A := by
  exact (List.zip_of_prod (taggedHalf_tags a A) (taggedHalf_values a A)).symm

theorem tagBits_expanded {m : ℕ} (W : ℕ) (a : Fin m → Bool) :
    NativeMatchingXorTagStream.expanded W ((List.finRange m).map a)=tagBits W a := by
  simp [NativeMatchingXorTagStream.expanded,tagBits,List.flatMap_map]

theorem page_eq_shear {m W : ℕ} (a b : Fin m → Bool)
    (hlen : (selectedIndices a).length=(selectedIndices b).length) (x : BoolBank m W) :
    NativeMatchingXorPages.page (rawHalf (fun i => x (.inl i))) (rawHalf (fun j => x (.inr j)))
      (tagBits W a) (tagBits W b)=rawHalf (fun j => boolShear (maskMatrix a b) x (.inr j)) := by
  rw [NativeMatchingXorPages.page,zip_tagged,zip_tagged]
  exact mask_page_stream_eq_shear a b hlen x

theorem valid_tags {q m W : ℕ} (a b : Fin q → Fin m → Bool)
    (hlen : ∀p,(selectedIndices (a p)).length=(selectedIndices (b p)).length) (x : BoolBank m W) :
    NativeMatchingXorPages.ValidTags (rawHalf (fun i => x (.inl i))).length
      (fun p => tagBits W (a p)) (fun p => tagBits W (b p)) := by
  intro p
  refine ⟨by simp,by simp,?_⟩
  have hc := mask_page_selected_lengths (a p) (b p) (hlen p)
    (fun i => x (.inl i)) (fun j => x (.inr j))
  rw [NativeMatchingXorPages.selected_length_tags,NativeMatchingXorPages.selected_length_tags] at hc
  simpa only [taggedHalf_tags,tagBits] using hc

theorem output_partial {q m W : ℕ} (a b : Fin q → Fin m → Bool)
    (hlen : ∀p,(selectedIndices (a p)).length=(selectedIndices (b p)).length) (x : BoolBank m W)
    (n : ℕ) (hn : n≤q) :
    NativeMatchingXorPages.output (rawHalf (fun i => x (.inl i))) (rawHalf (fun j => x (.inr j)))
      (fun p => tagBits W (a p)) (fun p => tagBits W (b p)) n =
      rawHalf (fun j => boolShear ((List.ofFn (fun p => maskMatrix (a p) (b p))).take n).sum x (.inr j)) := by
  induction n with
  | zero => simp [NativeMatchingXorPages.output]
  | succ n ih =>
    have hlt : n<q := by omega
    rw [NativeMatchingXorPages.output,dite_eq_left hlt,ih (by omega)]
    let L := ((List.ofFn (fun p => maskMatrix (a p) (b p))).take n).sum
    have ha : rawHalf (fun i => x (.inl i))=rawHalf (fun i => boolShear L x (.inl i)) := by simp
    rw [ha,page_eq_shear (a ⟨n,hlt⟩) (b ⟨n,hlt⟩) (hlen ⟨n,hlt⟩),boolShear_add_comp]
    have hget : n < (List.ofFn (fun p => maskMatrix (a p) (b p))).length := by simpa using hlt
    rw [List.sum_take_succ _ _ hget]
    simp [L]

theorem output_eq_shear {q m W : ℕ} (a b : Fin q → Fin m → Bool)
    (hlen : ∀p,(selectedIndices (a p)).length=(selectedIndices (b p)).length) (x : BoolBank m W) :
    NativeMatchingXorPages.output (rawHalf (fun i => x (.inl i))) (rawHalf (fun j => x (.inr j)))
      (fun p => tagBits W (a p)) (fun p => tagBits W (b p)) q =
      rawHalf (fun j => boolShear (∑p,maskMatrix (a p) (b p)) x (.inr j)) := by
  have he := output_partial a b hlen x q (le_refl q)
  rw [List.take_of_length_le (by simp),List.sum_ofFn] at he
  exact he

theorem rational_output {r m W : ℕ} (F : Fin (r+1) → RationalMobius) (x : BoolBank m W) :
    NativeMatchingXorPages.output (rawHalf (fun i => x (.inl i))) (rawHalf (fun j => x (.inr j)))
      (fun p => tagBits W (fun i : Fin m => rationalOutgoingOn F i p))
      (fun p => tagBits W (fun j : Fin m => rationalIncomingOn F j p)) (rationalPageCount F) =
      rawHalf (fun j => boolShear
        (fun j i => if (i,j) ∈ overlapEdges (rationalFamilyMaps F) m then 1 else 0) x (.inr j)) := by
  rw [output_eq_shear _ _ (fun p => (rational_page_masks F p).1),rational_page_matrix_sum]

end TransposeFollowup.NativeExpanderShearSemantics
