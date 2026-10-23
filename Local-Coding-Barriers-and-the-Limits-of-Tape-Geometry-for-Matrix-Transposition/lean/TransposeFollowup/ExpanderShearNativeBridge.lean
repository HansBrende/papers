import TransposeFollowup.ExpanderShear
import TransposeFollowup.ExpanderShearRowStream

/-! Exact semantics of increasing matching pages. Masks select rows in their
native order; the actual stream pairing defines the incidence matrix. -/
namespace TransposeFollowup.ExpanderShear
open scoped BigOperators
open ExpanderShearRowStream MatchingXorStream
set_option autoImplicit false

abbrev BoolBank (m W : ℕ) := Row m → Word W

def selectedIndices {m : ℕ} (a : Fin m → Bool) : List (Fin m) :=
  (List.finRange m).filter a

def maskSource {m : ℕ} (a b : Fin m → Bool) : Fin m → Option (Fin m) :=
  pairSource (selectedIndices a) (selectedIndices b)

def maskMatrix {m : ℕ} (a b : Fin m → Bool) : Matrix (Fin m) (Fin m) Bit :=
  fun j i => match maskSource a b j with
    | none => 0
    | some k => if k = i then 1 else 0

def rawHalf {m W : ℕ} (A : Fin m → Word W) : List Bool :=
  rawWords ((List.finRange m).map A)

def taggedHalf {m W : ℕ} (a : Fin m → Bool) (A : Fin m → Word W) : List Record :=
  records ((List.finRange m).map (fun i => (a i, A i)))

@[simp] theorem rawHalf_length {m W : ℕ} (A : Fin m → Word W) :
    (rawHalf A).length = m * W := by simp [rawHalf]

@[simp] theorem taggedHalf_values {m W : ℕ} (a : Fin m → Bool) (A : Fin m → Word W) :
    values (taggedHalf a A) = rawHalf A := by
  simp only [taggedHalf, values_records, List.map_map, Function.comp_def, rawHalf]

@[simp] theorem taggedHalf_tags {m W : ℕ} (a : Fin m → Bool) (A : Fin m → Word W) :
    tags (taggedHalf a A) = (List.finRange m).flatMap (fun i => List.replicate W (a i)) := by
  simp [taggedHalf, tags_records, List.flatMap_map]

@[simp] theorem taggedHalf_length {m W : ℕ} (a : Fin m → Bool) (A : Fin m → Word W) :
    (taggedHalf a A).length = m * W := by
  have h := congrArg List.length (taggedHalf_values a A)
  simpa [values] using h

noncomputable def boolShear {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit) (x : BoolBank m W) : BoolBank m W :=
  fun r w => boolEquiv.symm (shear L (fun r w => ofBool (x r w)) r w)

@[simp] theorem ofBool_boolShear {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (x : BoolBank m W) (r : Row m) (w : Fin W) :
    ofBool (boolShear L x r w) = shear L (fun r w => ofBool (x r w)) r w := by
  exact boolEquiv.apply_symm_apply _

@[simp] theorem boolShear_left {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (x : BoolBank m W) (i : Fin m) : boolShear L x (.inl i) = x (.inl i) := by
  funext w
  apply ofBool_injective
  simp

theorem maskMatrix_sum {m : ℕ} (a b : Fin m → Bool) (A : Fin m → Bit) (j : Fin m) :
    (∑ i, maskMatrix a b j i * A i) =
      match maskSource a b j with | none => 0 | some i => A i := by
  cases h : maskSource a b j with
  | none => simp [maskMatrix, h]
  | some i => simp [maskMatrix, h]

theorem pairedUpdate_eq_boolShear {m W : ℕ} (a b : Fin m → Bool) (x : BoolBank m W)
    (j : Fin m) :
    pairedUpdate (selectedIndices a) (selectedIndices b)
      (fun i => x (.inl i)) (fun i => x (.inr i)) j = boolShear (maskMatrix a b) x (.inr j) := by
  funext w
  apply ofBool_injective
  rw [ofBool_boolShear, shear_right, maskMatrix_sum]
  dsimp only [pairedUpdate, maskSource]
  cases h : pairSource (selectedIndices a) (selectedIndices b) j <;>
    simp [wordXor, ofBool_xor, add_comm]

/-- Exact native page semantics, including unselected target rows. -/
theorem mask_page_stream_eq_shear {m W : ℕ} (a b : Fin m → Bool)
    (hlen : (selectedIndices a).length = (selectedIndices b).length) (x : BoolBank m W) :
    MatchingXorStream.apply
      (selected (taggedHalf a (fun i => x (.inl i))))
      (taggedHalf b (fun i => x (.inr i))) =
    rawHalf (fun j => boolShear (maskMatrix a b) x (.inr j)) := by
  unfold taggedHalf
  rw [selected_records, selectedRows_map]
  rw [apply_records]
  · rw [applyRows_eq_paired _ _ (List.nodup_finRange m)]
    · apply congrArg rawWords
      apply List.map_congr_left
      intro j _
      exact pairedUpdate_eq_boolShear a b x j
    · simpa only [List.length_map, selectedIndices] using hlen
  · rw [selectedRows_map]
    simpa only [List.length_map, selectedIndices] using hlen

/-- The native page's equal-length premise follows from matched row counts. -/
theorem mask_page_selected_lengths {m W : ℕ} (a b : Fin m → Bool)
    (hlen : (selectedIndices a).length = (selectedIndices b).length)
    (A B : Fin m → Word W) :
    (selected (taggedHalf a A)).length = (selected (taggedHalf b B)).length := by
  simp only [taggedHalf, selected_records, selectedRows_map, rawWords_length, List.length_map]
  exact congrArg (fun n => n * W) hlen

theorem shear_add_comp {m W : ℕ} (L K : Matrix (Fin m) (Fin m) Bit) (x : Bank m W) :
    shear K (shear L x) = shear (L + K) x := by
  funext r w
  cases r with
  | inl i => rfl
  | inr j =>
    simp only [shear, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    ring

@[simp] theorem shear_zero {m W : ℕ} (x : Bank m W) : shear 0 x = x := by
  funext r w
  cases r <;> simp [shear]

theorem shear_fold {m W : ℕ} (Ls : List (Matrix (Fin m) (Fin m) Bit)) (x : Bank m W) :
    Ls.foldl (fun y L => shear L y) x = shear Ls.sum x := by
  induction Ls generalizing x with
  | nil => simp
  | cons L Ls ih => simp only [List.foldl_cons, ih, shear_add_comp, List.sum_cons]

theorem boolShear_add_comp {m W : ℕ} (L K : Matrix (Fin m) (Fin m) Bit) (x : BoolBank m W) :
    boolShear K (boolShear L x) = boolShear (L + K) x := by
  funext r w
  apply ofBool_injective
  simp only [ofBool_boolShear]
  exact congrFun (congrFun (shear_add_comp L K (fun r w => ofBool (x r w))) r) w

@[simp] theorem boolShear_zero {m W : ℕ} (x : BoolBank m W) : boolShear 0 x = x := by
  funext r w
  apply ofBool_injective
  simp

theorem boolShear_fold {m W : ℕ} (Ls : List (Matrix (Fin m) (Fin m) Bit)) (x : BoolBank m W) :
    Ls.foldl (fun y L => boolShear L y) x = boolShear Ls.sum x := by
  induction Ls generalizing x with
  | nil => simp
  | cons L Ls ih => simp only [List.foldl_cons, ih, boolShear_add_comp, List.sum_cons]

/-- Target/source pairs in the order actually visited by one native page. -/
def maskEdges {m : ℕ} (a b : Fin m → Bool) : List (Fin m × Fin m) :=
  (selectedIndices b).zip (selectedIndices a)

theorem maskMatrix_eq_incidence {m : ℕ} (a b : Fin m → Bool) (j i : Fin m) :
    maskMatrix a b j i = if (j, i) ∈ maskEdges a b then 1 else 0 := by
  have he := pairSource_some_iff (selectedIndices a) (selectedIndices b)
    ((List.nodup_finRange m).filter b) j i
  change maskSource a b j = some i ↔ (j, i) ∈ maskEdges a b at he
  by_cases hm : (j, i) ∈ maskEdges a b
  · have hs := he.mpr hm
    simp [maskMatrix, hs, hm]
  · have hn : maskSource a b j ≠ some i := fun h => hm (he.mp h)
    cases hs : maskSource a b j with
    | none => simp [maskMatrix, hs, hm]
    | some k =>
      have hk : k ≠ i := fun h => hn (hs.trans (congrArg some h))
      simp [maskMatrix, hs, hm, hk]

/-- Edge-disjoint pages implement the simple union adjacency, without
characteristic-two cancellation. The disjointness is checked on actual pairs. -/
theorem maskMatrices_sum_eq_union {m : ℕ}
    (pages : List ((Fin m → Bool) × (Fin m → Bool)))
    (hnodup : (pages.flatMap (fun p => maskEdges p.1 p.2)).Nodup) :
    (pages.map (fun p => maskMatrix p.1 p.2)).sum =
      fun j i => if (j, i) ∈ pages.flatMap (fun p => maskEdges p.1 p.2) then 1 else 0 := by
  induction pages with
  | nil => funext j i; simp
  | cons p pages ih =>
    rw [List.flatMap_cons] at hnodup
    obtain ⟨_, ht, hd⟩ := List.nodup_append.mp hnodup
    rw [List.map_cons, List.sum_cons, ih ht]
    funext j i
    change maskMatrix p.1 p.2 j i +
      (if (j, i) ∈ pages.flatMap (fun p => maskEdges p.1 p.2) then 1 else 0) = _
    simp only [maskMatrix_eq_incidence, List.flatMap_cons, List.mem_append]
    by_cases hh : (j, i) ∈ maskEdges p.1 p.2
    · have hn : (j, i) ∉ pages.flatMap (fun p => maskEdges p.1 p.2) := by
        exact fun h => hd _ hh _ h rfl
      simp [hh, hn]
    · simp [hh]

end TransposeFollowup.ExpanderShear
