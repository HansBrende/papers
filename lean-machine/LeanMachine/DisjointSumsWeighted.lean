import LeanMachine.DisjointSumsCompatibility
import Mathlib.Algebra.Group.Equiv.Basic

/-! # Weighted parity records by a coordinate change

Coordinatewise additive automorphisms preserve equality on every coordinate
view. Transporting the code through `AddEquiv.piCongrRight` therefore reduces
weighted kernel invariance, compatibility, and record separation to the
ordinary disjoint-sum results. No recovery or extension proof is repeated.
-/

namespace LeanMachine.DisjointSums

open scoped Classical

variable {ι κ A : Type*} [AddCommGroup A]
variable (D : DisjointSums ι κ) (θ : ι → A ≃+ A)

/-- The ordinary block encoder after a coordinatewise additive automorphism. -/
def weightedEncode : (ι → A) →+ (κ → A) :=
  D.encode.comp (AddEquiv.piCongrRight θ).toAddMonoidHom

@[simp] theorem weightedEncode_apply (x : ι → A) :
    D.weightedEncode θ x = D.encode (fun i => θ i (x i)) := rfl

/-- Coordinate automorphisms preserve surjectivity of the block encoder. -/
theorem weightedEncode_surjective [Fintype κ] :
    Function.Surjective (D.weightedEncode θ) :=
  D.encode_surjective.comp (AddEquiv.piCongrRight θ).surjective

/-- Every weighted fibre has exactly the expected finite number of words. -/
theorem weighted_fiber_card [Fintype ι] [Fintype κ] [Fintype A]
    (y : κ → A) :
    (Finset.univ.filter fun x : ι → A => D.weightedEncode θ x = y).card =
      Fintype.card A ^ (Fintype.card ι - Fintype.card κ) := by
  classical
  have h := card_fiber_mul_card (D.weightedEncode θ) (D.weightedEncode_surjective θ) y
  rw [Fintype.card_fun, Fintype.card_fun] at h
  have hp : 0 < Fintype.card A ^ Fintype.card κ := pow_pos Fintype.card_pos _
  apply Nat.eq_of_mul_eq_mul_right hp
  rw [h, ← pow_add, Nat.sub_add_cancel D.card_le]

/-- Finite kernel size, with the alphabet and both index types explicitly finite. -/
theorem card_weighted_kernel [Fintype ι] [Fintype κ] [Fintype A] :
    Nat.card (D.weightedEncode θ).ker =
      Fintype.card A ^ (Fintype.card ι - Fintype.card κ) := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, AddMonoidHom.mem_ker] using
    D.weighted_fiber_card θ (0 : κ → A)

variable (C : Set (ι → A))
variable (hstable : ∀ x ∈ C, ∀ z : ι → A, D.weightedEncode θ z = 0 → x + z ∈ C)

include hstable in
private theorem image_kernel_stable :
    ∀ u ∈ (AddEquiv.piCongrRight θ) '' C, ∀ z : ι → A,
      D.encode z = 0 → u + z ∈ (AddEquiv.piCongrRight θ) '' C := by
  rintro u ⟨x, hx, rfl⟩ z hz
  refine ⟨x + (AddEquiv.piCongrRight θ).symm z, hstable x hx _ ?_, ?_⟩
  · change D.encode ((AddEquiv.piCongrRight θ) ((AddEquiv.piCongrRight θ).symm z)) = 0
    simpa only [AddEquiv.apply_symm_apply] using hz
  · simp only [map_add, AddEquiv.apply_symm_apply]

private theorem recovery_image (S : Set ι) (i : ι)
    (hrecover : ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v S → u i = v i) :
    ∀ u ∈ (AddEquiv.piCongrRight θ) '' C,
    ∀ v ∈ (AddEquiv.piCongrRight θ) '' C,
      Set.EqOn u v S → u i = v i := by
  rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩ hview
  change θ i (x i) = θ i (y i)
  apply congrArg (θ i)
  apply hrecover x hx y hy
  intro j hj
  exact (θ j).injective (hview hj)

include hstable in
/-- Weighted compatibility is the ordinary compatibility theorem on the
coordinate-transformed code. The block index need not be finite. -/
theorem weighted_support_subset_insert_of_recovery [Nontrivial A] (hC : C.Nonempty)
    (S : Set ι) (i : ι)
    (hrecover : ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v S → u i = v i)
    (hiS : i ∉ S) (k : κ) (hik : i ∈ D.support k) :
    (↑(D.support k) : Set ι) ⊆ insert i S := by
  exact D.support_subset_insert_of_recovery ((AddEquiv.piCongrRight θ) '' C)
    (D.image_kernel_stable θ C hstable) (hC.image (AddEquiv.piCongrRight θ))
    S i (recovery_image θ C S i hrecover) hiS k hik

include hstable in
/-- A free coordinate of a weighted parity template must belong to its
recovery view. No finiteness assumption is used. -/
theorem weighted_mem_view_of_free [Nontrivial A] (hC : C.Nonempty)
    (S : Set ι) (i : ι)
    (hrecover : ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v S → u i = v i)
    (hfree : ∀ k, i ∉ D.support k) : i ∈ S := by
  exact D.mem_view_of_free ((AddEquiv.piCongrRight θ) '' C)
    (D.image_kernel_stable θ C hstable) (hC.image (AddEquiv.piCongrRight θ))
    S i (recovery_image θ C S i hrecover) hfree

include hstable in
/-- Selected weighted syndromes determine all weighted syndromes on a code
invariant under the weighted kernel. Empty codes and trivial groups are
allowed; the fully-viewed and all-incident enclosure conditions are unchanged. -/
theorem weighted_encode_eq_of_invariant_recovery [Finite κ]
    (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i k, (↑(D.support k) : Set ι) ⊆ H i → k ∈ T)
    (hincident : ∀ k, (∀ i ∈ D.support k, i ∈ H i) → k ∈ T)
    {x y : ι → A} (hx : x ∈ C) (hy : y ∈ C)
    (hrecord : Set.EqOn (D.weightedEncode θ x) (D.weightedEncode θ y) T) :
    D.weightedEncode θ x = D.weightedEncode θ y := by
  exact D.encode_eq_of_invariant_recovery ((AddEquiv.piCongrRight θ) '' C)
    (D.image_kernel_stable θ C hstable) H T
    (fun i => recovery_image θ C (H i) i (hrecover i)) hinternal hincident
    (Set.mem_image_of_mem (AddEquiv.piCongrRight θ) hx)
    (Set.mem_image_of_mem (AddEquiv.piCongrRight θ) hy) hrecord

/-- The attained-record map indexed by the selected weighted parity blocks. -/
def weightedSyndromeRecord (T : Set κ) (x : ι → A) : T → A :=
  fun k => D.weightedEncode θ x k

include hstable in
/-- Exact weighted kernel-times-attained-record count. This is a general
`Nat.card` identity; finite code-size applications supply finiteness. -/
theorem card_eq_weighted_kernel_mul_record_image_of_recovery [Finite κ]
    (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i k, (↑(D.support k) : Set ι) ⊆ H i → k ∈ T)
    (hincident : ∀ k, (∀ i ∈ D.support k, i ∈ H i) → k ∈ T) :
    Nat.card C = Nat.card (D.weightedEncode θ).ker *
      Nat.card (D.weightedSyndromeRecord θ T '' C) := by
  apply CosetRecords.card_eq_subgroup_mul_image
    (D.weightedEncode θ).ker C (D.weightedSyndromeRecord θ T)
  · intro x hx z hz
    exact hstable x hx z hz
  · intro x hx z hz
    have hz' : D.weightedEncode θ z = 0 := hz
    funext k
    change D.weightedEncode θ (x + z) k = D.weightedEncode θ x k
    rw [map_add, hz', add_zero]
  · intro x hx y hy hrecord
    change D.weightedEncode θ (y - x) = 0
    have heq := D.weighted_encode_eq_of_invariant_recovery θ C hstable H T
      hrecover hinternal hincident hx hy (fun k hk => congrFun hrecord ⟨k, hk⟩)
    rw [map_sub, heq, sub_self]

include hstable in
/-- Finite-record corollary of the attained-image identity. -/
theorem card_le_pow_of_weighted_invariant_recovery
    [Fintype ι] [Fintype κ] [Fintype A]
    (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i k, (↑(D.support k) : Set ι) ⊆ H i → k ∈ T)
    (hincident : ∀ k, (∀ i ∈ D.support k, i ∈ H i) → k ∈ T) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card ι - Fintype.card κ + Nat.card T) := by
  classical
  rw [D.card_eq_weighted_kernel_mul_record_image_of_recovery θ C hstable H T
    hrecover hinternal hincident, D.card_weighted_kernel θ, pow_add]
  apply Nat.mul_le_mul_left
  have h := Nat.card_le_card_of_injective
    (Subtype.val : (D.weightedSyndromeRecord θ T '' C) → (T → A)) Subtype.val_injective
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fun] using h

end LeanMachine.DisjointSums
