import LeanMachine.DisjointSumsWeighted

/-! # Pinned coordinates as singleton parity blocks

Adjoin a singleton block at every coordinate on which kernel shifts must
vanish. Recording these singletons is equivalent to recording the raw
coordinates, even with arbitrary invertible coordinate weights. The existing
weighted compatibility and separation theorem then applies without granting
any additional shifts. The finite bound charges pinned coordinates exactly.
-/

namespace LeanMachine.DisjointSums

open scoped Classical
noncomputable section

variable {ι κ A : Type*} (D : DisjointSums ι κ) (E : Set ι)
variable (hfree : ∀ k, ∀ i ∈ E, i ∉ D.support k)

/-- Add one singleton sum for each pinned coordinate, outside the active blocks. -/
def withPins : DisjointSums ι (κ ⊕ E) where
  support := Sum.elim D.support (fun e => {e.val})
  nonempty := by
    intro k
    cases k with
    | inl k => exact D.nonempty k
    | inr e => exact Finset.singleton_nonempty e.val
  disjoint := by
    intro k l hkl
    cases k with
    | inl k =>
      cases l with
      | inl l => exact D.disjoint (fun h => hkl (congrArg Sum.inl h))
      | inr e =>
        exact Finset.disjoint_singleton_right.mpr (hfree k e.val e.property)
    | inr e =>
      cases l with
      | inl l =>
        exact Finset.disjoint_singleton_left.mpr (hfree l e.val e.property)
      | inr f =>
        exact Finset.disjoint_singleton.mpr
          (fun h => hkl (congrArg Sum.inr (Subtype.ext h)))

variable [AddCommGroup A] (θ : ι → A ≃+ A)

@[simp] theorem withPins_encode_left (x : ι → A) (k : κ) :
    (D.withPins E hfree).weightedEncode θ x (Sum.inl k) =
      D.weightedEncode θ x k := rfl

@[simp] theorem withPins_encode_right (x : ι → A) (e : E) :
    (D.withPins E hfree).weightedEncode θ x (Sum.inr e) = θ e (x e) := by
  simp [weightedEncode_apply, encode_apply, withPins]

/-- The augmented kernel is exactly the active kernel with zero pinned values. -/
theorem withPins_encode_eq_zero_iff (z : ι → A) :
    (D.withPins E hfree).weightedEncode θ z = 0 ↔
      D.weightedEncode θ z = 0 ∧ Set.EqOn z 0 E := by
  constructor
  · intro h
    constructor
    · funext k
      exact congrFun h (Sum.inl k)
    · intro i hi
      have h' := congrFun h (Sum.inr ⟨i, hi⟩)
      simpa using h'
  · rintro ⟨h, hz⟩
    funext k
    cases k with
    | inl k => exact congrFun h k
    | inr e => simp [hz e.property]

/-- The record keeps raw pinned values and the selected active syndromes. -/
def pinnedRecord (T : Set κ) (x : ι → A) : (E → A) × (T → A) :=
  (fun e => x e, D.weightedSyndromeRecord θ T x)

variable (C : Set (ι → A))
variable (hstable : ∀ x ∈ C, ∀ z : ι → A,
  D.weightedEncode θ z = 0 → Set.EqOn z 0 E → x + z ∈ C)

include hstable in
/-- Raw pinned values plus selected active syndromes separate augmented cosets.
Only the original active blocks need satisfy the two enclosure conditions. -/
theorem withPins_encode_eq_of_recovery [Finite κ] [Finite E]
    (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i k, (↑(D.support k) : Set ι) ⊆ H i → k ∈ T)
    (hincident : ∀ k, (∀ i ∈ D.support k, i ∈ H i) → k ∈ T)
    {x y : ι → A} (hx : x ∈ C) (hy : y ∈ C)
    (hrecord : D.pinnedRecord E θ T x = D.pinnedRecord E θ T y) :
    (D.withPins E hfree).weightedEncode θ x =
      (D.withPins E hfree).weightedEncode θ y := by
  let T' : Set (κ ⊕ E) := {k | Sum.elim (fun k => k ∈ T) (fun _ => True) k}
  apply (D.withPins E hfree).weighted_encode_eq_of_invariant_recovery θ C
    (fun x hx z hz =>
      let h := (D.withPins_encode_eq_zero_iff E hfree θ z).mp hz
      hstable x hx z h.1 h.2) H T' hrecover
  · intro i k hk
    cases k with
    | inl k => exact hinternal i k hk
    | inr e => trivial
  · intro k hk
    cases k with
    | inl k => exact hincident k hk
    | inr e => trivial
  · exact hx
  · exact hy
  · intro k hk
    cases k with
    | inl k => exact congrFun (congrArg Prod.snd hrecord) ⟨k, hk⟩
    | inr e =>
      simp only [withPins_encode_right]
      exact congrArg (θ e) (congrFun (congrArg Prod.fst hrecord) e)

include hstable in
/-- Exact attained-record count for active shifts that fix prescribed coordinates. -/
theorem card_eq_pinned_kernel_mul_record_image [Finite κ] [Finite E]
    (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i k, (↑(D.support k) : Set ι) ⊆ H i → k ∈ T)
    (hincident : ∀ k, (∀ i ∈ D.support k, i ∈ H i) → k ∈ T) :
    Nat.card C = Nat.card ((D.withPins E hfree).weightedEncode θ).ker *
      Nat.card (D.pinnedRecord E θ T '' C) := by
  apply CosetRecords.card_eq_subgroup_mul_image
    ((D.withPins E hfree).weightedEncode θ).ker C (D.pinnedRecord E θ T)
  · intro x hx z hz
    have h := (D.withPins_encode_eq_zero_iff E hfree θ z).mp hz
    exact hstable x hx z h.1 h.2
  · intro x hx z hz
    have h := (D.withPins_encode_eq_zero_iff E hfree θ z).mp hz
    apply Prod.ext
    · funext e
      exact add_eq_left.mpr (h.2 e.property)
    · funext k
      change D.weightedEncode θ (x + z) k = D.weightedEncode θ x k
      rw [map_add, h.1, add_zero]
  · intro x hx y hy hrecord
    change (D.withPins E hfree).weightedEncode θ (y - x) = 0
    rw [map_sub, D.withPins_encode_eq_of_recovery E hfree θ C hstable H T
      hrecover hinternal hincident hx hy hrecord, sub_self]

/-- The pinned kernel has one independent constraint per active block and pin. -/
theorem card_pinned_kernel [Fintype ι] [Fintype κ] [Fintype A] :
    Nat.card ((D.withPins E hfree).weightedEncode θ).ker =
      Fintype.card A ^ (Fintype.card ι - (Fintype.card κ + Nat.card E)) := by
  classical
  simpa only [Fintype.card_sum, Nat.card_eq_fintype_card] using
    (D.withPins E hfree).card_weighted_kernel θ

include hstable hfree in
/-- Recording pins restores exactly their lost kernel dimensions. Thus the
finite exponent uses the number of active blocks, without a second pin charge. -/
theorem card_le_pow_of_pinned_invariant_recovery
    [Fintype ι] [Fintype κ] [Fintype A]
    (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i k, (↑(D.support k) : Set ι) ⊆ H i → k ∈ T)
    (hincident : ∀ k, (∀ i ∈ D.support k, i ∈ H i) → k ∈ T) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card ι - Fintype.card κ + Nat.card T) := by
  classical
  rw [D.card_eq_pinned_kernel_mul_record_image E hfree θ C hstable H T
    hrecover hinternal hincident, D.card_pinned_kernel E hfree θ]
  have hrec := Nat.card_le_card_of_injective
    (Subtype.val : (D.pinnedRecord E θ T '' C) → (E → A) × (T → A))
    Subtype.val_injective
  have hbound := Nat.mul_le_mul_left
    (Fintype.card A ^ (Fintype.card ι - (Fintype.card κ + Nat.card E))) hrec
  have hsize := (D.withPins E hfree).card_le
  simp only [Fintype.card_sum, ← Nat.card_eq_fintype_card (α := E)] at hsize
  convert hbound using 1
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, ← pow_add]
  congr 1
  simpa only [Nat.card_eq_fintype_card] using
    (show Fintype.card ι - Fintype.card κ + Nat.card T =
      Fintype.card ι - (Fintype.card κ + Nat.card E) +
        (Nat.card E + Nat.card T) by omega)

end
end LeanMachine.DisjointSums
