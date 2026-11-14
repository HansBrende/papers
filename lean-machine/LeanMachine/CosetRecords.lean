import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Setoid.Basic

/-! # Exact counting from records on subgroup-invariant codes

A record need only separate subgroup cosets on the specified code. Its fibres
in the whole ambient group may be larger. The code need not be a subgroup,
and neither the code nor the alphabet of records is assumed nonempty. The
`Nat.card` identity is general; its code-counting applications use finite sets.
-/

namespace LeanMachine.CosetRecords

open scoped Pointwise

private theorem card_image_eq_of_same_fibres {X Y Z : Type*}
    (C : Set X) (f : X → Y) (g : X → Z)
    (h : ∀ x ∈ C, ∀ y ∈ C, f x = f y ↔ g x = g y) :
    Nat.card (f '' C) = Nat.card (g '' C) := by
  let f' : C → Y := fun x => f x
  let g' : C → Z := fun x => g x
  have he : ∀ x y : C, (Setoid.ker f').r x y ↔ (Setoid.ker g').r x y :=
    fun x y => h x x.property y y.property
  have e := (Setoid.quotientKerEquivRange f').symm.trans
    ((Quotient.congrRight he).trans (Setoid.quotientKerEquivRange g'))
  have hc := Nat.card_congr e
  change Nat.card (Set.range (C.domRestrict f)) =
    Nat.card (Set.range (C.domRestrict g)) at hc
  simpa only [Set.range_domRestrict] using hc

/-- Exact counting by attained records. Stability and invariance are required
only on `C`, and separation is required only between two elements of `C`.
No finiteness hypothesis is needed for the cardinal identity. -/
theorem card_eq_subgroup_mul_image {G Z : Type*} [AddCommGroup G]
    (P : AddSubgroup G) (C : Set G) (record : G → Z)
    (hstable : ∀ x ∈ C, ∀ p ∈ P, x + p ∈ C)
    (hinvariant : ∀ x ∈ C, ∀ p ∈ P, record (x + p) = record x)
    (hseparate : ∀ x ∈ C, ∀ y ∈ C, record x = record y → y - x ∈ P) :
    Nat.card C = Nat.card P * Nat.card (record '' C) := by
  have hsat : C + (P : Set G) = C := by
    ext x
    constructor
    · rintro ⟨y, hy, p, hp, rfl⟩
      exact hstable y hy p hp
    · intro hx
      exact ⟨x, hx, 0, P.zero_mem, add_zero x⟩
  have himage : Nat.card ((fun x : G => (x : G ⧸ P)) '' C) =
      Nat.card (record '' C) := by
    apply card_image_eq_of_same_fibres
    intro x hx y hy
    rw [QuotientAddGroup.eq]
    constructor
    · intro hxy
      have hp : y - x ∈ P := by simpa [sub_eq_add_neg, add_comm] using hxy
      simpa using (hinvariant x hx (y - x) hp).symm
    · intro hxy
      simpa [sub_eq_add_neg, add_comm] using hseparate x hx y hy hxy
  calc
    Nat.card C = Nat.card (C + (P : Set G)) := by rw [hsat]
    _ = Nat.card P * Nat.card ((fun x : G => (x : G ⧸ P)) '' C) :=
      P.card_add_eq_card_addSubgroup_add_card_quotient C
    _ = Nat.card P * Nat.card (record '' C) := congrArg (Nat.card P * ·) himage

/-- Forgetting which records are attained gives the usual finite-record bound.
For a record consisting of `r` alphabet symbols, `Nat.card Z` is `q ^ r`. -/
theorem card_le_subgroup_mul_card {G Z : Type*} [AddCommGroup G] [Finite Z]
    (P : AddSubgroup G) (C : Set G) (record : G → Z)
    (hstable : ∀ x ∈ C, ∀ p ∈ P, x + p ∈ C)
    (hinvariant : ∀ x ∈ C, ∀ p ∈ P, record (x + p) = record x)
    (hseparate : ∀ x ∈ C, ∀ y ∈ C, record x = record y → y - x ∈ P) :
    Nat.card C ≤ Nat.card P * Nat.card Z := by
  rw [card_eq_subgroup_mul_image P C record hstable hinvariant hseparate]
  exact Nat.mul_le_mul_left _
    (Nat.card_le_card_of_injective (Subtype.val : (record '' C) → Z) Subtype.val_injective)

end LeanMachine.CosetRecords
