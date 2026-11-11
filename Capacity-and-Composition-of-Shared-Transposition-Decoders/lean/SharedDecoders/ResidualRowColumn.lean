import SharedDecoders.Model
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic

/-! # Sharp arbitrary row-then-column agreement

The families are arbitrary functions. A lower-triangle injection is proved
from the actual complete row/column computation; no injectivity of either
family is assumed.
-/

namespace SharedDecoders.RowColumn

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {A : Type*}

abbrev Mat (d : ℕ) (A : Type*) := Fin d → Fin d → A
abbrev Family (d : ℕ) (A : Type*) := Fin d → (Fin d → A) → (Fin d → A)

def intermediate (R : Family d A) (X : Mat d A) : Mat d A := fun i => R i (X i)

def complete (R C : Family d A) (X : Mat d A) : Mat d A :=
  fun i j => C j (fun k => intermediate R X k j) i

def Agreement (R C : Family d A) : Set (Mat d A) :=
  {X | complete R C X = fun i j => X j i}

/-- One coordinate for each unordered pair, read from the lower triangle. -/
def triangle (X : Mat d A) : Sym2 (Fin d) → A :=
  Sym2.lift ⟨fun i j => X (max i j) (min i j), by
    intro i j
    change X (max i j) (min i j) = X (max j i) (min j i)
    rw [max_comm, min_comm]⟩

@[simp] theorem triangle_pair (X : Mat d A) (i j : Fin d) :
    triangle X s(i,j) = X (max i j) (min i j) := rfl

/-- Recover columns and then rows in increasing order from the actual lower triangle. -/
theorem triangle_injective_of_rows (f : Family d A) {Y Z : Mat d A}
    (hY : ∀ i, Y i = f i (fun k => Y k i))
    (hZ : ∀ i, Z i = f i (fun k => Z k i)) (htri : triangle Y = triangle Z) : Y = Z := by
  have hr (n : ℕ) : ∀ i : Fin d, i.val = n → Y i = Z i := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      rw [hY i, hZ i]
      apply congrArg (f i)
      funext j
      by_cases hij : i ≤ j
      · have h := congrFun htri s(i,j)
        simpa only [triangle_pair, max_eq_right hij, min_eq_left hij] using h
      · have hji : j.val < n := by have := lt_of_not_ge hij; omega
        exact congrFun (ih j.val hji j rfl) i
  funext i
  exact hr i.val i rfl

theorem agreement_row {R C : Family d A} {X : Mat d A} (hX : X ∈ Agreement R C) (j : Fin d) :
    X j = C j (fun k => intermediate R X k j) := by
  funext i
  exact (congrFun (congrFun hX i) j).symm

/-- The lower triangle of the intermediate matrix determines each agreement input. -/
theorem agreement_encoding_injective (R C : Family d A) :
    Function.Injective (fun X : Agreement R C => triangle (intermediate R X.val)) := by
  intro X Z h
  have hi : intermediate R X.val = intermediate R Z.val :=
    triangle_injective_of_rows (fun i => R i ∘ C i)
      (fun i => congrArg (R i) (agreement_row X.property i))
      (fun i => congrArg (R i) (agreement_row Z.property i)) h
  apply Subtype.ext
  funext i
  rw [agreement_row X.property i, agreement_row Z.property i, hi]

theorem sym2_card (d : ℕ) : Fintype.card (Sym2 (Fin d)) = d * (d + 1) / 2 := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

/-- The exact triangular exponent, for arbitrary fixed deterministic families. -/
theorem agreement_card_le [Fintype A] (R C : Family d A) :
    Nat.card (Agreement R C) ≤ Fintype.card A ^ (d * (d + 1) / 2) := by
  have h := Nat.card_le_card_of_injective _ (agreement_encoding_injective R C)
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fun, sym2_card] using h

/-- Symmetric matrices over an arbitrary alphabet have one free symbol per unordered pair. -/
def symmetricEquiv : {X : Mat d A // ∀ i j, X i j = X j i} ≃ (Sym2 (Fin d) → A) where
  toFun X := Sym2.lift ⟨fun i j => X.val i j, X.property⟩
  invFun f := ⟨fun i j => f s(i,j), by intro i j; change f s(i,j) = f s(j,i); rw [Sym2.eq_swap]⟩
  left_inv _ := rfl
  right_inv f := by
    funext z
    induction z using Sym2.ind with
    | _ i j => rfl

/-- Identity row and column maps attain the fixed-family bound. -/
theorem identity_agreement_card [Fintype A] :
    Nat.card (Agreement (d := d) (A := A) (fun _ => id) (fun _ => id)) =
      Fintype.card A ^ (d * (d + 1) / 2) := by
  have e : Agreement (d := d) (A := A) (fun _ => id) (fun _ => id) ≃
      {X : Mat d A // ∀ i j, X i j = X j i} :=
    Equiv.subtypeEquivRight (fun X => by
      change (X = fun i j => X j i) ↔ _
      exact ⟨fun h i j => congrFun (congrFun h i) j, fun h => funext (fun i => funext (h i))⟩)
  rw [Nat.card_congr e, Nat.card_congr symmetricEquiv, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, sym2_card]

def HelperAgreement {κ : Type*} (H : Mat d A → κ) (R C : κ → Family d A) : Set (Mat d A) :=
  {X | X ∈ Agreement (R (H X)) (C (H X))}

/-- One actual joint helper selects both whole families; only its actual range is charged. -/
theorem helper_agreement_card_le [Fintype A] {κ : Type*}
    (H : Mat d A → κ) (R C : κ → Family d A) :
    Nat.card (HelperAgreement H R C) ≤
      Nat.card (Set.range H) * Fintype.card A ^ (d * (d + 1) / 2) := by
  classical
  let f : HelperAgreement H R C → Set.range H := fun X => ⟨H X.val, ⟨X.val, rfl⟩⟩
  have h (h : Set.range H) : Nat.card {X : HelperAgreement H R C // f X = h} ≤
      Fintype.card A ^ (d * (d + 1) / 2) := by
    let g : {X : HelperAgreement H R C // f X = h} → Agreement (R h.val) (C h.val) :=
      fun X => ⟨X.val.val, by
        have he := congrArg Subtype.val X.property
        change H X.val.val = h.val at he
        rw [← he]
        exact X.val.property⟩
    have hg : Function.Injective g := by
      intro X Y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun Z : Agreement (R h.val) (C h.val) => Z.val) hxy
    exact (Nat.card_le_card_of_injective g hg).trans (agreement_card_le _ _)
  let := Fintype.ofFinite (Set.range H)
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma] at he
  calc
    Nat.card (HelperAgreement H R C) = ∑ h : Set.range H, Nat.card {X // f X = h} := he.symm
    _ ≤ ∑ _h : Set.range H, Fintype.card A ^ (d * (d + 1) / 2) :=
      Finset.sum_le_sum (fun h' _ => h h')
    _ = _ := by simp [Nat.card_eq_fintype_card]

end SharedDecoders.RowColumn
