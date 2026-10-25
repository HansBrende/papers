import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.RelClasses
import Lean.Elab.Tactic.Omega

/-!
# Recovering words in an order of port colors

A directed recovery relation whose edges preserve port colors can be decoded
in color order from the coordinates whose left color precedes their right color.
Comparing an order with its reverse gives a half-size record.
-/

namespace LeanMachine.ColorOrder

open Finset

variable {V α κ : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Agreement on the recorded coordinates propagates in increasing left-color order. -/
theorem eq_of_agree_on_record [LinearOrder κ] [WellFoundedLT κ]
    (N : V → Finset V) (left right : V → κ)
    (hcolors : ∀ q, left q ≠ right q)
    (hedge : ∀ q p, p ∈ N q → left p = right q)
    (x y : V → α)
    (hrec : ∀ q, (∀ p ∈ N q, x p = y p) → x q = y q)
    (hrecord : ∀ q, left q < right q → x q = y q) : x = y := by
  have h : ∀ c : κ, ∀ q, left q = c → x q = y q := by
    intro c
    induction c using WellFoundedLT.induction with
    | ind c ih =>
      intro q hq
      by_cases hr : left q < right q
      · exact hrecord q hr
      · apply hrec q
        intro p hp
        have hpq : left p < left q := by
          rw [hedge q p hp]
          exact lt_of_le_of_ne (le_of_not_gt hr) (Ne.symm (hcolors q))
        exact ih (left p) (hq ▸ hpq) p rfl
  funext q
  exact h (left q) q rfl

/-- Cardinality form of the ordered decoding argument. -/
theorem card_le_pow_record [Fintype α] [LinearOrder κ] [WellFoundedLT κ]
    (N : V → Finset V) (left right : V → κ)
    (hcolors : ∀ q, left q ≠ right q)
    (hedge : ∀ q p, p ∈ N q → left p = right q)
    (C : Finset (V → α))
    (hrec : ∀ x ∈ C, ∀ y ∈ C, ∀ q,
      (∀ p ∈ N q, x p = y p) → x q = y q) :
    C.card ≤ Fintype.card α ^ (univ.filter (fun q => left q < right q)).card := by
  classical
  let S := univ.filter (fun q => left q < right q)
  let f : (V → α) → (S → α) := fun x q => x q
  have hf : Set.InjOn f C := by
    intro x hx y hy heq
    apply eq_of_agree_on_record N left right hcolors hedge x y (hrec x hx y hy)
    intro q hq
    exact congrFun heq ⟨q, by simp [S, hq]⟩
  calc
    C.card = (C.image f).card := (card_image_iff.mpr hf).symm
    _ ≤ Fintype.card (S → α) := card_le_univ _
    _ = Fintype.card α ^ S.card := by simp

/-- An order and its reverse give a record of at most half the coordinates. -/
theorem card_le_pow_half [Fintype α] [Nonempty α] [Fintype κ] [LinearOrder κ]
    (N : V → Finset V) (left right : V → κ)
    (hcolors : ∀ q, left q ≠ right q)
    (hedge : ∀ q p, p ∈ N q → left p = right q)
    (C : Finset (V → α))
    (hrec : ∀ x ∈ C, ∀ y ∈ C, ∀ q,
      (∀ p ∈ N q, x p = y p) → x q = y q) :
    C.card ≤ Fintype.card α ^ (Fintype.card V / 2) := by
  classical
  let S := univ.filter (fun q => left q < right q)
  let T := univ.filter (fun q => right q < left q)
  have hST : S.card + T.card = Fintype.card V := by
    have hn : (fun q => ¬left q < right q) = (fun q => right q < left q) := by
      funext q
      exact propext ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (hcolors q)),
        fun h => not_lt_of_ge (le_of_lt h)⟩
    have h := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun q => left q < right q)
    have hf : univ.filter (fun q => ¬left q < right q) = T := by
      apply Finset.filter_congr
      intro q _
      exact iff_of_eq (congrFun hn q)
    rw [hf, card_univ] at h
    exact h
  have hS := card_le_pow_record N left right hcolors hedge C hrec
  have hT := card_le_pow_record (κ := κᵒᵈ) N left right hcolors hedge C hrec
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  by_cases hs : S.card ≤ Fintype.card V / 2
  · exact hS.trans (Nat.pow_le_pow_right hpos hs)
  · have ht : T.card ≤ Fintype.card V / 2 := by omega
    exact hT.trans (Nat.pow_le_pow_right hpos ht)

end LeanMachine.ColorOrder
