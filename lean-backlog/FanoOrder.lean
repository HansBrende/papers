import FanoCertificate

/-!
# Exact whole-row order value of the Fano host

The seven lines use the actual incidence predicate of `FanoCertificate`.
The proof checks the 128 row subsets and one collinear-first order, rather
than enumerating the 5040 permutations. A double count identifies the prefix
formula with the sum of the seven last-helper positions, numbered 1 through 7.

The comparison with the maximum induced acyclic-set size uses Paper 17's
separate written whole-row exactness theorem; that adapter is not proved here.
-/

namespace LeanBacklog.FanoOrder

open Finset FanoCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 4096

abbrev Point := Fin 7
abbrev Order := Equiv.Perm Point

/-- The point rows incident with one line normal. -/
def line (l : Point) : Finset Point := univ.filter fun p => incident p l

/-- Lines all of whose helper rows lie in the given row set. -/
def completeLines (A : Finset Point) : Finset Point :=
  univ.filter fun l => line l ⊆ A

/-- The sharp complete-line count for each possible cardinality. -/
def completeLimit : ℕ → ℕ
  | 0 | 1 | 2 => 0
  | 3 | 4 => 1
  | 5 => 2
  | 6 => 4
  | _ => 7

/-- A kernel-checked statement about the 128 point subsets, not all orders. -/
theorem completeLines_card_le : ∀ A : Finset Point,
    (completeLines A).card ≤ completeLimit A.card := by decide

/-- `order p` is the zero-based position of point `p`. -/
def rowPrefix (order : Order) (a : Point) : Finset Point :=
  univ.filter fun p => order p < a

theorem prefix_card (order : Order) (a : Point) : (rowPrefix order a).card = a.val := by
  have he : rowPrefix order a = (Iio a).map order.symm.toEmbedding := by
    ext p
    simp [rowPrefix]
  rw [he, card_map]
  simp

/-- The full 49-cell prefix-order cost. -/
def orderCost (order : Order) : ℕ :=
  49 - ∑ a : Point, (completeLines (rowPrefix order a)).card

theorem prefix_sum_le_eight (order : Order) :
    ∑ a : Point, (completeLines (rowPrefix order a)).card ≤ 8 := by
  calc
    _ ≤ ∑ a : Point, completeLimit a.val := by
      apply sum_le_sum
      intro a _
      simpa only [prefix_card] using completeLines_card_le (rowPrefix order a)
    _ = 8 := by decide

theorem orderCost_ge_fortyOne (order : Order) : 41 ≤ orderCost order := by
  have h := prefix_sum_le_eight order
  unfold orderCost
  omega

/-- Positions of the order 1,3,5,0,2,4,6; its first three points form line 0. -/
def attainingOrder : Order where
  toFun := ![3, 0, 4, 1, 5, 2, 6]
  invFun := ![1, 3, 5, 0, 2, 4, 6]
  left_inv := by intro p; revert p; decide
  right_inv := by intro p; revert p; decide

theorem attainingOrder_cost : orderCost attainingOrder = 41 := by decide

/-- Exact minimum, without introducing a computable permutation search. -/
theorem exact_order_value : (∀ order, 41 ≤ orderCost order) ∧
    ∃ order, orderCost order = 41 :=
  ⟨orderCost_ge_fortyOne, attainingOrder, attainingOrder_cost⟩

/-- Last helper position, with positions numbered 1 through 7. -/
def lastHelperPosition (order : Order) (l : Point) : ℕ :=
  (line l).sup fun p => (order p).val + 1

theorem lastHelperPosition_le_seven (order : Order) (l : Point) :
    lastHelperPosition order l ≤ 7 := by
  apply Finset.sup_le
  intro p _
  have h := (order p).isLt
  omega

theorem line_subset_prefix_iff (order : Order) (a l : Point) :
    line l ⊆ rowPrefix order a ↔ lastHelperPosition order l ≤ a.val := by
  constructor
  · intro h
    apply Finset.sup_le
    intro p hp
    have hp' := (mem_filter.mp (h hp)).2
    exact Nat.add_one_le_iff.mpr hp'
  · intro h p hp
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    have hl : (order p).val + 1 ≤ a.val := (Finset.le_sup hp).trans h
    exact Nat.add_one_le_iff.mp hl

/-- An eight-value threshold count used for double counting. -/
private theorem threshold_count : ∀ n : Fin 8,
    (∑ a : Point, if n.val ≤ a.val then 1 else 0) = 7 - n.val := by decide

theorem prefix_sum_eq_last_complements (order : Order) :
    (∑ a : Point, (completeLines (rowPrefix order a)).card) =
      ∑ l : Point, (7 - lastHelperPosition order l) := by
  simp only [completeLines, card_eq_sum_ones, sum_filter]
  simp only [line_subset_prefix_iff]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  exact threshold_count ⟨lastHelperPosition order l,
    by have h := lastHelperPosition_le_seven order l; omega⟩

/-- The prefix formula is the standard sum of last-helper positions. -/
theorem orderCost_eq_sum_lastHelperPosition (order : Order) :
    orderCost order = ∑ l : Point, lastHelperPosition order l := by
  have ht : (∑ l : Point, lastHelperPosition order l) +
      (∑ a : Point, (completeLines (rowPrefix order a)).card) = 49 := by
    rw [prefix_sum_eq_last_complements, ← sum_add_distrib]
    calc
      _ = ∑ _ : Point, 7 := by
        apply sum_congr rfl
        intro l _
        have h := lastHelperPosition_le_seven order l
        omega
      _ = 49 := by decide
  unfold orderCost
  omega

/-- Exact value in the usual last-helper-position formulation. -/
theorem exact_last_helper_value :
    (∀ order, 41 ≤ ∑ l : Point, lastHelperPosition order l) ∧
      ∃ order, (∑ l : Point, lastHelperPosition order l) = 41 := by
  simpa only [orderCost_eq_sum_lastHelperPosition] using exact_order_value

#print axioms completeLines_card_le
#print axioms exact_order_value
#print axioms orderCost_eq_sum_lastHelperPosition
#print axioms exact_last_helper_value

end LeanBacklog.FanoOrder
