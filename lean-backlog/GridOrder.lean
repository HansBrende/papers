import GridFull

/-!
# Exact whole-row order value of the rectangular grid

The six lines use the actual nine-point incidence predicate of GridCertificate.
The proof checks the 512 point subsets and one attaining row order, not all
9! permutations. Double counting identifies the full prefix cost with the
sum of last-helper positions; removing the 18 incident cells gives cost 23.

The passage from this row-order optimum to arbitrary induced acyclic sets uses
Paper 17's separate written whole-row exactness argument. No capacity equality
or attaining code for the Shannon upper bound is claimed here.
-/

namespace LeanBacklog.GridOrder

open Finset GridCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev Point := Fin 9
abbrev Line := Fin 6
abbrev Order := Equiv.Perm Point

def line (l : Line) : Finset Point := univ.filter fun p => incident p l

def completeLines (A : Finset Point) : Finset Line :=
  univ.filter fun l => line l ⊆ A

/-- Sharp complete-line counts for all row-set cardinalities. -/
def completeLimit : ℕ → ℕ
  | 0 | 1 | 2 => 0
  | 3 | 4 => 1
  | 5 | 6 => 2
  | 7 => 3
  | 8 => 4
  | _ => 6

theorem completeLines_card_le : ∀ A : Finset Point,
    (completeLines A).card ≤ completeLimit A.card := by decide

/-- The permutation assigns zero-based positions to points. -/
def rowPrefix (order : Order) (a : Point) : Finset Point :=
  univ.filter fun p => order p < a

theorem prefix_card (order : Order) (a : Point) : (rowPrefix order a).card = a.val := by
  have he : rowPrefix order a = (Iio a).map order.symm.toEmbedding := by
    ext p
    simp [rowPrefix]
  rw [he, card_map]
  simp

def orderCost (order : Order) : ℕ :=
  54 - ∑ a : Point, (completeLines (rowPrefix order a)).card

def residualOrderCost (order : Order) : ℕ :=
  36 - ∑ a : Point, (completeLines (rowPrefix order a)).card

theorem prefix_sum_le_thirteen (order : Order) :
    ∑ a : Point, (completeLines (rowPrefix order a)).card ≤ 13 := by
  calc
    _ ≤ ∑ a : Point, completeLimit a.val := by
      apply sum_le_sum
      intro a _
      simpa only [prefix_card] using completeLines_card_le (rowPrefix order a)
    _ = 13 := by decide

theorem orderCost_ge_fortyOne (order : Order) : 41 ≤ orderCost order := by
  have h := prefix_sum_le_thirteen order
  unfold orderCost
  omega

theorem residualOrderCost_ge_twentyThree (order : Order) : 23 ≤ residualOrderCost order := by
  have h := prefix_sum_le_thirteen order
  unfold residualOrderCost
  omega

theorem residualOrderCost_add_loops (order : Order) :
    residualOrderCost order + 18 = orderCost order := by
  have h := prefix_sum_le_thirteen order
  unfold orderCost residualOrderCost
  omega

/-- Positions of the row order 0,1,2,3,6,4,5,7,8. -/
def attainingOrder : Order where
  toFun := ![0, 1, 2, 3, 5, 6, 4, 7, 8]
  invFun := ![0, 1, 2, 3, 6, 4, 5, 7, 8]
  left_inv := by intro p; revert p; decide
  right_inv := by intro p; revert p; decide

theorem attainingOrder_cost : orderCost attainingOrder = 41 := by decide
theorem attainingOrder_residual_cost : residualOrderCost attainingOrder = 23 := by decide

theorem exact_order_value : (∀ order, 41 ≤ orderCost order) ∧
    ∃ order, orderCost order = 41 :=
  ⟨orderCost_ge_fortyOne, attainingOrder, attainingOrder_cost⟩

theorem exact_residual_order_value : (∀ order, 23 ≤ residualOrderCost order) ∧
    ∃ order, residualOrderCost order = 23 :=
  ⟨residualOrderCost_ge_twentyThree, attainingOrder, attainingOrder_residual_cost⟩

def lastHelperPosition (order : Order) (l : Line) : ℕ :=
  (line l).sup fun p => (order p).val + 1

theorem lastHelperPosition_le_nine (order : Order) (l : Line) :
    lastHelperPosition order l ≤ 9 := by
  apply Finset.sup_le
  intro p _
  have h := (order p).isLt
  omega

theorem line_subset_prefix_iff (order : Order) (a : Point) (l : Line) :
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

private theorem threshold_count : ∀ n : Fin 10,
    (∑ a : Point, if n.val ≤ a.val then 1 else 0) = 9 - n.val := by decide

theorem prefix_sum_eq_last_complements (order : Order) :
    (∑ a : Point, (completeLines (rowPrefix order a)).card) =
      ∑ l : Line, (9 - lastHelperPosition order l) := by
  simp only [completeLines, card_eq_sum_ones, sum_filter]
  simp only [line_subset_prefix_iff]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  exact threshold_count ⟨lastHelperPosition order l,
    by have h := lastHelperPosition_le_nine order l; omega⟩

theorem orderCost_eq_sum_lastHelperPosition (order : Order) :
    orderCost order = ∑ l : Line, lastHelperPosition order l := by
  have ht : (∑ l : Line, lastHelperPosition order l) +
      (∑ a : Point, (completeLines (rowPrefix order a)).card) = 54 := by
    rw [prefix_sum_eq_last_complements, ← sum_add_distrib]
    calc
      _ = ∑ _ : Line, 9 := by
        apply sum_congr rfl
        intro l _
        have h := lastHelperPosition_le_nine order l
        omega
      _ = 54 := by decide
  unfold orderCost
  omega

theorem exact_last_helper_value :
    (∀ order, 41 ≤ ∑ l : Line, lastHelperPosition order l) ∧
      ∃ order, (∑ l : Line, lastHelperPosition order l) = 41 := by
  simpa only [orderCost_eq_sum_lastHelperPosition] using exact_order_value

/-- The residual Shannon upper bound is strictly below every row-order cost. -/
theorem residual_upper_lt_order (h : Finset Cell → ℝ) (hh : MotionDepthCodes.IsPolymatroid h)
    (hv : MotionDepthCodes.IsValid h nbhd) (hc : ∀ v, h {v} ≤ 1) (order : Order) :
    h univ < residualOrderCost order := by
  have hu := GridCertificate.residual_le h hh hv hc
  have ho : (23 : ℝ) ≤ residualOrderCost order := by
    exact_mod_cast residualOrderCost_ge_twentyThree order
  linarith

/-- The same strict comparison on the full 54-cell host. -/
theorem full_upper_lt_order (h : Finset GridFull.Grid → ℝ) (hh : MotionDepthCodes.IsPolymatroid h)
    (hv : MotionDepthCodes.IsValid h GridFull.helpers) (hc : ∀ v, h {v} ≤ 1) (order : Order) :
    h univ < orderCost order := by
  have hu := GridFull.full_upper hh hv hc
  have ho : (41 : ℝ) ≤ orderCost order := by exact_mod_cast orderCost_ge_fortyOne order
  linarith

end LeanBacklog.GridOrder

#print axioms LeanBacklog.GridOrder.exact_order_value
#print axioms LeanBacklog.GridOrder.exact_residual_order_value
#print axioms LeanBacklog.GridOrder.exact_last_helper_value
#print axioms LeanBacklog.GridOrder.residual_upper_lt_order
#print axioms LeanBacklog.GridOrder.full_upper_lt_order
