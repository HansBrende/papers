import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-! A size budget for disjoint nonempty finite sets. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u

theorem disjoint_family_size_bound {V : Type u} [Fintype V] [DecidableEq V]
    (U : Finset (Finset V)) (hne : ∀ S ∈ U, S.Nonempty)
    (hdis : (U : Set (Finset V)).PairwiseDisjoint id) (ell : ℕ) :
    (ell + 1) * U.card ≤ Fintype.card V + ell * (U.filter (fun S => S.card ≤ ell)).card := by
  have hpoint (S : Finset V) (hS : S ∈ U) :
      ell + 1 ≤ S.card + if S.card ≤ ell then ell else 0 := by
    have hp := Finset.card_pos.mpr (hne S hS)
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpoint
  have hcards : ∑ S ∈ U, S.card ≤ Fintype.card V := by
    calc
      _ = (U.biUnion id).card := by simpa only [id_eq] using (Finset.card_biUnion hdis).symm
      _ ≤ _ := Finset.card_le_univ _
  have hsmall : (∑ S ∈ U, if S.card ≤ ell then ell else 0) =
      ell * (U.filter (fun S => S.card ≤ ell)).card := by
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib] at hsum
  rw [hsmall] at hsum
  nlinarith

end TransposeFollowup
