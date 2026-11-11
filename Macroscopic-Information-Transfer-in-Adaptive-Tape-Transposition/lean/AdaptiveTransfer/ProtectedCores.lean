import LeanMachine.ProtectedIntervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Protected chart cores and separately paid fringes -/

namespace AdaptiveTransfer

open LeanMachine.ProtectedIntervals

/-- Monotonicity and the stated local error put every selected position in
the strict core or one of its closed fringes. -/
theorem selected_in_core_or_fringe {f : ℝ → ℝ} (hf : Monotone f)
    {ell W z : ℝ} {u : ℤ} {j : ℕ} (hz : ell ≤ z ∧ z < ell + W)
    (herr : |(u : ℝ) - f z| ≤ j) :
    u ∈ core (f ell) (f (ell + W)) j ∪ fringe (f ell) (f (ell + W)) j := by
  apply covered
  have he := abs_le.mp herr
  have h₁ := hf hz.1
  have h₂ := hf hz.2.le
  constructor <;> linarith [he.1, he.2]

/-- Steps outside the carrier slab cannot write a protected core cell. -/
theorem outside_avoids_core {f : ℝ → ℝ} (hf : Monotone f)
    {ell W z : ℝ} {u : ℤ} {j : ℕ} (hz : z < ell ∨ ell + W ≤ z)
    (herr : |(u : ℝ) - f z| ≤ j) : u ∉ core (f ell) (f (ell + W)) j := by
  apply outside_core
  have he := abs_le.mp herr
  rcases hz with hz | hz
  · have hh := hf hz.le
    left
    linarith [he.2]
  · have hh := hf hz
    right
    linarith [he.1]

alias protected_core_disjoint_fringe := LeanMachine.ProtectedIntervals.core_disjoint_fringe

/-- Individual head errors may differ. The total core bill depends only on
the normalized chart width, while fringe costs add separately. -/
theorem normalized_chart_core_fringe_counts {I : Type*} [Fintype I]
    (f : I → ℝ → ℝ) (hf : ∀ i, Monotone (f i))
    (hnorm : ∀ z, (∑ i, f i z) = z) (ell W : ℝ) (hW : 0 ≤ W) (j : I → ℕ) :
    (∑ i, ((core (f i ell) (f i (ell + W)) (j i)).card : ℝ)) ≤ W + Fintype.card I ∧
      (∑ i, (fringe (f i ell) (f i (ell + W)) (j i)).card) ≤
        4 * (∑ i, j i) + 2 * Fintype.card I := by
  constructor
  · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      card_core_le (hf i (by linarith : ell ≤ ell + W)) (j i))
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hnorm,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, add_sub_cancel_left] using hsum
  · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      card_fringe_le (f i ell) (f i (ell + W)) (j i))
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Nat.mul_comm (Fintype.card I) 2] using hsum

end AdaptiveTransfer
