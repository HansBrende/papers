import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Basic.Real.Basic

set_option autoImplicit false

/-!
# Averaging a credit together with its paid cost

Pointwise signed inequalities can be averaged before replacing the mean cost
by its budget. No single phase must simultaneously optimize credit and cost.
-/

namespace LeanMachine.PaidAveraging

open Finset
open scoped BigOperators

variable {ι : Type*} {A : Finset ι} {f g : ι → ℝ} {c β Δ G : ℝ}

/-- Averaging preserves the complete signed expression. -/
theorem mean_signed_eq (hA : A.Nonempty) (f g : ι → ℝ) (c β : ℝ) :
    (∑ ρ ∈ A, (f ρ - c - β * g ρ)) / A.card =
      (∑ ρ ∈ A, f ρ) / A.card - c - β * ((∑ ρ ∈ A, g ρ) / A.card) := by
  have h : (𝔼 ρ ∈ A, (f ρ - c - β * g ρ)) =
      (𝔼 ρ ∈ A, f ρ) - c - β * (𝔼 ρ ∈ A, g ρ) := by
    rw [expect_sub_distrib, expect_sub_distrib, expect_const hA, ← mul_expect]
  simpa only [expect_eq_sum_div_card] using h

/-- The exact mean bound does not require a sign condition on the coefficient. -/
theorem mean_signed_le (hA : A.Nonempty)
    (hpoint : ∀ ρ ∈ A, f ρ - c - β * g ρ ≤ Δ) :
    (∑ ρ ∈ A, f ρ) / A.card - c - β * ((∑ ρ ∈ A, g ρ) / A.card) ≤ Δ := by
  rw [← mean_signed_eq hA f g c β]
  simpa only [expect_eq_sum_div_card] using expect_le hA hpoint

/-- A budget for the mean cost suffices when its penalty coefficient is nonnegative. -/
theorem mean_credit_sub_cost_le (hA : A.Nonempty) (hβ : 0 ≤ β)
    (hpoint : ∀ ρ ∈ A, f ρ - c - β * g ρ ≤ Δ)
    (hcost : (∑ ρ ∈ A, g ρ) / A.card ≤ G) :
    (∑ ρ ∈ A, f ρ) / A.card - c - β * G ≤ Δ :=
  (sub_le_sub_left (mul_le_mul_of_nonneg_left hcost hβ) _).trans
    (mean_signed_le hA hpoint)

end LeanMachine.PaidAveraging
