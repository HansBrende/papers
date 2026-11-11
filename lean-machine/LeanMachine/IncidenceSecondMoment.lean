import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-! A finite second-moment bound from marginal incidence counts. -/

namespace LeanMachine.IncidenceSecondMoment

open scoped BigOperators

/-- The finite Euclidean triangle inequality, expanded as pairwise
Cauchy--Schwarz. No independence assumptions are present. -/
theorem squared_sum_le {I T : Type*} [Fintype I] [Fintype T] (f : I → T → ℝ) :
    (∑ t, (∑ i, f i t)^2) ≤ (∑ i, Real.sqrt (∑ t, (f i t)^2))^2 := by
  calc
    _ = ∑ i, ∑ j, ∑ t, f i t*f j t := by
      simp_rw [pow_two, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ ∑ i, ∑ j, Real.sqrt (∑ t, (f i t)^2)*Real.sqrt (∑ t, (f j t)^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (f i) (f j)
    _ = _ := by rw [pow_two, Finset.sum_mul_sum]

/-- The sum of squared sample occupancies is bounded by the square of the
sum of square roots of the actual marginal sample counts. -/
theorem incidence_squared_sum_le {I T : Type*} [Fintype I] [Fintype T]
    (R : I → T → Prop) [DecidableRel R] :
    (∑ t, (Fintype.card {i // R i t} : ℝ)^2) ≤
      (∑ i, Real.sqrt (Fintype.card {t // R i t} : ℝ))^2 := by
  let f (i : I) (t : T) : ℝ := if R i t then 1 else 0
  have h₁ (t : T) : (∑ i, f i t) = (Fintype.card {i // R i t} : ℝ) := by
    simp [f, Fintype.card_subtype]
  have h₂ (i : I) : (∑ t, (f i t)^2) = (Fintype.card {t // R i t} : ℝ) := by
    simp [f, Fintype.card_subtype]
  simpa only [h₁,h₂] using squared_sum_le f


/-- A coarse real-exponent weight bound, from Bernoulli's inequality. -/
theorem power_weight_le (x r : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hr : 0 ≤ r) :
    x*(1-x)^r ≤ 1/(r+1) := by
  have hr1 : 0 < r+1 := by linarith
  rcases eq_or_lt_of_le hx1 with hxeq | hxlt
  · subst x
    by_cases hr0 : r=0
    · subst r; norm_num
    · rw [sub_self, Real.zero_rpow hr0, mul_zero]
      positivity
  · have hu : 0 < 1-x := sub_pos.mpr hxlt
    have hs : -1 ≤ x/(1-x) := by have hh := div_nonneg hx hu.le; linarith
    have hb := one_add_mul_self_le_rpow_one_add hs (show 1 ≤ r+1 by linarith)
    have he : 1+x/(1-x)=1/(1-x) := by field_simp; ring
    have hm := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hu.le (r+1))
    rw [he, ← Real.mul_rpow (by positivity : 0 ≤ 1/(1-x)) hu.le,
      one_div_mul_cancel (ne_of_gt hu), Real.one_rpow] at hm
    have hp : (1-x)^(r+1) = (1-x)^r*(1-x) := Real.rpow_add_one hu.ne' r
    have hl : (1+(r+1)*(x/(1-x)))*(1-x)^(r+1) =
        (1-x)^r*((1-x)+(r+1)*x) := by
      rw [hp]
      field_simp
    rw [hl] at hm
    have hn := mul_nonneg (Real.rpow_nonneg hu.le r) hu.le
    apply (le_div_iff₀ hr1).mpr
    nlinarith only [hm,hn]

end LeanMachine.IncidenceSecondMoment
