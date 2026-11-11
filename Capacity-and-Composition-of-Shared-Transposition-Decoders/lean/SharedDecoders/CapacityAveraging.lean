import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The negative doubled-step term survives averaging

The finite telescoping estimate keeps a nonnegative terminal potential. Its
limit only needs nonnegativity of that potential, not a uniform upper bound.
-/

namespace SharedDecoders

open scoped BigOperators Topology
open Filter

theorem geometric_telescope_six (a : ℕ → ℝ) (C B r : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hr : 0 ≤ r) (hr6 : r < 6)
    (hstep : ∀ n, C ≤ 6 * a n - a (n + 1) + B * r ^ n) :
    C ≤ 5 * a 0 + 5 * B / (6 - r) := by
  have hfinite (n : ℕ) :
      C * (∑ j ∈ Finset.range n, (1 / 6 : ℝ) ^ j) +
          6 * (1 / 6 : ℝ) ^ n * a n ≤
      6 * a 0 + B * (∑ j ∈ Finset.range n, (r / 6) ^ j) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := mul_le_mul_of_nonneg_left (hstep n)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6) n)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_succ]
      have heq : (1 / 6 : ℝ) ^ n * r ^ n = (r / 6) ^ n := by
        rw [← mul_pow]
        congr 1
        ring
      nlinarith [congrArg (fun x => B * x) heq]
  have hbound (n : ℕ) :
      C * (∑ j ∈ Finset.range n, (1 / 6 : ℝ) ^ j) ≤
      6 * a 0 + B * (∑ j ∈ Finset.range n, (r / 6) ^ j) := by
    have htail : 0 ≤ 6 * (1 / 6 : ℝ) ^ n * a n :=
      mul_nonneg (by positivity) (ha n)
    linarith [hfinite n]
  have hr' : 0 ≤ r / 6 := by positivity
  have hr'1 : r / 6 < 1 := by linarith
  have hl := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 6)
      (by norm_num : (1 / 6 : ℝ) < 1)).tendsto_sum_nat
  have ht := (hasSum_geometric_of_lt_one hr' hr'1).tendsto_sum_nat
  have hlimit := le_of_tendsto_of_tendsto (hl.const_mul C)
    ((ht.const_mul B).const_add (6 * a 0)) (Filter.Eventually.of_forall hbound)
  norm_num at hlimit
  have hden : 6 - r ≠ 0 := by linarith
  have heq : (5 / 6 : ℝ) * (6 * a 0 + B * (1 - r / 6)⁻¹) =
      5 * a 0 + 5 * B / (6 - r) := by
    field_simp
  rw [← heq]
  nlinarith

/-- The exact analytic implication used by the two-class bound. The substantive
cyclic graph and gcd estimates are explicit inputs, not hidden formal axioms. -/
theorem two_class_averaging (a g : ℕ → ℝ) (D b d : ℝ)
    (hb : 0 < b) (hd : 0 < d)
    (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 ≤ d / 2)
    (hg : ∀ n, g n ≤ 2 * Real.sqrt d * (Real.sqrt 2) ^ n)
    (hstep : ∀ n, D ≤ 9 / 16 * b * d ^ 2 + 3 / 16 * b * d * a n -
      1 / 32 * b * d * a (n + 1) + 3 / 4 * b * d * g n) :
    D ≤ 41 / 64 * b * d ^ 2 + 5 / 3 * b * d * Real.sqrt d := by
  have hbd : 0 < b * d := mul_pos hb hd
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsnon := Real.sqrt_nonneg (2 : ℝ)
  have hslt : Real.sqrt 2 < 6 := by nlinarith
  let C := 32 * (D - 9 / 16 * b * d ^ 2) / (b * d)
  have hc (n : ℕ) : C ≤ 6 * a n - a (n + 1) +
      (48 * Real.sqrt d) * (Real.sqrt 2) ^ n := by
    have hh := hstep n
    have hg' := mul_le_mul_of_nonneg_left (hg n) (by positivity : 0 ≤ 3 / 4 * b * d)
    apply (div_le_iff₀ hbd).mpr
    nlinarith
  have h := geometric_telescope_six a C (48 * Real.sqrt d) (Real.sqrt 2)
    ha hsnon hslt hc
  have hsbound : 15 / 2 / (6 - Real.sqrt 2) ≤ (5 / 3 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < 6 - Real.sqrt 2)).mpr
    nlinarith
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hfrac : 5 * (48 * Real.sqrt d) / (6 - Real.sqrt 2) =
      32 * Real.sqrt d * (15 / 2 / (6 - Real.sqrt 2)) := by ring
  rw [hfrac] at h
  have hc' : C ≤ 5 * (d / 2) + 32 * Real.sqrt d * (5 / 3) := by
    have hm := mul_le_mul_of_nonneg_left hsbound (by positivity : 0 ≤ 32 * Real.sqrt d)
    linarith
  have hh := (div_le_iff₀ hbd).mp hc'
  nlinarith

end SharedDecoders
