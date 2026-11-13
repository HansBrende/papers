import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Polynomial certificates for counting a finite real spectrum. -/

noncomputable section

namespace LeanMachine.SpectralCounting

open Polynomial

/-- Functional oddness forces each nonzero coefficient to have odd degree. -/
theorem odd_of_coeff_ne_zero (q : Polynomial ℝ)
    (hodd : ∀ x, q.eval (-x) = -q.eval x) {k : ℕ} (hk : q.coeff k ≠ 0) : Odd k := by
  have he : q.comp (C (-1) * X) = -q := by
    apply Polynomial.funext
    intro x
    simpa using hodd x
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff k) he
  simp only [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_neg] at hc
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, mul_one] at hc
    exact False.elim (hk (by linarith))
  · exact h

/-- Saturation at minus and plus one. -/
def clip (x : ℝ) : ℝ := max (-1) (min 1 x)

variable {n : Type*} [Fintype n]

/-- A lower approximation at the actual values suffices to count values at least one.
Neither continuity nor approximation on an interval is required. -/
theorem two_mul_card_ge_one_le (v : n → ℝ) (q : ℝ → ℝ) (η : ℝ)
    (h : ∀ i, clip (v i) - η ≤ q (v i)) :
    2 * (Fintype.card {i : n // 1 ≤ v i} : ℝ) ≤
      (1 + η) * Fintype.card n + ∑ i, q (v i) := by
  classical
  have hp (i : n) : 2 * (if 1 ≤ v i then (1 : ℝ) else 0) ≤ 1 + η + q (v i) := by
    have hi := h i
    by_cases hvi : 1 ≤ v i
    · simp [clip, hvi] at hi ⊢
      linarith
    · have hc : -1 ≤ clip (v i) := le_max_left _ _
      simp only [ite_eq_right hvi, mul_zero]
      linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  have he : (∑ i, 2 * (if 1 ≤ v i then (1 : ℝ) else 0)) =
      2 * (Fintype.card {i : n // 1 ≤ v i} : ℝ) := by
    rw [← Finset.mul_sum]
    simp [Fintype.card_subtype]
  rw [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  simpa only [mul_comm] using hs

/-- Odd moment bounds control every odd polynomial by its weighted coefficient sum. -/
theorem abs_sum_eval_le_of_odd_moments (v : n → ℝ) (γ D : ℝ)
    (hm : ∀ k : ℕ, Odd k → |∑ i, v i ^ k| ≤ γ ^ k * D)
    (q : Polynomial ℝ) (hodd : ∀ x, q.eval (-x) = -q.eval x) :
    |∑ i, q.eval (v i)| ≤ (∑ k ∈ q.support, |q.coeff k| * γ ^ k) * D := by
  have he : ∑ i, q.eval (v i) = ∑ k ∈ q.support, q.coeff k * ∑ i, v i ^ k := by
    simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he]
  calc
    _ ≤ ∑ k ∈ q.support, |q.coeff k * ∑ i, v i ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ q.support, |q.coeff k| * (γ ^ k * D) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hm k (odd_of_coeff_ne_zero q hodd (Polynomial.mem_support_iff.mp hk))) (abs_nonneg _)
    _ = _ := by simp only [← mul_assoc, Finset.sum_mul]

end LeanMachine.SpectralCounting
