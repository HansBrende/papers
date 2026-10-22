import TransposeFollowup.Treewidth
import Mathlib.Algebra.Order.Floor.Ring

/-! Expected separator loss and its quadratic optimization. A single global
integer component threshold suffices, so the average-treewidth argument needs
neither pointwise square-root rounding nor a Jensen inequality. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

noncomputable def treewidthLossSeparator {n : ℕ} (b : ℕ)
    (G : SimpleGraph (Fin n)) (L : ℕ) : Finset (Fin n) :=
  (treewidth_separator_loss (b := b) G L).choose

theorem treewidthLossSeparator_bound {n : ℕ} (b : ℕ)
    (G : SimpleGraph (Fin n)) (L : ℕ) :
    (L + 1) * graphSeparatorLoss b G (treewidthLossSeparator b G L) ≤
      b * n * ((treewidth G + 1) * n + L * (L + 1)) :=
  (treewidth_separator_loss (b := b) G L).choose_spec

theorem mean_treewidth_separator_loss {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (graphs : Ω → SimpleGraph (Fin n)) (b L : ℕ) :
    ((L : ℝ) + 1) * (∑ x, p x *
        (graphSeparatorLoss b (graphs x) (treewidthLossSeparator b (graphs x) L) : ℝ)) ≤
      (b : ℝ) * n * (n * ((∑ x, p x * (treewidth (graphs x) : ℝ)) + 1) + L * (L + 1)) := by
  calc
    _ = ∑ x, p x * (((L : ℝ) + 1) *
        (graphSeparatorLoss b (graphs x) (treewidthLossSeparator b (graphs x) L) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, p x * ((b : ℝ) * n *
        (((treewidth (graphs x) : ℝ) + 1) * n + L * (L + 1))) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hp x)
      exact_mod_cast treewidthLossSeparator_bound b (graphs x) L
    _ = _ := by
      have he (x : Ω) : p x * ((b : ℝ) * n *
          (((treewidth (graphs x) : ℝ) + 1) * n + L * (L + 1))) =
          (b : ℝ) * n * n * (p x * treewidth (graphs x)) +
            p x * ((b : ℝ) * n * n + b * n * L * (L + 1)) := by ring
      simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hp1]
      ring

/-- Optimizing the integral component threshold directly improves the earlier
coefficient 1/9 (and its 1/n rounding loss) to 1/4, with an additional
positive finite-size correction a/2. -/
theorem quadratic_bound_of_integer_tests (n e a : ℝ) (hn : 0 < n) (he : 0 ≤ e)
    (htest : ∀ L : ℕ, n * ((L : ℝ) + 1) * a ≤ n * e + L * (L + 1)) :
    n / 4 * (max a 0) ^ 2 + max a 0 / 2 ≤ e := by
  by_cases ha : a ≤ 0
  · simpa [max_eq_right ha] using he
  · have ha0 : 0 < a := lt_of_not_ge ha
    rw [max_eq_left ha0.le]
    let r : ℝ := n * a / 2
    let L : ℕ := ⌊r⌋₊
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hlo : (L : ℝ) ≤ r := Nat.floor_le hr
    have hhi : r ≤ (L : ℝ) + 1 := (Nat.lt_floor_add_one r).le
    have hprod : r ^ 2 + r ≤ ((L : ℝ) + 1) * (2 * r - L) := by
      have hnonneg := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
      nlinarith
    have hupper : ((L : ℝ) + 1) * (2 * r - L) ≤ n * e := by
      have ht := htest L
      dsimp [r]
      nlinarith
    have hsq := hprod.trans hupper
    dsimp [r] at hsq
    apply (mul_le_mul_iff_left₀ hn).mp
    nlinarith

end TransposeFollowup
