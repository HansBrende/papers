import LeanMachine.LogarithmicDensity

/-! The explicit sparse-density condition in the getter theorem always has
a positive solution for every fixed resource budget. -/

namespace AdaptiveTransfer.Getter

theorem exists_getter_density (k a N : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N) (hc : 1 ≤ c) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 2 ∧
      γ * ((a : ℝ) + Real.logb 2 (2 * Real.exp 1 * k * c / γ)) ≤ 1 / (64 * (N : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  exact LeanMachine.exists_logarithmic_density (a : ℝ)
    (by positivity) (by positivity) (by norm_num)

end AdaptiveTransfer.Getter
