import Mathlib.Analysis.SpecificLimits.Basic

/-! A sequential criterion for an eventual uniform positive gap.

The admissible objects may depend on the size, and need not form compact sets.
The hypothesis rules out vanishing-cost sequences whose sizes tend to infinity.
-/

namespace CascadeObstruction

open Filter Topology

set_option autoImplicit false

/-- If no sequence of admissible objects at diverging sizes has cost tending
to zero, all sufficiently large admissible objects have one positive cost gap. -/
theorem exists_uniform_positive_gap {Obj : ℕ → Type*}
    (cost : (n : ℕ) → Obj n → ℝ)
    (nonneg : ∀ n x, 0 ≤ cost n x)
    (noVanishing : ∀ (ns : ℕ → ℕ) (xs : ∀ i, Obj (ns i)),
      Tendsto ns atTop atTop →
      ¬ Tendsto (fun i => cost (ns i) (xs i)) atTop (𝓝 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ x : Obj n, δ ≤ cost n x := by
  classical
  by_contra h
  push Not at h
  have hw : ∀ i : ℕ, ∃ n : ℕ, i ≤ n ∧ ∃ x : Obj n,
      cost n x < 1 / ((i : ℝ) + 1) := by
    intro i
    exact h (1 / ((i : ℝ) + 1)) (by positivity) i
  choose ns hns xs hcost using hw
  have hn : Tendsto ns atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact eventually_atTop.2 ⟨b, fun i hi => hi.trans (hns i)⟩
  apply noVanishing ns xs hn
  exact squeeze_zero (fun i => nonneg _ _) (fun i => (hcost i).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end CascadeObstruction
