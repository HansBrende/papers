import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! Positive sparse densities with an arbitrarily small explicit logarithmic
information bill. The proof reuses Mathlib's continuity of x log x at zero. -/

namespace LeanMachine
open Filter
open scoped Topology

theorem exists_logarithmic_density (a : ℝ) {B ε cap : ℝ}
    (hB : 0 < B) (hε : 0 < ε) (hcap : 0 < cap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ cap ∧ γ * (a + Real.logb 2 (B / γ)) ≤ ε := by
  let f (x : ℝ) := x * (a + Real.log B / Real.log 2) - (x * Real.log x) / Real.log 2
  have hcont : Continuous f :=
    (continuous_id.mul continuous_const).sub (Real.continuous_mul_log.div_const _)
  have ht : Tendsto f (𝓝 0) (𝓝 0) := by
    simpa only [f, zero_mul, zero_div, sub_zero] using hcont.continuousAt.tendsto (x := 0)
  have hsmall : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x < ε :=
    (ht.eventually (gt_mem_nhds hε)).filter_mono nhdsWithin_le_nhds
  have hbounded : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < cap :=
    (gt_mem_nhds hcap).filter_mono nhdsWithin_le_nhds
  have hex : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x < cap ∧ f x < ε := by
    filter_upwards [self_mem_nhdsWithin, hbounded, hsmall] with x hx hb hs
    exact ⟨hx, hb, hs⟩
  obtain ⟨γ, hγ, hγcap, hγf⟩ := hex.exists
  refine ⟨γ, hγ, hγcap.le, ?_⟩
  have he : γ * (a + Real.logb 2 (B / γ)) = f γ := by
    rw [Real.logb, Real.log_div hB.ne' hγ.ne']
    dsimp [f]
    ring
  rw [he]
  exact hγf.le

end LeanMachine
