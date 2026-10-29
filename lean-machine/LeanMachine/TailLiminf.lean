import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.ENNReal

set_option autoImplicit false

/-!
# Zero lower limits of real sequences

For nonnegative real sequences, take the lower limit in the complete ordered
space `ℝ≥0∞`. This avoids the default values of conditionally complete real
extrema when their required boundedness fails. The resulting zero condition says
exactly that arbitrarily late values lie below every positive real threshold.
-/

namespace LeanMachine.TailLiminf

open Filter
open scoped Topology

/-- A zero extended-nonnegative lower limit is equivalent to arbitrarily late
small values. No sign hypothesis is required: truncation by `ofReal` preserves
comparison with every positive threshold. -/
theorem liminf_ofReal_eq_zero_iff {a : ℕ → ℝ} :
    liminf (fun R => ENNReal.ofReal (a R)) atTop = 0 ↔
      ∀ ε > 0, ∀ R₀ : ℕ, ∃ R ≥ R₀, a R < ε := by
  constructor
  · intro h ε hε
    have hf : ∃ᶠ R in atTop, ENNReal.ofReal (a R) < ENNReal.ofReal ε :=
      frequently_lt_of_liminf_lt (h := by simpa [h] using ENNReal.ofReal_pos.mpr hε)
    exact frequently_atTop.mp (hf.mono fun _ hR => (ENNReal.ofReal_lt_ofReal_iff hε).mp hR)
  · intro h
    apply le_antisymm ?_ bot_le
    rw [liminf_le_iff]
    intro b hb
    obtain ⟨ε, _, hε, hεb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
    have he : 0 < ε := ENNReal.ofReal_pos.mp hε
    exact (frequently_atTop.mpr (h ε he)).mono fun _ hR =>
      ((ENNReal.ofReal_lt_ofReal_iff he).mpr hR).trans hεb

/-- Ordinary convergence to zero implies the extended-nonnegative zero lower
limit; boundedness need not be supplied separately. -/
theorem liminf_ofReal_eq_zero_of_tendsto {a : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 0)) :
    liminf (fun R => ENNReal.ofReal (a R)) atTop = 0 := by
  simpa using (ENNReal.tendsto_ofReal ha).liminf_eq

/-- Finite nonnegative scaling preserves a zero lower limit, including
the zero coefficient. This is the standard extended-real scaling law. -/
theorem liminf_ofReal_const_mul_eq_zero {a : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (ha : liminf (fun R => ENNReal.ofReal (a R)) atTop = 0) :
    liminf (fun R => ENNReal.ofReal (c * a R)) atTop = 0 := by
  simp_rw [ENNReal.ofReal_mul hc]
  rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top, ha, mul_zero]

end LeanMachine.TailLiminf
