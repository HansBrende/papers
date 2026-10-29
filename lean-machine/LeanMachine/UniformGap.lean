import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
# Uniform gaps from sequential exclusion

If two nonnegative costs cannot both vanish along instances of increasing
dimension, then sufficiently large instances with a small first cost have
a uniformly positive second cost. The instance type can encode additional
class restrictions without changing the argument.
-/

namespace LeanMachine.UniformGap

open Filter
open scoped Topology

/-- A single positive constant can bound the first cost above and the
second cost below. No topology or nonemptiness assumption on the instance
type is needed. -/
theorem exists_gap {ι : Type*} (dimension : ι → ℕ) (a δ : ι → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hδ : ∀ x, 0 ≤ δ x)
    (hno : ∀ x : ℕ → ι,
      Tendsto (fun n => dimension (x n)) atTop atTop →
      Tendsto (fun n => a (x n)) atTop (𝓝 0) →
      Tendsto (fun n => δ (x n)) atTop (𝓝 0) → False) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d₀ : ℕ,
      ∀ x, d₀ ≤ dimension x → a x ≤ ε → ε ≤ δ x := by
  by_contra! h
  have hw : ∀ n : ℕ, ∃ x : ι,
      n ≤ dimension x ∧ a x ≤ 1 / ((n : ℝ) + 1) ∧ δ x < 1 / ((n : ℝ) + 1) :=
    fun n => h _ (by positivity) n
  choose x hd hax hδx using hw
  exact hno x (tendsto_atTop_mono hd tendsto_id)
    (squeeze_zero (fun n => ha (x n)) hax tendsto_one_div_add_atTop_nhds_zero_nat)
    (squeeze_zero (fun n => hδ (x n)) (fun n => (hδx n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)

end LeanMachine.UniformGap
