import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Ring.Real

set_option autoImplicit false

/-! Explicit boundedness for real lower limits; no totalized extremum is
used without its order hypotheses. -/

namespace LeanMachine.BoundedLiminf

open Filter
open scoped Topology

theorem bounds {f : ℕ → ℝ} {a b : ℝ} (hf : ∀ n, a ≤ f n ∧ f n ≤ b) :
    a ≤ liminf f atTop ∧ liminf f atTop ≤ b :=
  ⟨le_liminf_of_le
    (IsCoboundedUnder.of_frequently_le (Frequently.of_forall fun n => (hf n).2))
    (Eventually.of_forall fun n => (hf n).1),
   liminf_le_of_frequently_le (Frequently.of_forall fun n => (hf n).2)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => (hf n).1))⟩

/-- A converging lower bound passes to a bounded sequence's lower limit. -/
theorem le_of_tendsto {f g : ℕ → ℝ} {a b G : ℝ}
    (hf : ∀ n, a ≤ f n ∧ f n ≤ b) (hg : Tendsto g atTop (𝓝 G))
    (hgf : ∀ᶠ n in atTop, g n ≤ f n) : G ≤ liminf f atTop := by
  obtain ⟨v, hvf, hv⟩ := exists_seq_tendsto_liminf (f := atTop) (u := f)
    (IsCoboundedUnder.of_frequently_le (Frequently.of_forall fun n => (hf n).2))
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => (hf n).1))
  exact le_of_tendsto_of_tendsto (hg.comp hv) hvf (hv.eventually hgf)

/-- Order comparison needs only a lower bound on the left and an upper bound
on the right; the eventual comparison supplies the other two bounds. -/
theorem mono {f g : ℕ → ℝ} {a b : ℝ} (hf : ∀ n, a ≤ f n) (hg : ∀ n, g n ≤ b)
    (hfg : ∀ᶠ n in atTop, f n ≤ g n) : liminf f atTop ≤ liminf g atTop :=
  liminf_le_liminf hfg
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall hf))
    (IsCoboundedUnder.of_frequently_le (Frequently.of_forall hg))

end LeanMachine.BoundedLiminf
