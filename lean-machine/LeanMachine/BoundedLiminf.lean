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

/-- A pointwise affine upper bound with a vanishing error passes to lower
limits, by taking a subsequence attaining the right-hand lower limit. -/
theorem affine_upper {f g e : ℕ → ℝ} {a b c lo hi : ℝ}
    (hf : ∀ n, a ≤ f n) (hg : ∀ n, lo ≤ g n ∧ g n ≤ hi)
    (he : Tendsto e atTop (𝓝 0)) (hfg : ∀ n, f n ≤ b+c*g n+e n) :
    liminf f atTop ≤ b+c*liminf g atTop := by
  obtain ⟨v, hgv, hv⟩ := exists_seq_tendsto_liminf (f := atTop) (u := g)
    (IsCoboundedUnder.of_frequently_le (Frequently.of_forall fun n => (hg n).2))
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => (hg n).1))
  have ht : Tendsto (fun n => b+c*g (v n)+e (v n)) atTop
      (𝓝 (b+c*liminf g atTop)) := by
    simpa only [add_zero,Function.comp_apply] using (tendsto_const_nhds.add
      (tendsto_const_nhds.mul hgv)).add (he.comp hv)
  apply le_of_forall_lt_imp_le_of_dense
  intro z hz
  have hz' := eventually_lt_of_lt_liminf hz
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall hf))
  apply ge_of_tendsto ht
  exact (hv.eventually hz').mono (fun n hn => hn.le.trans (hfg (v n)))

end LeanMachine.BoundedLiminf
