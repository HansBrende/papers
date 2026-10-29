import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Ring.Real

set_option autoImplicit false

/-!
# Upper limits of bounded real sequences

The explicit bounds ensure that real upper limits have their usual order
properties. Passing an inequality along a sequence approaching the upper limit
also handles coefficients that vanish at finite indices or in the limit.
-/

namespace LeanMachine.BoundedLimsup

open Filter
open scoped Topology

/-- An eventual lower bound passes to the upper limit of a sequence bounded
above by one. -/
theorem le_limsup {f : ℕ → ℝ} {B : ℝ} (hf1 : ∀ n, f n ≤ 1)
    (hlo : ∀ᶠ n in atTop, B ≤ f n) : B ≤ limsup f atTop :=
  le_limsup_of_frequently_le hlo.frequently
    (isBoundedUnder_of_eventually_le (Eventually.of_forall hf1))

/-- The upper limit of a sequence in `[0, 1]` is nonnegative. -/
theorem limsup_nonneg {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hf1 : ∀ n, f n ≤ 1) : 0 ≤ limsup f atTop :=
  le_limsup hf1 (Eventually.of_forall hf0)

/-- The upper limit of a sequence in `[0, 1]` is at most one. -/
theorem limsup_le_one {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hf1 : ∀ n, f n ≤ 1) : limsup f atTop ≤ 1 :=
  limsup_le_of_le
    (IsCoboundedUnder.of_frequently_ge (Frequently.of_forall hf0))
    (Eventually.of_forall hf1)

/-- Pass an eventual product inequality to the upper limit of its bounded
factor. Neither finite coefficients nor their limit need be positive. -/
theorem mul_limsup_le_of_tendsto {f a b : ℕ → ℝ} {A B : ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hab : ∀ᶠ n in atTop, a n * f n ≤ b n) :
    A * limsup f atTop ≤ B := by
  obtain ⟨v, hfv, hv⟩ := exists_seq_tendsto_limsup (f := atTop) (u := f)
    (IsCoboundedUnder.of_frequently_ge (Frequently.of_forall hf0))
    (isBoundedUnder_of_eventually_le (Eventually.of_forall hf1))
  exact le_of_tendsto_of_tendsto ((ha.comp hv).mul hfv) (hb.comp hv)
    (hv.eventually hab)

/-- An eventual comparison between bounded nonnegative sequences passes to
their upper limits, with a fixed nonnegative scale factor. -/
theorem limsup_le_mul_limsup {f g : ℕ → ℝ} {s : ℝ}
    (hf0 : ∀ n, 0 ≤ f n)
    (hg0 : ∀ n, 0 ≤ g n) (hg1 : ∀ n, g n ≤ 1)
    (hs : 0 ≤ s) (hfg : ∀ᶠ n in atTop, f n ≤ s * g n) :
    limsup f atTop ≤ s * limsup g atTop := by
  have hsg : IsBoundedUnder (· ≤ ·) atTop (fun n => s * g n) :=
    isBoundedUnder_of_eventually_le (a := s) (Eventually.of_forall fun n => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg1 n) hs)
  calc
    limsup f atTop ≤ limsup (fun n => s * g n) atTop :=
      limsup_le_limsup hfg
        (IsCoboundedUnder.of_frequently_ge (Frequently.of_forall hf0)) hsg
    _ ≤ s * limsup g atTop := by
      simpa only [Pi.mul_def, limsup_const] using
        (limsup_mul_le (f := atTop) (u := fun _ : ℕ => s) (v := g)
          (Frequently.of_forall fun _ : ℕ => hs)
          (isBoundedUnder_of_eventually_le (Eventually.of_forall fun _ : ℕ => le_refl s))
          (Eventually.of_forall hg0)
          (isBoundedUnder_of_eventually_le (Eventually.of_forall hg1)))

end LeanMachine.BoundedLimsup
