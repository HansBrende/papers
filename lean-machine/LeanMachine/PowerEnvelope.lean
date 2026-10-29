import LeanMachine.TailMoments
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Power envelopes and finite moments

A power envelope with decay exponent strictly above `k + 1` has a finite
`k`-th moment. The existing moment-to-tail estimate then gives the scaled
tail decay needed for common-envelope obstructions, without an integral
estimate. Summability allows either sign of the amplitude.
-/

namespace LeanMachine.PowerEnvelope

open Filter
open scoped BigOperators Topology

/-- A decay exponent above `k + 1` makes the `k`-th moment summable.
The amplitude may be any real number. -/
theorem summable_moment (k : ℕ) {p : ℝ} (hp : (k : ℝ) + 1 < p) (H : ℝ) :
    Summable (fun i : ℕ => (i + 1 : ℝ) ^ k * (H / (i + 1 : ℝ) ^ p)) := by
  have hpow : Summable (fun i : ℕ => (i + 1 : ℝ) ^ ((k : ℝ) - p)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr
        (show (k : ℝ) - p < -1 by linarith))
  refine (hpow.mul_left H).congr fun i => ?_
  rw [Real.rpow_sub (by positivity), Real.rpow_natCast]
  ring

/-- In particular, every power envelope with exponent above one is summable. -/
theorem summable {p : ℝ} (hp : 1 < p) (H : ℝ) :
    Summable (fun i : ℕ => H / (i + 1 : ℝ) ^ p) := by
  simpa using summable_moment 0 (by simpa using hp) H

/-- Every fixed nonnegative shift of the polynomially scaled tail tends
to zero once the decay exponent exceeds the moment threshold. -/
theorem polynomial_tail_tendsto_zero (k : ℕ) {p H : ℝ}
    (hp : (k : ℝ) + 1 < p) (hH : 0 ≤ H) (shift : ℝ) (hshift : 0 ≤ shift) :
    Tendsto (fun R : ℕ => (R + shift : ℝ) ^ k *
      ∑' i : ℕ, H / ((i + R : ℕ) + 1 : ℝ) ^ p) atTop (𝓝 0) := by
  exact TailMoments.polynomial_tail_tendsto_zero
    (h := fun i : ℕ => H / (i + 1 : ℝ) ^ p) k shift hshift
    (fun i => div_nonneg hH (Real.rpow_nonneg (by positivity) p))
    (summable_moment k hp H)

end LeanMachine.PowerEnvelope
