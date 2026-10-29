import LeanMachine.TailMoments
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Power envelopes and finite moments

A power envelope with decay exponent strictly above `k + 1` has a finite
`k`-th moment. The existing moment-to-tail estimate then gives the scaled
tail decay needed for common-envelope obstructions, without an integral
estimate. Summability allows either sign of the amplitude.
Power balancing also supplies one scale at which a sublinear covering
payment and a decaying residual rate both vanish.
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

/-- A positive width exponent strictly between the two power thresholds.
Neither the covering exponent nor its growth exponent must be nonnegative. -/
theorem exists_balanced_exponent {p s u : ℝ} (hp : 0 < p) (hs : s < 1)
    (hu : u < p * (1 - s)) :
    ∃ v : ℝ, 0 < v ∧ v < p ∧ u < v * (1 - s) := by
  have hden : 0 < 1 - s := sub_pos.mpr hs
  obtain ⟨v, hv, hvp⟩ := exists_between (max_lt hp ((div_lt_iff₀ hden).mpr hu))
  exact ⟨v, (le_max_left _ _).trans_lt hv, hvp,
    (div_lt_iff₀ hden).mp ((le_max_right _ _).trans_lt hv)⟩

/-- The three balanced-scale limits, on any positive base tending to infinity.
This is an algebraic consequence of Mathlib's negative-power limit. -/
theorem balanced_scale_limits {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hxlim : Tendsto x l atTop)
    {p s u v : ℝ} (hv : 0 < v) (hvp : v < p) (hu : u < v * (1 - s))
    (A H : ℝ) :
    Tendsto (fun i => x i ^ (-v)) l (𝓝 0) ∧
    Tendsto (fun i => x i ^ (-v) * (H * x i ^ u * (x i ^ (-v)) ^ (-s)))
      l (𝓝 0) ∧
    Tendsto (fun i => (A / x i ^ p) / x i ^ (-v)) l (𝓝 0) := by
  refine ⟨(tendsto_rpow_neg_atTop hv).comp hxlim, ?_, ?_⟩
  · convert ((tendsto_rpow_neg_atTop (sub_pos.mpr hu)).comp hxlim).const_mul H
        using 1
    · funext i
      simp only [Function.comp_apply]
      rw [← Real.rpow_mul (hx i).le,
        show -(v * (1 - s) - u) = -v + u + (-v) * (-s) by ring,
        Real.rpow_add (hx i), Real.rpow_add (hx i)]
      ring
    · simp
  · convert ((tendsto_rpow_neg_atTop (sub_pos.mpr hvp)).comp hxlim).const_mul A
        using 1
    · funext i
      simp only [Function.comp_apply]
      rw [div_div, ← Real.rpow_add (hx i),
        show p + -v = p - v by ring, Real.rpow_neg (hx i).le]
      rfl
    · simp

end LeanMachine.PowerEnvelope
