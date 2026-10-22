import TransposeFollowup.ReextractionPowerBounds

/-! Cubic trace-budget contradiction reused by the final spanning-profile
exclusion. The earlier nilpotent-only route is preserved in the research
archive and is no longer part of the active proof chain. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false

theorem cubic_trace_budget_contradiction {η θ gain U₀ W₀ N T m : ℝ}
    (hη : 0 < η) (hU : 0 ≤ U₀) (hm : 0 ≤ m)
    (hretain : N ≤ W₀ * η ^ (-(143 * θ)) * m ^ 3)
    (hupper : T ^ 3 ≤ U₀ * η ^ (-(548 * θ)) * N)
    (hbudget : 250 ^ 3 * U₀ * W₀ * η ^ (3 * gain - 691 * θ) ≤ 1)
    (hgrowth : η ^ (-gain) * m < 250 * T) : False := by
  have hp : η ^ (-(548 * θ)) * η ^ (-(143 * θ)) = η ^ (-(691 * θ)) := by
    rw [← Real.rpow_add hη]
    congr 1
    ring
  have hgain : η ^ (3 * gain - 691 * θ) * (η ^ (-gain)) ^ 3 = η ^ (-(691 * θ)) := by
    rw [← Real.rpow_mul_natCast hη.le, ← Real.rpow_add hη]
    congr 1
    norm_num
    ring
  have hbound : (250 * T) ^ 3 ≤ (η ^ (-gain) * m) ^ 3 := by
    calc
      _ = 250 ^ 3 * T ^ 3 := mul_pow _ _ _
      _ ≤ 250 ^ 3 * (U₀ * η ^ (-(548 * θ)) * N) :=
        mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ ≤ 250 ^ 3 * (U₀ * η ^ (-(548 * θ)) * (W₀ * η ^ (-(143 * θ)) * m ^ 3)) := by
        gcongr
      _ = (250 ^ 3 * U₀ * W₀) * (η ^ (-(548 * θ)) * η ^ (-(143 * θ))) * m ^ 3 := by ring
      _ = (250 ^ 3 * U₀ * W₀ * η ^ (3 * gain - 691 * θ)) * (η ^ (-gain) * m) ^ 3 := by
        rw [hp, ← hgain, mul_pow]
        ring
      _ ≤ 1 * (η ^ (-gain) * m) ^ 3 := mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = _ := one_mul _
  exact (not_lt_of_ge hbound) (pow_lt_pow_left₀ hgrowth (by positivity) (by norm_num : (3 : ℕ) ≠ 0))


end TransposeFollowup.SL2Projection
