import TransposeFollowup.MobiusBoxCoefficient
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-! Probability averages of the actual SL2 representation, controlled by
second moments of arbitrary scalar coefficients. All integrals used in
Jensen's inequality are proved integrable. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem group_coefficient_energy_integrable (μ : Measure Group) [IsFiniteMeasure μ]
    (u v : ComplexL2) :
    Integrable (fun g : Group => ‖inner ℂ v (complexPullbackL2 g⁻¹ u)‖ ^ 2) μ := by
  apply (integrable_const ((‖v‖ * ‖u‖) ^ 2)).mono'
    (group_coefficient_energy_continuous u v).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro g
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb := norm_inner_le_norm (𝕜 := ℂ) v (complexPullbackL2 g⁻¹ u)
  rw [complexPullbackL2_norm] at hb
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

theorem groupActionAverage_inner_sq_le (μ : Measure Group) [IsProbabilityMeasure μ]
    (u v : ComplexL2) :
    ‖inner ℂ v (groupActionAverage μ u)‖ ^ 2 ≤
      ∫ g, ‖inner ℂ v (complexPullbackL2 g⁻¹ u)‖ ^ 2 ∂μ := by
  have hc : ConvexOn ℝ univ (fun z : ℂ => ‖z‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  have hi := (integrable_complexPullbackL2_inverse μ u).const_inner (𝕜 := ℂ) v
  have hj := hc.map_integral_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (ae_of_all μ (fun _ => mem_univ _)) hi (group_coefficient_energy_integrable μ u v)
  simpa only [Function.comp_apply, integral_inner (integrable_complexPullbackL2_inverse μ u) v,
    groupActionAverage] using hj

theorem groupActionAverage_norm_sq_le_of_coefficient_energy
    (μ : Measure Group) [IsProbabilityMeasure μ] (u : ComplexL2) {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ v : ComplexL2,
      (∫ g, ‖inner ℂ v (complexPullbackL2 g⁻¹ u)‖ ^ 2 ∂μ) ≤ C * ‖v‖ ^ 2) :
    ‖groupActionAverage μ u‖ ^ 2 ≤ C := by
  let w := groupActionAverage μ u
  have hb := (groupActionAverage_inner_sq_le μ u w).trans (henergy w)
  have hn : ‖inner ℂ w w‖ = ‖w‖ ^ 2 := by
    simp only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg w)]
  change ‖inner ℂ w w‖ ^ 2 ≤ C * ‖w‖ ^ 2 at hb
  rw [hn] at hb
  by_cases hw : w = 0
  · change ‖w‖ ^ 2 ≤ C
    simpa only [hw, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hC
  · have hp : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
    change ‖w‖ ^ 2 ≤ C
    exact (mul_le_mul_iff_of_pos_right hp).mp (by simpa only [pow_two] using hb)

end TransposeFollowup.RealMobius
