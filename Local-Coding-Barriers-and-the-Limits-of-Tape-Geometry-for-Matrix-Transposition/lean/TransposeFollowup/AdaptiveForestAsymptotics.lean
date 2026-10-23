import TransposeFollowup.AdaptiveForestLaw

/-! Near-full-payload expected cost for actual forest-code families. The
only vanishing quantities are forward width and the state/source/helper
information deficit; no numerical protocol budget is assumed. -/

namespace TransposeFollowup.AdaptiveForestLaw

open Classical Filter
open scoped BigOperators Topology
set_option autoImplicit false

theorem near_linear {Delta : ℕ} (b sigma : ℕ → ℕ)
    (F : ∀ d, AdaptiveForestLaw d (b d) (sigma d) Delta)
    (hb : ∀ d, 0 < d → 0 < b d)
    (hwidth : Tendsto (fun d => (sigma d : ℝ) / d) atTop (𝓝 0))
    (hinfo : Tendsto (fun d => ((F d).stateBits + (F d).deficit) / (d*d*b d : ℕ)) atTop (𝓝 0)) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ d in atTop,
      (1-eps) * (d*d*b d : ℕ) ≤ (F d).expectedLength := by
  let delta := max 2 Delta
  have hw : Tendsto (fun d => (1+2*(sigma d:ℝ))/(d:ℝ)) atTop (𝓝 0) := by
    convert (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).add (hwidth.const_mul 2) using 1
    · funext d
      ring
    · norm_num
  have hr := adaptive_forest_near_linear
    (fun d => (F d).expectedLength / (d*d*b d:ℕ))
    (fun d => (1+2*(sigma d:ℝ))/(d:ℝ))
    (fun d => ((F d).stateBits+(F d).deficit)/(d*d*b d:ℕ))
    (fun R => (delta:ℝ)^(2*R))
    (fun R M => (bucketPatternCount M (delta^R):ℝ)*((delta:ℝ)^R+1))
    hw hinfo (fun R => by positivity)
  have hbudget : ∀ R : ℕ, 0 < R → ∀ M : ℕ, 0 < M →
      ∀ᶠ d in atTop,
        1 - (delta:ℝ)^(2*R) * (1/(M:ℝ)+(1+2*(sigma d:ℝ))/(d:ℝ)) -
          ((bucketPatternCount M (delta^R):ℝ)*((delta:ℝ)^R+1)) *
            (((F d).stateBits+(F d).deficit)/(d*d*b d:ℕ)) ≤
          (1+1/(R:ℝ))*((F d).expectedLength/(d*d*b d:ℕ)) := by
    intro R hR M hM
    filter_upwards [eventually_ge_atTop 1] with d hd
    have hd0 : 0 < d := by omega
    have hb0 := hb d hd0
    have hP : (0:ℝ) < (d*d*b d:ℕ) := by positivity
    have hn := adaptive_forest_normalized_budget d M R (sigma d) hd0 hM
      (d*b d:ℕ) (F d).expectedLength ((delta:ℝ)^(2*R))
      (bucketPatternCount M (delta^R)) ((delta:ℝ)^R) (F d).stateBits (F d).deficit
      (by positivity) (by positivity) ((F d).budget R M hR hM hd0)
    have he : (d:ℝ)*(d*b d:ℕ) = (d*d*b d:ℕ) := by push_cast; ring
    rw [he] at hn
    have hi : (bucketPatternCount M (delta^R):ℝ)*
        (((delta:ℝ)^R+1)*(F d).stateBits+(F d).deficit)/(d*d*b d:ℕ) ≤
        ((bucketPatternCount M (delta^R):ℝ)*((delta:ℝ)^R+1))*
          (((F d).stateBits+(F d).deficit)/(d*d*b d:ℕ)) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hP.le
      nlinarith [(F d).deficit_nonneg,
        mul_nonneg (show (0:ℝ) ≤ (bucketPatternCount M (delta^R):ℝ)*(delta:ℝ)^R by positivity)
          (F d).deficit_nonneg]
    linarith
  intro eps heps
  filter_upwards [hr hbudget eps heps, eventually_ge_atTop 1] with d hh hd
  have hd0 : 0 < d := by omega
  have hb0 := hb d hd0
  exact (le_div_iff₀ (by positivity : (0:ℝ) < (d*d*b d:ℕ))).mp hh

end TransposeFollowup.AdaptiveForestLaw
