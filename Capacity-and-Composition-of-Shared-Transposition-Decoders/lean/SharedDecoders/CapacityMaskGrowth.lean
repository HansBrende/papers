import SharedDecoders.CapacityMaskProbabilityCorollaries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The growing-class range and vanishing empty-label probability -/

namespace SharedDecoders.CapacityMaskProbability

open Filter
open scoped Topology

/-- The explicit class-count restriction implied by the stated logarithmic
choice. The lower bound on the logarithm is needed only for the simpler
`sqrt d` envelope below. -/
theorem growing_class_bound (d : ℕ) (hd : 1<d) (M : ℝ) (hM : 0≤M)
    (h : M*logDeviation 6 d≤1) : M≤Real.sqrt ((d : ℝ)/(6*Real.log d)) := by
  have hd0 : (0 : ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hlog : 0<Real.log d := Real.log_pos (by exact_mod_cast hd)
  have hη : 0≤logDeviation 6 d := logDeviation_nonneg _ _
  have hs : (logDeviation 6 d)^2*(d : ℝ)=6*Real.log d := by
    rw [logDeviation_sq 6 (by norm_num) d (by omega)]
    field_simp
  have hh : M^2*(logDeviation 6 d)^2≤1 := by nlinarith [mul_nonneg hM hη]
  have hm := mul_le_mul_of_nonneg_right hh (le_of_lt hd0)
  have he : M^2*(logDeviation 6 d)^2*d=M^2*(6*Real.log d) := by rw [mul_assoc,hs]
  rw [he] at hm
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<6*Real.log d)).mpr
  simpa only [one_mul] using hm

theorem growing_class_sqrt_bound (d : ℕ) (hd : 1<d) (hlog : 1/6≤Real.log d)
    (M : ℝ) (hM : 0≤M) (h : M*logDeviation 6 d≤1) : M≤Real.sqrt d := by
  have hh := growing_class_bound d hd M hM h
  have hd0 : (0 : ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hden : (0 : ℝ)<6*Real.log d := by linarith
  have hquot : (d : ℝ)/(6*Real.log d)≤d := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hlog,hd0]
  exact hh.trans (Real.sqrt_le_sqrt hquot)

theorem growing_reciprocal_bound (d : ℕ) (hd : 1<d) (M : ℝ) (hM : 0<M)
    (h : M*logDeviation 6 d≤1) : Real.sqrt (6*(d : ℝ)*Real.log d)≤(d : ℝ)/M := by
  have hd0 : (0 : ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hη : 0≤logDeviation 6 d := logDeviation_nonneg _ _
  have hs : ((d : ℝ)*logDeviation 6 d)^2=6*(d : ℝ)*Real.log d := by
    rw [mul_pow,logDeviation_sq 6 (by norm_num) d (by omega)]
    field_simp
  rw [← hs,Real.sqrt_sq_eq_abs,abs_of_nonneg (mul_nonneg (le_of_lt hd0) hη)]
  apply (le_div_iff₀ hM).mpr
  have hh := mul_le_mul_of_nonneg_left h (le_of_lt hd0)
  nlinarith only [hh]

theorem empty_bound_explicit (d : ℕ) (hd : 1<d) (hlog : 1/6≤Real.log d)
    (M : ℝ) (hM : 0<M) (h : M*logDeviation 6 d≤1) :
    M*Real.exp (-(d : ℝ)/M)≤
      Real.sqrt d*Real.exp (-Real.sqrt (6*(d : ℝ)*Real.log d)) := by
  have hsmall := growing_class_sqrt_bound d hd hlog M (le_of_lt hM) h
  have hlarge := growing_reciprocal_bound d hd M hM h
  exact mul_le_mul hsmall (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hlarge))
    (le_of_lt (Real.exp_pos _)) (Real.sqrt_nonneg _)

theorem empty_bound_sqrt (d : ℕ) (hd : 1<d) (hlog : 1/6≤Real.log d)
    (M : ℝ) (hM : 0<M) (h : M*logDeviation 6 d≤1) :
    M*Real.exp (-(d : ℝ)/M)≤Real.sqrt d*Real.exp (-Real.sqrt d) := by
  have hh := empty_bound_explicit d hd hlog M hM h
  have hs : (d : ℝ)≤6*(d : ℝ)*Real.log d := by
    have hd0 : (0 : ℝ)≤d := Nat.cast_nonneg _
    nlinarith only [hlog,hd0]
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg (Real.sqrt_le_sqrt hs))) (Real.sqrt_nonneg _))

/-- The empty-class union bound actually tends to zero throughout the claimed
growing range. No rate of growth for `M` is supplied beyond `M η_d ≤ 1`. -/
theorem empty_probability_bound_tendsto (M : ℕ → ℕ)
    (hM : ∀ᶠ d in atTop, 0<M d)
    (h : ∀ᶠ d in atTop, (M d : ℝ)*logDeviation 6 d≤1) :
    Tendsto (fun d : ℕ => (M d : ℝ)*Real.exp (-(d : ℝ)/(M d : ℝ))) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun d : ℕ => Real.sqrt (d : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun d : ℕ => Real.sqrt (d : ℝ)*Real.exp (-Real.sqrt (d : ℝ)))
      atTop (nhds 0) := by
    simpa only [pow_one,Function.comp_def] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hsqrt
  have hlog : ∀ᶠ d : ℕ in atTop, (1/6 : ℝ)≤Real.log d :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1/6)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun d => by positivity)
  · filter_upwards [hM,h,hlog,eventually_gt_atTop 1] with d hMd hd hld hd1
    exact empty_bound_sqrt d hd1 hld (M d) (by exact_mod_cast hMd) hd

end SharedDecoders.CapacityMaskProbability
