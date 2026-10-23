import TransposeFollowup.AdaptiveBankRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt

/-! The explicit adaptive-forest error is negligible even after multiplication
by log(log₂ d). The comparison is with a single exponential in sqrt(log₂ d). -/

namespace TransposeFollowup

open Filter
open scoped Topology
set_option autoImplicit false

noncomputable def adaptiveRateMajorant (sigma : ℕ) (As Ad t : ℝ) : ℝ :=
  (3 + 2*(sigma : ℝ) + 2*As + Ad) * t *
    Real.exp (-(Real.log 2 / 4) * Real.sqrt t)

theorem adaptiveRateError_le_majorant (d delta sigma : ℕ)
    (hd : 0 < d) (hdelta : 2 ≤ delta) (As Ad : ℝ) (hAs : 0 ≤ As) (hAd : 0 ≤ Ad)
    (ht : (delta : ℝ)^8 ≤ Real.logb 2 (d : ℝ)) :
    adaptiveRateError d delta sigma As Ad ≤
      adaptiveRateMajorant sigma As Ad (Real.logb 2 (d : ℝ)) := by
  let t := Real.logb 2 (d : ℝ)
  let K := delta ^ adaptiveRateRadius delta t
  let u := Real.sqrt t
  let e := Real.exp (-(Real.log 2 / 4) * u)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdelta0 : 0 < delta := by omega
  have hdelta1 : (1 : ℝ) ≤ delta := by exact_mod_cast (show 1 ≤ delta by omega)
  have ht1 : 1 ≤ t := (one_le_pow₀ hdelta1).trans ht
  have ht0 : 0 ≤ t := by linarith
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = t := Real.sq_sqrt ht0
  have hut : u ≤ t := Real.sqrt_le_self_iff.mpr (Or.inr ht1)
  have hk1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hdelta0))
  have hk1R : (1 : ℝ) ≤ K := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < K := by linarith
  have hk4 := (adaptiveRateRadius_bounds delta hdelta t ht).2.2
  change (K : ℝ)^4 ≤ t at hk4
  have hk2 : (K : ℝ)^2 ≤ t := by
    have hpow : K^2 ≤ K^4 := Nat.pow_le_pow_right hk1 (by omega)
    exact (by exact_mod_cast hpow : (K : ℝ)^2 ≤ (K : ℝ)^4).trans hk4
  have hku : (K : ℝ) ≤ u := Real.le_sqrt_of_sq_le hk2
  have hkt : (K : ℝ) ≤ t := hku.trans hut
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hld : Real.log (d : ℝ) = t * Real.log 2 := by
    dsimp [t, Real.logb]
    field_simp
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hx : (d : ℝ)^(-(1/(4*(K : ℝ)))) ≤ e := by
    rw [Real.rpow_def_of_pos hd0]
    apply Real.exp_le_exp.mpr
    have hprod : u*(K : ℝ) ≤ t := by nlinarith [mul_le_mul_of_nonneg_left hku hu0]
    have hquot : u/4 ≤ t/(4*(K : ℝ)) := by
      apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hquot hl2.le
    change Real.log (d : ℝ) * -(1/(4*(K : ℝ))) ≤ -(Real.log 2/4)*u
    rw [hld]
    calc
      _ = -(Real.log 2 * (t/(4*(K : ℝ)))) := by ring
      _ ≤ -(Real.log 2 * (u/4)) := neg_le_neg hmul
      _ = _ := by ring
  have hdinv : (d : ℝ)⁻¹ ≤ e := by
    rw [← Real.exp_log hd0, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    rw [hld]
    nlinarith [mul_le_mul_of_nonneg_left hut hl2.le]
  have hsqrtinv : ((d : ℝ)^(1/2 : ℝ))⁻¹ ≤ e := by
    rw [Real.rpow_def_of_pos hd0, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    rw [hld]
    nlinarith [mul_le_mul_of_nonneg_left hut hl2.le]
  have hfirst : (K : ℝ)^2 * (2*(d : ℝ)^(-(1/(4*(K : ℝ))))) ≤ 2*t*e := by
    have h := mul_le_mul hk2 (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity) ht0
    nlinarith
  have hsecond : (K : ℝ)^2 * ((1+2*(sigma : ℝ))/d) ≤ (1+2*(sigma : ℝ))*t*e := by
    have h := mul_le_mul hk2 hdinv (by positivity) ht0
    have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1+2*(sigma : ℝ))
    simpa only [div_eq_mul_inv] using (by nlinarith :
      (K : ℝ)^2*((1+2*(sigma : ℝ))*(d : ℝ)⁻¹) ≤ (1+2*(sigma : ℝ))*t*e)
  have hcoef : ((K : ℝ)+1)*As+Ad ≤ (2*As+Ad)*t := by
    nlinarith [mul_le_mul_of_nonneg_right hkt hAs,
      mul_le_mul_of_nonneg_left ht1 hAs, mul_le_mul_of_nonneg_left ht1 hAd]
  have hthird : (((K : ℝ)+1)*As+Ad)/(d : ℝ)^(1/2 : ℝ) ≤ (2*As+Ad)*t*e := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hcoef hsqrtinv (by positivity) (by positivity)
  change (K : ℝ)^2 * (2*(d : ℝ)^(-(1/(4*(K : ℝ))))+(1+2*(sigma : ℝ))/d) +
    (((K : ℝ)+1)*As+Ad)/(d : ℝ)^(1/2 : ℝ) ≤
      (3+2*(sigma : ℝ)+2*As+Ad)*t*e
  nlinarith

theorem adaptiveRateMajorant_mul_t_tendsto (sigma : ℕ) (As Ad : ℝ) :
    Tendsto (fun t : ℝ => adaptiveRateMajorant sigma As Ad t * t) atTop (𝓝 0) := by
  let C := 3 + 2*(sigma : ℝ) + 2*As + Ad
  have hc : 0 < Real.log 2 / 4 := by positivity
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 (Real.log 2/4) hc).comp
    Real.tendsto_sqrt_atTop
  have hh : Tendsto (fun t : ℝ => C * (Real.sqrt t)^4 *
      Real.exp (-(Real.log 2/4)*Real.sqrt t)) atTop (𝓝 0) := by
    simpa [Real.rpow_natCast, mul_assoc] using h.const_mul C
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hs : (Real.sqrt t)^4 = t^2 := by nlinarith [Real.sq_sqrt ht]
  rw [hs]
  dsimp [adaptiveRateMajorant, C]
  ring

theorem adaptiveRateError_log_t_tendsto (delta sigma : ℕ) (hdelta : 2 ≤ delta)
    (As Ad : ℝ) (hAs : 0 ≤ As) (hAd : 0 ≤ Ad) :
    Tendsto (fun d : ℕ => adaptiveRateError d delta sigma As Ad *
      Real.log (Real.logb 2 (d : ℝ))) atTop (𝓝 0) := by
  let t := fun d : ℕ => Real.logb 2 (d : ℝ)
  have ht : Tendsto t atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hlim := (adaptiveRateMajorant_mul_t_tendsto sigma As Ad).comp ht
  have hlo : ∀ᶠ d : ℕ in atTop, 0 ≤ adaptiveRateError d delta sigma As Ad * Real.log (t d) := by
    filter_upwards [ht.eventually_ge_atTop 1] with d hd
    have he : 0 ≤ adaptiveRateError d delta sigma As Ad := by
      dsimp [adaptiveRateError]
      positivity
    exact mul_nonneg he (Real.log_nonneg hd)
  have hhi : ∀ᶠ d : ℕ in atTop,
      adaptiveRateError d delta sigma As Ad * Real.log (t d) ≤
        adaptiveRateMajorant sigma As Ad (t d) * t d := by
    filter_upwards [ht.eventually_ge_atTop ((delta : ℝ)^8), ht.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℕ)] with d hth ht1 hd
    have he := adaptiveRateError_le_majorant d delta sigma (by omega) hdelta As Ad hAs hAd hth
    have hlog : Real.log (t d) ≤ t d := Real.log_le_self (by linarith)
    have hmaj : 0 ≤ adaptiveRateMajorant sigma As Ad (t d) := by
      dsimp [adaptiveRateMajorant]
      positivity
    exact mul_le_mul he hlog (Real.log_nonneg ht1) hmaj
  exact squeeze_zero' hlo hhi hlim

end TransposeFollowup
