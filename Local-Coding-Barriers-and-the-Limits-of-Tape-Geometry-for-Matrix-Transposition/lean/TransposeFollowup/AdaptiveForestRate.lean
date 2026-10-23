import TransposeFollowup.AdaptiveForestLaw
import TransposeFollowup.AdaptiveBankRateLimit

/-! The explicit asymptotic rate for actual adaptive forest strategies, with
fixed forward width and row-graph degree. State and combined source/helper
deficit are bounded by constant multiples of one raw row. -/

namespace TransposeFollowup.AdaptiveForestLaw

open Filter
open scoped Topology
set_option autoImplicit false

theorem logarithmic_logarithmic_rate {Delta sigma : ℕ} (b : ℕ → ℕ)
    (F : ∀ d, AdaptiveForestLaw d (b d) sigma Delta)
    (hb : ∀ d, 0 < d → 0 < b d)
    (As Ad : ℝ) (hAs : 0 ≤ As) (hAd : 0 ≤ Ad)
    (hs : ∀ᶠ d in atTop, (F d).stateBits ≤ As*(d*b d : ℕ))
    (hdef : ∀ᶠ d in atTop, (F d).deficit ≤ Ad*(d*b d : ℕ)) :
    ∀ᶠ d : ℕ in atTop,
      (1-(8*Real.log ((max 2 Delta : ℕ):ℝ)+1)/Real.log (Real.logb 2 (d:ℝ))) *
        (d*d*b d : ℕ) ≤ (F d).expectedLength := by
  let delta := max 2 Delta
  have ht : Tendsto (fun d : ℕ => Real.logb 2 (d:ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).comp tendsto_natCast_atTop_atTop
  have herr := adaptiveRateError_log_t_tendsto delta sigma (le_max_left _ _) As Ad hAs hAd
  have hevent : ∀ᶠ d : ℕ in atTop,
      adaptiveRateError d delta sigma As Ad * Real.log (Real.logb 2 (d:ℝ)) ≤ 1 :=
    herr.eventually_le_const (by norm_num)
  filter_upwards [hs, hdef, ht.eventually_ge_atTop ((delta:ℝ)^8),
    ht.eventually_ge_atTop 2, eventually_ge_atTop (1:ℕ), hevent] with d hsd hdd htd ht2 hd he
  have hd0 : 0 < d := by omega
  have hb0 := hb d hd0
  have hlog : 0 < Real.log (Real.logb 2 (d:ℝ)) :=
    Real.log_pos (by linarith)
  have herror : adaptiveRateError d delta sigma As Ad ≤
      1/Real.log (Real.logb 2 (d:ℝ)) := (le_div_iff₀ hlog).mpr he
  have hrate := (F d).explicit_rate hd hb0 htd As Ad hAs hAd hsd hdd
  have hratio : 1-(8*Real.log (delta:ℝ)+1)/Real.log (Real.logb 2 (d:ℝ)) ≤
      (F d).expectedLength/(d*d*b d:ℕ) := by
    rw [add_div]
    dsimp only [delta] at herror ⊢
    linarith
  exact (le_div_iff₀ (by positivity : (0:ℝ)<(d*d*b d:ℕ))).mp hratio

end TransposeFollowup.AdaptiveForestLaw
