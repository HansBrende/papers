import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

/-! The actual dyadic level-count bound is logarithmic in inverse scale.
One uniform threshold absorbs that logarithm and any fixed constant into
an arbitrarily small negative power of the scale. -/
namespace TransposeFollowup
open Classical Filter Set
open scoped Topology
set_option autoImplicit false

theorem covering_level_log_bound {η C θ V : ℝ} {N : ℕ}
    (hη : 0 < η) (hηhalf : η ≤ 1 / 2) (hC : C ≤ η⁻¹ ^ 3)
    (hθ : η ≤ θ) (hV : 1 ≤ V)
    (hN : (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / (θ * V)))) :
    (N : ℝ) ≤ 5 + 4 * Real.logb 2 η⁻¹ := by
  have hθ0 : 0 < θ := hη.trans_le hθ
  have hden : η ≤ θ * V := hθ.trans (le_mul_of_one_le_right hθ0.le hV)
  have hi : 2 ≤ η⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hη]
    linarith
  have hr : 16 * C / (θ * V) ≤ 16 * η⁻¹ ^ 4 := by
    calc
      _ ≤ 16 * η⁻¹ ^ 3 / (θ * V) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hC (by norm_num)) (by positivity)
      _ ≤ 16 * η⁻¹ ^ 3 / η := div_le_div_of_nonneg_left (by positivity) hη hden
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hpow : 1 ≤ η⁻¹ ^ 4 := one_le_pow₀ (by linarith)
  have hm : max 1 (16 * C / (θ * V)) ≤ 16 * η⁻¹ ^ 4 := max_le (by linarith) hr
  have hl2 : Real.logb 2 (2 : ℝ) = 1 := by
    rw [Real.logb]
    exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hl16 : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow, hl2]
    norm_num
  calc
    (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / (θ * V))) := hN
    _ ≤ 1 + Real.logb 2 (16 * η⁻¹ ^ 4) := add_le_add le_rfl
      (Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hm)
    _ = _ := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, hl16]
      ring

theorem covering_level_log_bound_of_powers {η C V s κ γ : ℝ} {N : ℕ}
    (hη : 0 < η) (hηhalf : η ≤ 1 / 2) (hsone : s ≤ 1) (hκ : 0 ≤ κ) (hγ : 0 ≤ γ)
    (hC : C ≤ η ^ (-3 + κ)) (hV : η ^ (-γ) ≤ V)
    (hN : (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / (η ^ s * V)))) :
    (N : ℝ) ≤ 5 + 4 * Real.logb 2 η⁻¹ := by
  have hηone : η ≤ 1 := by linarith
  have hθlower : η ≤ η ^ s := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hη hηone hsone
  have hVone : 1 ≤ V := by
    have hh : 1 ≤ η ^ (-γ) := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_ge hη hηone (show -γ ≤ 0 by linarith)
    exact hh.trans hV
  have hCcoarse : C ≤ η⁻¹ ^ 3 := hC.trans (by
    calc
      η ^ (-3 + κ) ≤ η ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith)
      _ = η⁻¹ ^ 3 := by
        exact (Real.rpow_neg hη.le (3 : ℝ)).trans
          ((congrArg Inv.inv (Real.rpow_natCast η 3)).trans (inv_pow η 3).symm))
  exact covering_level_log_bound hη hηhalf hCcoarse hθlower hVone hN

theorem exists_uniform_covering_loss_threshold {s : ℝ} (hs : 0 < s) (C : ℝ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 2 ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ → C ≤ η ^ (-s) ∧
        5 + 4 * Real.logb 2 η⁻¹ ≤ η ^ (-s) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he := (isLittleO_log_rpow_nhdsGT_zero (neg_lt_zero.mpr hs)).def
    (by positivity : 0 < Real.log 2 / 9)
  have hc := (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hs)).eventually
    (eventually_ge_atTop C)
  obtain ⟨u, hu, hinterval⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (he.and hc)
  change 0 < u at hu
  refine ⟨min (u / 2) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro η hη hηsmall
  have hηhalf : η ≤ 1 / 2 := hηsmall.trans (min_le_right _ _)
  have hηu : η < u := lt_of_le_of_lt (hηsmall.trans (min_le_left _ _)) (by linarith)
  obtain ⟨hb, hconst⟩ := hinterval ⟨hη, hηu⟩
  have hp : 0 ≤ η ^ (-s) := Real.rpow_nonneg hη.le _
  have hln : Real.log η ≤ 0 := Real.log_nonpos hη.le (by linarith)
  simp only [Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonpos hln] at hb
  have hlog : 1 ≤ Real.logb 2 η⁻¹ := by
    have hi : 2 ≤ η⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hη]
      linarith
    have hh := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) (by norm_num) hi
    have hl : Real.logb 2 (2 : ℝ) = 1 := by rw [Real.logb]; exact div_self hl2.ne'
    rwa [hl] at hh
  refine ⟨hconst, ?_⟩
  calc
    5 + 4 * Real.logb 2 η⁻¹ ≤ 9 * Real.logb 2 η⁻¹ := by linarith
    _ ≤ η ^ (-s) := by
      rw [Real.logb, Real.log_inv, ← mul_div_assoc, div_le_iff₀ hl2]
      nlinarith [hb]

end TransposeFollowup
