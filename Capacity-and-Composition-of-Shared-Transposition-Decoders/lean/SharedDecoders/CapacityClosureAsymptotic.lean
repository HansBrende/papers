import SharedDecoders.CapacityClosure
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semifield

/-! The finite error is sublinear for the stated logarithmic number of rounds. -/

namespace SharedDecoders.CapacityClosure

open Filter
open scoped Topology

def rounds (d : ℕ) : ℕ := Nat.log 2 d / 2

theorem rounds_eq_floor (d : ℕ) : rounds d = ⌊Real.logb 2 d / 2⌋₊ := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_div_natCast,
    Real.natFloor_logb_natCast]
  rfl

theorem rounds_pos {d : ℕ} (hd : 4 ≤ d) : 0 < rounds d := by
  have hh := Nat.le_log_of_pow_le (b := 2) (x := 2) (by omega) (by simpa using hd)
  dsimp [rounds]
  omega

theorem rounds_le_log (d : ℕ) : rounds d ≤ Nat.log 2 d := Nat.div_le_self _ _

theorem rounds_tendsto : Tendsto rounds atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop (2^(2*n))] with d hd
  have hh := Nat.le_log_of_pow_le (by omega : 1 < 2) hd
  dsimp [rounds]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
  nlinarith only [hh]

theorem sqrt_two_gt_one : 1 < Real.sqrt 2 := by
  have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem error_nonneg (d R : ℕ) : 0 ≤ error d R := by
  have hp : 1 ≤ (Real.sqrt 2)^R := one_le_pow₀ sqrt_two_gt_one.le
  have hden : 0 < Real.sqrt 2-1 := sub_pos.mpr sqrt_two_gt_one
  dsimp [error]
  positivity

/-- A coarse bound is enough: the geometric numerator costs at most `d`.
This also applies to any positive round count at most `log₂ d`. -/
theorem error_ratio_le {d R : ℕ} (hd : 0 < d) (hR : 0 < R)
    (hlog : R ≤ Nat.log 2 d) :
    error d R / d ≤ (1/10+7/(5*(Real.sqrt 2-1)))/(R : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hk : 0 < Real.sqrt 2-1 := sub_pos.mpr sqrt_two_gt_one
  have hpow : (2 : ℝ)^R ≤ d := by
    exact_mod_cast Nat.pow_le_of_le_log (Nat.ne_of_gt hd) hlog
  have hsquare : ((Real.sqrt 2)^R)^2 = (2 : ℝ)^R := by
    rw [← pow_mul, Nat.mul_comm R 2, pow_mul, Real.sq_sqrt (by norm_num)]
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  have hn := Real.sqrt_nonneg (d : ℝ)
  have ht : 0 ≤ (Real.sqrt 2)^R := by positivity
  have hle : (Real.sqrt 2)^R ≤ Real.sqrt d := by nlinarith only [hpow, hsquare, hsq, hn, ht]
  have hprod : Real.sqrt d*((Real.sqrt 2)^R-1) ≤ (d : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hle hn
    nlinarith only [hh, hsq, hn]
  have hscaled := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 7/(5*(Real.sqrt 2-1)) by positivity)
  apply (div_le_div_iff₀ hd' hR').mpr
  have he : error d R * (R : ℝ) = (d : ℝ)/10+
      7/(5*(Real.sqrt 2-1))*Real.sqrt d*((Real.sqrt 2)^R-1) := by
    dsimp [error]
    field_simp [ne_of_gt hR', ne_of_gt hk]
  rw [he]
  nlinarith only [hscaled]

theorem error_ratio_tendsto :
    Tendsto (fun d : ℕ => error d (rounds d)/(d : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun d => div_nonneg (error_nonneg d _) (Nat.cast_nonneg _)))
  · filter_upwards [eventually_ge_atTop 4] with d hd
    exact error_ratio_le (by omega) (rounds_pos hd) (rounds_le_log d)
  · exact (tendsto_const_div_atTop_nhds_zero_nat
      (1/10+7/(5*(Real.sqrt 2-1)) : ℝ)).comp rounds_tendsto

/-- A width-independent vanishing correction to the rate, with the defect
retained in its original binary units. -/
noncomputable def rateError (d : ℕ) : ℝ := 1/(d : ℝ)+error d (rounds d)/(d : ℝ)

theorem rateError_tendsto : Tendsto rateError atTop (𝓝 0) := by
  change Tendsto (fun d : ℕ => 1/(d : ℝ)+error d (rounds d)/(d : ℝ)) atTop (𝓝 0)
  convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add error_ratio_tendsto using 1
  norm_num

theorem capacity_rate_bound {d b : ℕ} [NeZero d]
    {C : Submodule CapacityIntervals.Bit (BinaryState d b)} {p : ZMod d → Bool}
    (hC : IsSharedCode CapacityIntervals.Bit p C) {r : Bool → ZMod d}
    (hr : ∀ a, p (r a) = a) (hd : 4 ≤ d) (hb : 0 < b) :
    (Module.finrank CapacityIntervals.Bit C : ℝ)/((b : ℝ)*(d : ℝ)^2) ≤
      3/5+rateError d+13/5*(defect (residual C p r) : ℝ)/((b : ℝ)*(d : ℝ)^2) := by
  have hh := capacity_bound hC hr (rounds d) (rounds_pos hd)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  apply (div_le_iff₀ (by positivity : 0 < (b : ℝ)*(d : ℝ)^2)).mpr
  have he : (3/5+rateError d+13/5*(defect (residual C p r) : ℝ)/((b : ℝ)*(d : ℝ)^2))*
      ((b : ℝ)*(d : ℝ)^2) = 3/5*(b : ℝ)*(d : ℝ)^2+(b : ℝ)*d+
        (b : ℝ)*d*error d (rounds d)+13/5*(defect (residual C p r) : ℝ) := by
    dsimp [rateError]
    field_simp
    ring
  rw [he]
  exact hh


/-- The asymptotic coefficient is uniform over widths, sources, partitions and
representatives; only the displayed defect survives as an extra parameter. -/
theorem uniform_eventual_bound (eps : ℝ) (heps : 0 < eps) :
    ∃ d₀ : ℕ, ∀ (d b : ℕ) [NeZero d], d₀ ≤ d → 0 < b →
      ∀ (p : ZMod d → Bool) (r : Bool → ZMod d)
        (C : Submodule CapacityIntervals.Bit (BinaryState d b)),
      (∀ a, p (r a) = a) → IsSharedCode CapacityIntervals.Bit p C →
      (Module.finrank CapacityIntervals.Bit C : ℝ) ≤
        (3/5+eps)*(b : ℝ)*(d : ℝ)^2+13/5*(defect (residual C p r) : ℝ) := by
  have hev : ∀ᶠ d : ℕ in atTop, rateError d < eps :=
    rateError_tendsto.eventually_lt_const heps
  obtain ⟨d₀, hd₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max d₀ 4, ?_⟩
  intro d b _ hd hb p r C hr hC
  have hfour : 4 ≤ d := le_trans (le_max_right _ _) hd
  have he : rateError d ≤ eps := (hd₀ d (le_trans (le_max_left _ _) hd)).le
  have hh := capacity_rate_bound hC hr hfour hb
  have hdb : 0 < (b : ℝ)*(d : ℝ)^2 := by
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  have hbnd : (Module.finrank CapacityIntervals.Bit C : ℝ)/((b : ℝ)*(d : ℝ)^2) ≤
      3/5+eps+13/5*(defect (residual C p r) : ℝ)/((b : ℝ)*(d : ℝ)^2) := by linarith
  have hout := (div_le_iff₀ hdb).mp hbnd
  have heq : (3/5+eps+13/5*(defect (residual C p r) : ℝ)/((b : ℝ)*(d : ℝ)^2))*
      ((b : ℝ)*(d : ℝ)^2) =
        (3/5+eps)*(b : ℝ)*(d : ℝ)^2+13/5*(defect (residual C p r) : ℝ) := by
    field_simp
  rwa [heq] at hout

end SharedDecoders.CapacityClosure
