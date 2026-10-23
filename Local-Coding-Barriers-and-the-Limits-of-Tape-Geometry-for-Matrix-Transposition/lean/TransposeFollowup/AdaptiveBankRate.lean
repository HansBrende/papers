import TransposeFollowup.AdaptiveBankNumerics
import TransposeFollowup.GapBankGroups
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Bounds

/-! Explicit choices of radius and bucket count for the logarithmic-logarithmic
loss bound. All floors and positivity obligations are included. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

theorem bucketPatternCount_le_pow (M K : ℕ) : bucketPatternCount M K ≤ (M + 1)^K := by
  have hgeom (k : ℕ) : (∑ j ∈ Finset.range k, M^(j+1)) ≤ (M+1)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hp := Nat.pow_le_pow_left (Nat.le_succ M) k
      calc
        _ ≤ (M+1)^k + M^(k+1) := Nat.add_le_add_right ih _
        _ ≤ (M+1)^k + (M+1)^k * M := by
          rw [pow_succ]
          exact Nat.add_le_add_left (Nat.mul_le_mul_right M hp) _
        _ = _ := by rw [pow_succ]; ring
  calc bucketPatternCount M K
      ≤ ∑ j ∈ Finset.range (min K M), M^(j+1) :=
        Finset.sum_le_sum (fun j _ => Nat.choose_le_pow M (j+1))
    _ ≤ ∑ j ∈ Finset.range K, M^(j+1) :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.min_le_left _ _))
    _ ≤ _ := hgeom K

noncomputable def adaptiveRateRadius (delta : ℕ) (t : ℝ) : ℕ :=
  ⌊Real.logb (delta : ℝ) t / 4⌋₊

/-- The exact radius from the written proof is legal and has the claimed
reciprocal bound and fourth-power growth budget. -/
theorem adaptiveRateRadius_bounds (delta : ℕ) (hdelta : 2 ≤ delta)
    (t : ℝ) (ht : (delta : ℝ)^8 ≤ t) :
    2 ≤ adaptiveRateRadius delta t ∧
    (1 / (adaptiveRateRadius delta t : ℝ)) ≤
      8 * Real.log (delta : ℝ) / Real.log t ∧
    ((delta ^ adaptiveRateRadius delta t : ℕ) : ℝ)^4 ≤ t := by
  have hd : (1 : ℝ) < delta := by exact_mod_cast (show 1 < delta by omega)
  have hd0 : (0 : ℝ) < delta := lt_trans zero_lt_one hd
  have ht0 : 0 < t := (pow_pos hd0 8).trans_le ht
  have hlog : 8 ≤ Real.logb (delta : ℝ) t := by
    apply (Real.le_logb_iff_rpow_le hd ht0).mpr
    simpa using ht
  let a := Real.logb (delta : ℝ) t / 4
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have hfloor : (adaptiveRateRadius delta t : ℝ) ≤ a := Nat.floor_le (by linarith)
  have hfloor2 : a < (adaptiveRateRadius delta t : ℝ) + 1 := Nat.lt_floor_add_one a
  have hR : 2 ≤ adaptiveRateRadius delta t := Nat.le_floor ha
  have hR0 : (0 : ℝ) < adaptiveRateRadius delta t := by exact_mod_cast (show 0 < adaptiveRateRadius delta t by omega)
  have hlogt : 0 < Real.log t := by
    have ht1 : 1 < t := (one_lt_pow₀ hd (by decide : (8 : ℕ) ≠ 0)).trans_le ht
    exact Real.log_pos ht1
  have hlogd : 0 < Real.log (delta : ℝ) := Real.log_pos hd
  have hhalf : Real.log t ≤ 8 * (adaptiveRateRadius delta t : ℝ) * Real.log (delta : ℝ) := by
    have haR : a ≤ 2 * (adaptiveRateRadius delta t : ℝ) := by linarith
    dsimp [a, Real.logb] at haR
    have hm := mul_le_mul_of_nonneg_right haR hlogd.le
    field_simp at hm
    nlinarith
  refine ⟨hR, (div_le_div_iff₀ hR0 hlogt).mpr (by nlinarith), ?_⟩
  have hexp : (4 * adaptiveRateRadius delta t : ℕ) ≤ Real.logb (delta : ℝ) t := by
    push_cast
    dsimp [a] at hfloor
    linarith
  have hp := (Real.rpow_le_rpow_of_exponent_le hd.le hexp).trans_eq
    (Real.rpow_logb hd0 (ne_of_gt hd) ht0)
  have hp' : (delta : ℝ)^(4 * adaptiveRateRadius delta t) ≤ t := by
    simpa only [Real.rpow_natCast] using hp
  simpa only [Nat.cast_pow, ← pow_mul, Nat.mul_comm] using hp'

noncomputable def adaptiveRateBuckets (d K : ℕ) : ℕ :=
  ⌊(d : ℝ) ^ (1 / (4 * (K : ℝ)))⌋₊

theorem adaptiveRateBuckets_bounds (d K : ℕ) (hd : 1 ≤ d) (hK : 0 < K)
    (hKt : 4 * (K : ℝ) ≤ Real.logb 2 (d : ℝ)) :
    1 ≤ adaptiveRateBuckets d K ∧ adaptiveRateBuckets d K ≤ d ∧
    1 / (adaptiveRateBuckets d K : ℝ) ≤ 2 * (d : ℝ)^(-(1 / (4 * (K : ℝ)))) ∧
    (bucketPatternCount (adaptiveRateBuckets d K) K : ℝ) ≤ (d : ℝ)^(1/2 : ℝ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hd1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  let x := (d : ℝ) ^ (1 / (4 * (K : ℝ)))
  let M := adaptiveRateBuckets d K
  have hx1 : 1 ≤ x := Real.one_le_rpow hd1 (by positivity)
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hxle : x ≤ d := Real.rpow_le_self_of_one_le hd1 (by
    apply (div_le_one (by positivity : 0 < 4 * (K : ℝ))).mpr
    linarith)
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa [x] using hx1)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMle : M ≤ d := Nat.floor_le_of_le hxle
  have hfloor : (M : ℝ) ≤ x := Nat.floor_le hx0.le
  have hfloor' : x < (M : ℝ) + 1 := Nat.lt_floor_add_one x
  have hhalf : x / 2 ≤ (M : ℝ) := by
    have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have hinv : 1 / (M : ℝ) ≤ 2 * (d : ℝ)^(-(1 / (4 * (K : ℝ)))) := by
    rw [Real.rpow_neg hd0.le]
    change 1 / (M : ℝ) ≤ 2 * x⁻¹
    apply (div_le_iff₀ hM0).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf (inv_nonneg.mpr hx0.le)
    have he : x / 2 * x⁻¹ = (1/2 : ℝ) := by field_simp
    rw [he] at hh
    nlinarith
  have hxpow : x^K = (d : ℝ)^(1/4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd0.le]
    congr 1
    field_simp
  have htwo : (2 : ℝ)^K ≤ (d : ℝ)^(1/4 : ℝ) := by
    have he : (K : ℝ) ≤ Real.logb 2 (d : ℝ) / 4 := by linarith
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
    have heq : (2 : ℝ) ^ (Real.logb 2 (d : ℝ) / 4) = (d : ℝ)^(1/4 : ℝ) := by
      rw [div_eq_mul_inv, Real.rpow_mul (by norm_num)]
      rw [Real.rpow_logb (by norm_num) (by norm_num) hd0]
      norm_num
    simpa only [Real.rpow_natCast, heq] using h
  have hQ : (bucketPatternCount M K : ℝ) ≤ (d : ℝ)^(1/2 : ℝ) := by
    have hb : (bucketPatternCount M K : ℝ) ≤ ((M : ℝ)+1)^K := by
      exact_mod_cast bucketPatternCount_le_pow M K
    have hm : (M : ℝ) + 1 ≤ 2 * x := by linarith
    calc
      _ ≤ ((M : ℝ)+1)^K := hb
      _ ≤ (2*x)^K := pow_le_pow_left₀ (by positivity) hm K
      _ = (2 : ℝ)^K * (d : ℝ)^(1/4 : ℝ) := by rw [mul_pow, hxpow]
      _ ≤ (d : ℝ)^(1/4 : ℝ) * (d : ℝ)^(1/4 : ℝ) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hd0.le _)
      _ = (d : ℝ)^(1/2 : ℝ) := by
        rw [← Real.rpow_add hd0]
        norm_num
  exact ⟨hM1, hMle, hinv, hQ⟩

noncomputable def adaptiveRateError (d delta sigma : ℕ) (As Ad : ℝ) : ℝ :=
  let K := delta ^ adaptiveRateRadius delta (Real.logb 2 (d : ℝ))
  (K : ℝ)^2 * (2 * (d : ℝ)^(-(1 / (4 * (K : ℝ)))) + (1 + 2 * (sigma : ℝ)) / d) +
    (((K : ℝ) + 1) * As + Ad) / (d : ℝ)^(1/2 : ℝ)

/-- The explicit finite rate with the original radius, bucket floor and factor8.
The parameterized budget is supplied by the proved protocol theorem. -/
theorem adaptive_forest_explicit_rate
    (d delta sigma : ℕ) (hd : 1 ≤ d) (hdelta : 2 ≤ delta)
    (ht : (delta : ℝ)^8 ≤ Real.logb 2 (d : ℝ))
    (W B s D As Ad : ℝ) (hW : 0 < W) (hAs : 0 ≤ As) (hAd : 0 ≤ Ad)
    (hs : s ≤ As * W) (hD : D ≤ Ad * W)
    (hbudget : ∀ R M : ℕ, 0 < R → 0 < M → M ≤ d →
      (1 + 1 / (R : ℝ)) * B ≥ (d : ℝ) * W -
        W * (delta : ℝ)^(2*R) * ((d ⌈/⌉ M : ℕ) + 2 * (sigma : ℝ)) -
        (bucketPatternCount M (delta^R) : ℝ) * (((delta : ℝ)^R + 1) * s + D)) :
    1 - B / ((d : ℝ) * W) ≤
      8 * Real.log (delta : ℝ) / Real.log (Real.logb 2 (d : ℝ)) +
        adaptiveRateError d delta sigma As Ad := by
  let t := Real.logb 2 (d : ℝ)
  let R := adaptiveRateRadius delta t
  let K := delta^R
  let M := adaptiveRateBuckets d K
  let Q := (bucketPatternCount M K : ℝ)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hP : (0 : ℝ) < d * W := mul_pos hd0 hW
  obtain ⟨hR2, hRinv, hK4⟩ := adaptiveRateRadius_bounds delta hdelta t ht
  change 2 ≤ R at hR2
  change (K : ℝ)^4 ≤ t at hK4
  have hKlarge : 4 ≤ K := by
    calc 4 = 2^2 := by norm_num
         _ ≤ delta^2 := Nat.pow_le_pow_left hdelta 2
         _ ≤ delta^R := Nat.pow_le_pow_right (by omega) hR2
  have hKpos : 0 < K := by omega
  have hKt : 4 * (K : ℝ) ≤ t := by
    have hh : 4 * K ≤ K^4 := by
      calc 4 * K ≤ K * K := Nat.mul_le_mul_right K hKlarge
           _ = K^2 := by ring
           _ ≤ K^4 := Nat.pow_le_pow_right (by omega) (by omega)
    exact (by exact_mod_cast hh : 4 * (K : ℝ) ≤ (K : ℝ)^4).trans hK4
  obtain ⟨hM1,hMd,hMinv,hQ⟩ := adaptiveRateBuckets_bounds d K hd hKpos hKt
  change 1 ≤ M at hM1
  change M ≤ d at hMd
  change 1 / (M : ℝ) ≤ _ at hMinv
  change Q ≤ _ at hQ
  have hR0 : 0 < R := by omega
  have hM0 : 0 < M := by omega
  have hnorm := adaptive_forest_normalized_budget d M R sigma (by omega) hM0
    W B ((delta : ℝ)^(2*R)) Q ((delta : ℝ)^R) s D hW (by positivity)
    (hbudget R M hR0 hM0 hMd)
  have hpow : (delta : ℝ)^(2*R) = (K : ℝ)^2 := by
    dsimp [K]
    push_cast
    rw [← pow_mul, Nat.mul_comm]
  have hpow' : (delta : ℝ)^R = (K : ℝ) := by simp [K]
  rw [hpow, hpow'] at hnorm
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  let A := ((K : ℝ)+1)*As+Ad
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hstate : ((K : ℝ)+1)*s + D ≤ A * W := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (K : ℝ)+1)]
  have hsqrt : 0 < (d : ℝ)^(1/2 : ℝ) := Real.rpow_pos_of_pos hd0 _
  have hsquare : (d : ℝ)^(1/2 : ℝ) * (d : ℝ)^(1/2 : ℝ) = d := by
    rw [← Real.rpow_add hd0]
    norm_num
  have hinfo : Q * (((K : ℝ)+1)*s+D) / ((d : ℝ)*W) ≤ A / (d : ℝ)^(1/2 : ℝ) := by
    calc
      _ ≤ Q * (A*W) / ((d : ℝ)*W) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hstate hQ0) hP.le
      _ = Q*A/(d : ℝ) := by field_simp
      _ ≤ (d : ℝ)^(1/2 : ℝ)*A/d :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hQ hA) hd0.le
      _ = _ := by
        apply (div_eq_div_iff hd0.ne' hsqrt.ne').mpr
        nlinarith [hsquare]
  have hnear := mul_le_mul_of_nonneg_left
    (add_le_add_right hMinv ((1+2*(sigma : ℝ))/d)) (sq_nonneg (K : ℝ))
  have he : 0 ≤ adaptiveRateError d delta sigma As Ad := by
    dsimp [adaptiveRateError]
    positivity
  have hh : 1 - adaptiveRateError d delta sigma As Ad ≤
      (1+1/(R : ℝ))*(B/((d : ℝ)*W)) := by
    change 1 - ((K : ℝ)^2 * (2*(d : ℝ)^(-(1/(4*(K : ℝ)))) +
      (1+2*(sigma : ℝ))/d) + A/(d : ℝ)^(1/2 : ℝ)) ≤ _
    linarith
  have hi : 0 < 1/(R : ℝ) := by positivity
  by_cases hb : 1 ≤ B/((d : ℝ)*W)
  · have hrnonneg : 0 ≤ 8*Real.log (delta : ℝ)/Real.log t :=
      hi.le.trans hRinv
    change _ ≤ 8*Real.log (delta : ℝ)/Real.log t + _
    linarith
  · have hm := mul_le_mul_of_nonneg_left (le_of_not_ge hb) hi.le
    change _ ≤ 8*Real.log (delta : ℝ)/Real.log t + _
    nlinarith

end TransposeFollowup
