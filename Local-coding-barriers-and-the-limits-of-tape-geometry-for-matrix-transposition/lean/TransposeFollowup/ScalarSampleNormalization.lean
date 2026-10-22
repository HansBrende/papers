import TransposeFollowup.CubicSampleNormalization

/-! Numerical normalization for the actual source sample. These lemmas
keep the extraction constant and remove unknown covering counts from a
trimming budget. They do not choose the sampling radii or assert that
incompatible simultaneous budgets can be satisfied. -/
namespace TransposeFollowup.SL2Projection
set_option autoImplicit false

/-- Normalize the quantitative extraction cube, including its fixed
constant, using the existing spanning-cube normalization theorem. -/
theorem coefficient_cube_normalization {a C N T V P H : ℝ}
    (ha : 0 < a) (hC : 0 < C) (hN : 0 < N)
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hcube : a*N^4 ≤ C*(9*T*H*V)^3) (hmixed : T ≤ P*N) :
    N ≤ (C*(9*P*H)^3/a)*V^3 := by
  have hscaled : (a/C)^(1 : ℝ)*N^4 ≤ (9*T*H*V)^3 := by
    rw [Real.rpow_one, div_mul_eq_mul_div]
    apply (div_le_iff₀ hC).mpr
    simpa only [mul_comm] using hcube
  have hh := spanning_cube_sample_normalization (η := a/C) (θ := 1) (S := 1) (m := V)
    (div_pos ha hC) hN hT hV hP hH hscaled hmixed (by simp)
  have he : (9*P*H)^3*(a/C)^(-(1 : ℝ))*(1 : ℝ)^3 = C*(9*P*H)^3/a := by
    rw [Real.rpow_neg_one, inv_div, one_pow, mul_one]
    ring
  rw [he] at hh
  exact hh

/-- Replace the sample-dependent trimming budget by a numerical ratio.
The ambient distribution supplies `N₀`; the extraction supplies `W`. -/
theorem trim_budget_of_global_normalization {N₀ N V W L C U A : ℝ}
    (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hV : 0 ≤ V)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hglobal : N ≤ W*V^3) (hU : U ≤ A*N)
    (hbudget : 32*L^3*C^3*W*(A+1/N₀) ≤ 1) :
    32*L^3*(U+1)*C^3 ≤ V^3 := by
  have hone : 1 ≤ (1/N₀)*N := by
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ hN₀).mpr (by simpa using hN)
  have hU' : U+1 ≤ (A+1/N₀)*N := by nlinarith only [hU, hone]
  have hscale : 0 ≤ A+1/N₀ := by positivity
  have hh := hU'.trans (mul_le_mul_of_nonneg_left hglobal hscale)
  have hfac : 0 ≤ 32*L^3*C^3 := by positivity
  calc
    _ = (32*L^3*C^3)*(U+1) := by ring
    _ ≤ (32*L^3*C^3)*((A+1/N₀)*(W*V^3)) := mul_le_mul_of_nonneg_left hh hfac
    _ = (32*L^3*C^3*W*(A+1/N₀))*V^3 := by ring
    _ ≤ 1*V^3 := mul_le_mul_of_nonneg_right hbudget (pow_nonneg hV _)
    _ = _ := one_mul _

/-- A certificate that this order of estimates cannot close. If final
coarsening already costs `s⁻⁴`, its cubic retention loss dominates the
available `s^κ` decay for `κ ≤ 12`. This is an obstruction to the displayed
budget, not an impossibility theorem for matrix growth. -/
theorem coarsening_trim_budget_obstruction {s κ C A W L : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hκ : κ ≤ 12)
    (hC : 1 ≤ C*s^4) (hA : s^κ ≤ A) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    1 < 32*L^3*C^3*W*A := by
  have hCpos : 0 < C := pos_of_mul_pos_left (zero_lt_one.trans_le hC) (by positivity)
  have hcs : 1 ≤ C^3*s^12 := by
    have hh := one_le_pow₀ hC (n := 3)
    convert hh using 1; ring
  have hsκ : s^12 ≤ s^κ := by
    have hh := Real.rpow_le_rpow_of_exponent_ge hs hs1 hκ
    simpa only [show (12 : ℝ) = (12 : ℕ) by norm_num, Real.rpow_natCast] using hh
  have hCA : 1 ≤ C^3*A :=
    hcs.trans (mul_le_mul_of_nonneg_left (hsκ.trans hA) (pow_nonneg hCpos.le _))
  have hLW : 1 ≤ L^3*W := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL) hW
  have hall : 1 ≤ (L^3*W)*(C^3*A) := one_le_mul_of_one_le_of_one_le hLW hCA
  have hh := mul_le_mul_of_nonneg_left hall (by norm_num : (0 : ℝ) ≤ 32)
  nlinarith only [hh]

end TransposeFollowup.SL2Projection
