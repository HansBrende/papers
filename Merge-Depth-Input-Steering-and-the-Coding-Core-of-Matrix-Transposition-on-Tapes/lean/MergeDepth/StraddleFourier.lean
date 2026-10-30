import MergeDepth.BlockPairsShift
import MergeDepth.StraddleProgression

/-!
# Partial results on Conjecture S: the exact form of `V_k` (Proposition 7.12)

The paper's normalized `sinc y = sin(πy)/(πy)` is Mathlib's `Real.sinc (π y)`.

* `integral_exp_tent`, `fourierCoeffOn_perTent`: the Fourier transform of the tent,
  `∫ e^{-iθy} Δ(y) dy = (w²/2) sinc²(θw/4)`, and the Fourier coefficients of a translated periodic
  tent on `[0, N]`.
* `fourierCoeffOn_profile`, `norm_sq_fourierCoeffOn_profile`: the Fourier coefficients of the
  profile `x_k` and `|x̂_k(r)|² = μ_k² φ(r)`, where `phiGen` is
  `sinc⁴(π r Π̂_κ/(2N)) ∏_{i<k} cos²(π r Π̂_i/N) ∏_{i<κ} cos²(π r Π̂_i/N)` (Parseval via
  Mathlib's `hasSum_sq_fourierCoeffOn`).
* `hasSum_phiGen`: `∑_{r ∈ ℤ} φ(r) = 1 + V_k` for every `κ ≥ 1`.
* `straddlePhi` `= φ_k` as printed; `phiGen_eq_straddlePhi` for `1 ≤ k ≤ κ`;
  `hasSum_straddlePhi`, `hasSum_straddlePhi_ne_zero`, `relVariance_eq_tsum`:
  **Proposition 7.12(a)**, `V_k = ∑_{r ≠ 0} φ_k(r)` (for `1 ≤ k ≤ κ`).
* `fineFloorK` `= F_k`, `fineFloorTerm`, `fineFloor` `= F(n, D)`; `fineFloorK_le_relVariance`
  and `fineFloorK_eq`: **Proposition 7.12(c)**, `V_k ≥ F_k = F(n_κ, κ - k)`;
  `summable_fineFloorTerm`.
* Proposition 7.12(b), the density of `W`, is `density_W` in `MergeDepth/StraddleDensity.lean`,
  which also restates (a) and (c) (`exact_form_V`).
-/

namespace MergeDepth

open Finset Real MeasureTheory

/-! ### The Fourier transform of the tent -/

/-- `(w²/4) sinc²(θw/4) = 4 sin²(θw/4)/θ²` for `θ ≠ 0` (`sinc` is Mathlib's unnormalized `sinc`). -/
theorem sq_mul_sinc_sq_eq {w θ : ℝ} (hθ : θ ≠ 0) :
    w ^ 2 / 4 * sinc (θ * w / 4) ^ 2 = 4 * sin (θ * w / 4) ^ 2 / θ ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [sinc_of_ne_zero (by positivity)]
    field_simp

/-- `∫_0^{w/2} (w - 2y) cos(θy) dy = (w²/4) sinc²(θw/4)`. -/
theorem integral_tent_cos_half (w θ : ℝ) :
    ∫ y in (0 : ℝ)..(w / 2), (w - 2 * y) * cos (θ * y) = w ^ 2 / 4 * sinc (θ * w / 4) ^ 2 := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp only [zero_mul, cos_zero, mul_one, zero_div, sinc_zero, one_pow]
    have hF : ∀ y ∈ Set.uIcc (0 : ℝ) (w / 2), HasDerivAt (fun y => w * y - y ^ 2) (w - 2 * y) y := by
      intro y _
      have := ((hasDerivAt_id y).const_mul w).sub (hasDerivAt_pow 2 y)
      convert this using 1
      · ext z; simp
      · simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (by apply Continuous.intervalIntegrable; fun_prop)]
    ring
  · rw [sq_mul_sinc_sq_eq hθ]
    have hF : ∀ y ∈ Set.uIcc (0 : ℝ) (w / 2), HasDerivAt
        (fun y => (w - 2 * y) * sin (θ * y) / θ - 2 * cos (θ * y) / θ ^ 2)
        ((w - 2 * y) * cos (θ * y)) y := by
      intro y _
      have h1 : HasDerivAt (fun y => θ * y) θ y := by
        simpa using (hasDerivAt_id y).const_mul θ
      have hs := (Real.hasDerivAt_sin (θ * y)).comp y h1
      have hc := (Real.hasDerivAt_cos (θ * y)).comp y h1
      have hl : HasDerivAt (fun y => w - 2 * y) (-2) y := by
        simpa using ((hasDerivAt_id y).const_mul 2).const_sub w
      have := ((hl.mul hs).div_const θ).sub ((hc.const_mul 2).div_const (θ ^ 2))
      convert this using 1
      · ext z; simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
      · simp only [Function.comp_apply]; field_simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have h2 : cos (θ * (w / 2)) = 1 - 2 * sin (θ * w / 4) ^ 2 := by
      rw [show θ * (w / 2) = 2 * (θ * w / 4) by ring, cos_two_mul, sin_sq]
      ring
    simp only [mul_zero, sin_zero, cos_zero, sub_zero, zero_div, zero_sub]
    rw [show w - 2 * (w / 2) = 0 by ring, h2]
    field_simp
    ring

/-- `∫_{-N/2}^{N/2} Δ(y) cos(θy) dy = (w²/2) sinc²(θw/4)` for `0 ≤ w ≤ N`. -/
theorem integral_tent_cos {N w : ℝ} (hw : 0 ≤ w) (hwN : w ≤ N) (θ : ℝ) :
    ∫ y in (-(N / 2))..(N / 2), tent w y * cos (θ * y) = w ^ 2 / 2 * sinc (θ * w / 4) ^ 2 := by
  have hc : Continuous fun y => tent w y * cos (θ * y) := by
    have := continuous_tent w; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hneg : ∫ y in (-(N / 2))..0, tent w y * cos (θ * y) =
      ∫ y in (0 : ℝ)..(N / 2), tent w y * cos (θ * y) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := N / 2)
      (fun y => tent w y * cos (θ * y))
    rw [neg_zero] at this
    rw [← this]; congr 1; ext x; simp [tent, abs_neg, mul_neg, cos_neg]
  have hhalf : ∫ y in (0 : ℝ)..(N / 2), tent w y * cos (θ * y) = w ^ 2 / 4 * sinc (θ * w / 4) ^ 2 := by
    have h1 : IntervalIntegrable (fun y => tent w y * cos (θ * y)) volume 0 (w / 2) :=
      hc.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun y => tent w y * cos (θ * y)) volume (w / 2) (N / 2) :=
      hc.intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have e1 : ∫ y in (0 : ℝ)..(w / 2), tent w y * cos (θ * y) =
        ∫ y in (0 : ℝ)..(w / 2), (w - 2 * y) * cos (θ * y) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [Set.uIcc_of_le (by linarith)] at hy
      unfold tent; rw [abs_of_nonneg hy.1, max_eq_right (by linarith [hy.2])]
    have e2 : ∫ y in (w / 2)..(N / 2), tent w y * cos (θ * y) = ∫ y in (w / 2)..(N / 2), (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [Set.uIcc_of_le (by linarith)] at hy
      unfold tent; rw [abs_of_nonneg (by linarith [hy.1]), max_eq_left (by linarith [hy.1]), zero_mul]
    rw [e1, e2, intervalIntegral.integral_zero, add_zero, integral_tent_cos_half]
  rw [hneg, hhalf]; ring

/-- `∫_{-N/2}^{N/2} Δ(y) sin(θy) dy = 0` (odd integrand). -/
theorem integral_tent_sin (N w θ : ℝ) :
    ∫ y in (-(N / 2))..(N / 2), tent w y * sin (θ * y) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -(N / 2)) (b := N / 2)
    (fun y => tent w y * sin (θ * y))
  rw [neg_neg] at h
  have hodd : (fun y => tent w (-y) * sin (θ * -y)) = fun y => -(tent w y * sin (θ * y)) := by
    ext y; simp [tent, abs_neg, mul_neg, sin_neg]
  rw [hodd, intervalIntegral.integral_neg] at h
  linarith

open Complex in
/-- The Fourier transform of the tent: `∫_{-N/2}^{N/2} e^{-iθy} Δ(y) dy = (w²/2) sinc²(θw/4)`. -/
theorem integral_exp_tent {N w : ℝ} (hw : 0 ≤ w) (hwN : w ≤ N) (θ : ℝ) :
    ∫ y in (-(N / 2))..(N / 2), Complex.exp (-((θ * y : ℝ) : ℂ) * I) * (tent w y : ℂ) =
      ((w ^ 2 / 2 * Real.sinc (θ * w / 4) ^ 2 : ℝ) : ℂ) := by
  have hpt : ∀ y : ℝ, Complex.exp (-((θ * y : ℝ) : ℂ) * I) * (tent w y : ℂ) =
      ((tent w y * Real.cos (θ * y) : ℝ) : ℂ) - I * ((tent w y * Real.sin (θ * y) : ℝ) : ℂ) := by
    intro y
    rw [← Complex.ofReal_neg, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  simp_rw [hpt]
  have hc1 : Continuous fun y => tent w y * Real.cos (θ * y) := by
    have := continuous_tent w; fun_prop
  have hc2 : Continuous fun y => tent w y * Real.sin (θ * y) := by
    have := continuous_tent w; fun_prop
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_tent_cos hw hwN, integral_tent_sin]
  · simp
  · exact (Complex.continuous_ofReal.comp hc1).intervalIntegrable _ _
  · exact (continuous_const.mul (Complex.continuous_ofReal.comp hc2)).intervalIntegrable _ _

/-! ### Fourier coefficients of the profile -/

open Complex in
/-- The Fourier coefficients on `[0, N]` of a translated periodic tent:
`N^{-1} ∫_0^N e^{-2πint/N} Δ_N(t + u) dt = e^{2πinu/N} (w²/2) sinc²(πnw/(2N)) / N`. -/
theorem fourierCoeffOn_perTent {N w : ℝ} (hN : 0 < N) (hw : 0 ≤ w) (hwN : w ≤ N) (u : ℝ) (n : ℤ) :
    fourierCoeffOn hN (fun t => (perTent N w (t + u) : ℂ)) n =
      Complex.exp (2 * π * I * n * u / N) *
        ((w ^ 2 / 2 * Real.sinc (π * n * w / (2 * N)) ^ 2 / N : ℝ) : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  set h : ℝ → ℂ := fun y => Complex.exp (2 * π * I * ((-n : ℤ) : ℂ) * y / N) * (perTent N w y : ℂ)
    with hh
  have hper : Function.Periodic h N := by
    intro y
    simp only [hh]
    rw [perTent_periodic y]
    congr 1
    rw [show 2 * π * I * ((-n : ℤ) : ℂ) * ((y + N : ℝ) : ℂ) / N =
        2 * π * I * ((-n : ℤ) : ℂ) * y / N + ((-n : ℤ) : ℂ) * (2 * π * I) by
      push_cast; field_simp; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have e1 : ∫ x in (0 : ℝ)..N, fourier (-n) (x : AddCircle (N - 0)) • (perTent N w (x + u) : ℂ) =
      Complex.exp (2 * π * I * n * u / N) * ∫ x in (0 : ℝ)..N, h (x + u) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hh, fourier_coe_apply, smul_eq_mul, sub_zero]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  have e2 : ∫ x in (0 : ℝ)..N, h (x + u) =
      ∫ y in (-(N / 2))..(N / 2), Complex.exp (-((2 * π * n / N * y : ℝ) : ℂ) * I) * (tent w y : ℂ) := by
    rw [intervalIntegral.integral_comp_add_right h u, zero_add, show N + u = u + N by ring,
      hper.intervalIntegral_add_eq u (-(N / 2)), show -(N / 2) + N = N / 2 by ring]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le (by linarith)] at hy
    simp only [hh]
    rw [perTent_eq_tent hN hwN (abs_le.mpr ⟨hy.1, hy.2⟩)]
    congr 2
    push_cast
    field_simp
  rw [fourierCoeffOn_eq_integral, e1, e2, integral_exp_tent hw hwN, Complex.real_smul,
    show 2 * π * n / N * w / 4 = π * n * w / (2 * N) by field_simp; ring]
  push_cast
  field_simp
  ring

/-- Fourier coefficients on `[a, b]` of finite sums of continuous functions. -/
theorem fourierCoeffOn_finsetSum {ι : Type*} (s : Finset ι) {a b : ℝ} (hab : a < b)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) (n : ℤ) :
    fourierCoeffOn hab (fun t => ∑ i ∈ s, f i t) n = ∑ i ∈ s, fourierCoeffOn hab (f i) n := by
  simp_rw [fourierCoeffOn_eq_integral, Finset.smul_sum]
  rw [← Finset.smul_sum, ← intervalIntegral.integral_finsetSum]
  intro i hi
  have hc : Continuous fun x : ℝ => fourier (-n) (x : AddCircle (b - a)) :=
    (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  exact (hc.smul (hf i hi)).intervalIntegrable _ _

open Complex in
/-- `∑_{S ⊆ s} e^{i(α + ∑_{i ∈ S} β_i)} = e^{iα} ∏_{i ∈ s} (1 + e^{iβ_i})`. -/
theorem sum_powerset_exp_mul_I (s : Finset ℕ) (α : ℝ) (β : ℕ → ℝ) :
    ∑ S ∈ s.powerset, Complex.exp (((α + ∑ i ∈ S, β i : ℝ) : ℂ) * I) =
      Complex.exp ((α : ℂ) * I) * ∏ i ∈ s, (1 + Complex.exp ((β i : ℂ) * I)) := by
  rw [Finset.prod_one_add, Finset.mul_sum]
  refine sum_congr rfl fun S _ => ?_
  push_cast
  rw [add_mul, Complex.exp_add, Finset.sum_mul, Complex.exp_sum]

open Complex in
/-- `|1 + e^{iβ}|² = 4 cos²(β/2)`. -/
theorem norm_sq_one_add_exp_mul_I (β : ℝ) :
    ‖1 + Complex.exp ((β : ℂ) * I)‖ ^ 2 = 4 * Real.cos (β / 2) ^ 2 := by
  have h : 1 + Complex.exp ((β : ℂ) * I) =
      Complex.exp (((β / 2 : ℝ) : ℂ) * I) * ((2 * Real.cos (β / 2) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.two_cos, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    rw [show ((β : ℂ) / 2 * I + (β : ℂ) / 2 * I) = (β : ℂ) * I by ring,
      show ((β : ℂ) / 2 * I + -((β : ℂ) / 2) * I) = 0 by ring, Complex.exp_zero]
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  ring

open Complex in
/-- `‖∑_{S ⊆ s} e^{i(α + ∑_{i ∈ S} β_i)}‖² = ∏_{i ∈ s} 4 cos²(β_i/2)`. -/
theorem norm_sq_sum_powerset_exp (s : Finset ℕ) (α : ℝ) (β : ℕ → ℝ) :
    ‖∑ S ∈ s.powerset, Complex.exp (((α + ∑ i ∈ S, β i : ℝ) : ℂ) * I)‖ ^ 2 =
      ∏ i ∈ s, (4 * Real.cos (β i / 2) ^ 2) := by
  rw [sum_powerset_exp_mul_I, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_prod,
    ← Finset.prod_pow]
  exact prod_congr rfl fun i _ => norm_sq_one_add_exp_mul_I (β i)

theorem profilePeriod_pos (m : ℕ) : (0 : ℝ) < (m : ℝ) + 1 := by positivity

open Complex in
/-- The Fourier coefficients of the straddle profile on `[0, N]`. -/
theorem fourierCoeffOn_profile (m k κ : ℕ) (n : ℤ) :
    fourierCoeffOn (profilePeriod_pos m) (fun t => (profile m k κ t : ℂ)) n =
      (((2 ^ (k - 1) * piHat m κ)⁻¹ * (piHat m κ ^ 2 / 2 *
        Real.sinc (π * n * piHat m κ / (2 * ((m : ℝ) + 1))) ^ 2 / ((m : ℝ) + 1)) : ℝ) : ℂ) *
      ∑ S ∈ (Icc 1 (k - 1)).powerset, ∑ S' ∈ (Icc 1 (κ - 1)).powerset,
        Complex.exp (2 * π * I * n * ((apexHat m k S - valleyHat m κ S' : ℝ) : ℂ) /
          (((m : ℝ) + 1 : ℝ) : ℂ)) := by
  have hN := profilePeriod_pos m
  have hw0 : 0 ≤ piHat m κ := piHat_pos.le
  have hwN : piHat m κ ≤ (m : ℝ) + 1 := piHat_le m κ
  have hcont : ∀ u : ℝ, Continuous fun t : ℝ => (perTent ((m : ℝ) + 1) (piHat m κ) (t + u) : ℂ) :=
    fun u => Complex.continuous_ofReal.comp
      ((continuous_perTent hN hwN).comp (continuous_id.add continuous_const))
  have hfun : (fun t => (profile m k κ t : ℂ)) = fun t =>
      (((2 ^ (k - 1) * piHat m κ)⁻¹ : ℝ) : ℂ) *
      ∑ S ∈ (Icc 1 (k - 1)).powerset, ∑ S' ∈ (Icc 1 (κ - 1)).powerset,
        (perTent ((m : ℝ) + 1) (piHat m κ) (t + (apexHat m k S - valleyHat m κ S')) : ℂ) := by
    ext t
    simp only [profile, Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    refine sum_congr rfl fun S _ => sum_congr rfl fun S' _ => ?_
    congr 2; ring
  rw [hfun, fourierCoeffOn.const_mul, fourierCoeffOn_finsetSum _ _ _
    (fun S _ => continuous_finsetSum _ fun S' _ => hcont _)]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeffOn_finsetSum _ _ _ (fun S' _ => hcont _), Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun S' _ => ?_
  rw [fourierCoeffOn_perTent hN hw0 hwN]
  push_cast
  ring

/-- `φ` in general form: `sinc⁴(π r Π̂_κ/(2N)) ∏_{i=1}^{k-1} cos²(π r Π̂_i/N) ∏_{i=1}^{κ-1} cos²(π r Π̂_i/N)`
(Mathlib's unnormalized `sinc`). -/
noncomputable def phiGen (m k κ : ℕ) (r : ℤ) : ℝ :=
  Real.sinc (π * r * piHat m κ / (2 * ((m : ℝ) + 1))) ^ 4 *
    (∏ i ∈ Icc 1 (k - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2) *
    ∏ i ∈ Icc 1 (κ - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2

open Complex in
/-- `|x̂_k(r)|² = μ_k² φ(r)`. -/
theorem norm_sq_fourierCoeffOn_profile {m k κ : ℕ} (hκ : 1 ≤ κ) (n : ℤ) :
    ‖fourierCoeffOn (profilePeriod_pos m) (fun t => (profile m k κ t : ℂ)) n‖ ^ 2 =
      profileMean m k κ ^ 2 * phiGen m k κ n := by
  have hN := profilePeriod_pos m
  set N : ℝ := (m : ℝ) + 1 with hNdef
  set θ : ℝ := 2 * π * n / N with hθ
  -- the double sum is a product of two powerset sums
  have hsplit : ∑ S ∈ (Icc 1 (k - 1)).powerset, ∑ S' ∈ (Icc 1 (κ - 1)).powerset,
        Complex.exp (2 * π * I * n * ((apexHat m k S - valleyHat m κ S' : ℝ) : ℂ) / ((N : ℝ) : ℂ)) =
      (∑ S ∈ (Icc 1 (k - 1)).powerset, Complex.exp
          (((θ * ∑ i ∈ range k, (2 : ℝ)⁻¹ ^ i + ∑ i ∈ S, θ * piHat m i : ℝ) : ℂ) * I)) *
      (∑ S' ∈ (Icc 1 (κ - 1)).powerset, Complex.exp
          (((-(θ * (∑ i ∈ range κ, (2 : ℝ)⁻¹ ^ i + piHat m κ)) + ∑ i ∈ S', -(θ * piHat m i) : ℝ) : ℂ)
            * I)) := by
    rw [Finset.sum_mul_sum]
    refine sum_congr rfl fun S _ => sum_congr rfl fun S' _ => ?_
    rw [← Complex.exp_add]
    congr 1
    simp only [apexHat, valleyHat, hθ]
    push_cast
    simp only [Finset.sum_neg_distrib, ← Finset.mul_sum]
    field_simp
    ring
  rw [fourierCoeffOn_profile, hsplit, norm_mul, norm_mul, mul_pow, mul_pow,
    norm_sq_sum_powerset_exp, norm_sq_sum_powerset_exp, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, profileMean_eq hκ]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
  have hcos : ∀ i, Real.cos (-(θ * piHat m i) / 2) = Real.cos (π * n * piHat m i / N) := by
    intro i
    have : -(θ * piHat m i) / 2 = -(π * n * piHat m i / N) := by rw [hθ]; ring
    rw [this, Real.cos_neg]
  have hcos' : ∀ i, Real.cos (θ * piHat m i / 2) = Real.cos (π * n * piHat m i / N) := by
    intro i
    have : θ * piHat m i / 2 = π * n * piHat m i / N := by rw [hθ]; ring
    rw [this]
  simp only [hcos, hcos']
  unfold phiGen
  rw [← hNdef]
  have hw : piHat m κ = ((m - κ + 1 : ℕ) : ℝ) / 2 ^ κ := rfl
  rw [show (2 : ℝ) ^ (k - 1) * piHat m κ = 2 ^ (k - 1) * piHat m κ from rfl]
  have h4 : (4 : ℝ) ^ (κ - 1 + 1 - 1) = 4 ^ (κ - 1) := by rw [Nat.add_sub_cancel]
  have h4' : (4 : ℝ) ^ (k - 1 + 1 - 1) = 4 ^ (k - 1) := by rw [Nat.add_sub_cancel]
  rw [h4, h4']
  have hκpow : (2 : ℝ) ^ κ = 2 * 2 ^ (κ - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h44 : ∀ j : ℕ, (4 : ℝ) ^ j = (2 ^ j) ^ 2 := fun j => by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h44, h44, hw, hκpow]
  have hn : (0 : ℝ) < ((m - κ + 1 : ℕ) : ℝ) := by positivity
  field_simp
  ring

/-! ### Parseval: Proposition 7.12(a) -/

/-- `N⁻¹ ∫_0^N x_k² = Var x_k + μ_k²`. -/
theorem integral_profile_sq (m k κ : ℕ) :
    ((m : ℝ) + 1)⁻¹ * ∫ t in (0 : ℝ)..((m : ℝ) + 1), profile m k κ t ^ 2 =
      profileVariance m k κ + profileMean m k κ ^ 2 := by
  have hN := profilePeriod_pos m
  unfold profileVariance
  set μ := profileMean m k κ with hμ
  have hc := continuous_profile m k κ
  have hint : ∫ t in (0 : ℝ)..((m : ℝ) + 1), profile m k κ t = ((m : ℝ) + 1) * μ := by
    rw [hμ, profileMean]; field_simp
  have e : (fun t => (profile m k κ t - μ) ^ 2) =
      fun t => (profile m k κ t ^ 2 - (2 * μ) * profile m k κ t) + μ ^ 2 := by ext; ring
  have hsq : Continuous fun t => profile m k κ t ^ 2 := hc.pow 2
  rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, hint]
  · simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  · exact hsq.intervalIntegrable _ _
  · exact (continuous_const.mul hc).intervalIntegrable _ _
  · exact (hsq.sub (continuous_const.mul hc)).intervalIntegrable _ _
  · exact continuous_const.intervalIntegrable _ _

theorem profileMean_pos {m k κ : ℕ} (hκ : 1 ≤ κ) : 0 < profileMean m k κ := by
  rw [profileMean_eq hκ]; positivity

/-- **Proposition 7.12(a), general form**: for every `κ ≥ 1`, `∑_{r ∈ ℤ} φ(r) = 1 + V_k`, where
`φ = phiGen` is the normalized squared modulus of the Fourier coefficients of `x_k`. -/
theorem hasSum_phiGen {m k κ : ℕ} (hκ : 1 ≤ κ) :
    HasSum (fun r : ℤ => phiGen m k κ r) (1 + relVariance m k κ) := by
  have hN := profilePeriod_pos m
  have hc := continuous_profile m k κ
  have hcc : Continuous fun t => (profile m k κ t : ℂ) := Complex.continuous_ofReal.comp hc
  have hL2 : MemLp (fun t => (profile m k κ t : ℂ)) 2
      (volume.restrict (Set.Ioc 0 ((m : ℝ) + 1))) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (m : ℝ) + 1)).exists_bound_of_continuousOn
      hcc.continuousOn
    refine MemLp.of_bound hcc.aestronglyMeasurable C ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => hC t (Set.Ioc_subset_Icc_self ht))
  have h := hasSum_sq_fourierCoeffOn (profilePeriod_pos m) hL2
  simp_rw [norm_sq_fourierCoeffOn_profile hκ] at h
  have hrhs : (((m : ℝ) + 1) - 0)⁻¹ • ∫ x in (0 : ℝ)..((m : ℝ) + 1), ‖(profile m k κ x : ℂ)‖ ^ 2 =
      profileVariance m k κ + profileMean m k κ ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero, smul_eq_mul]
    exact integral_profile_sq m k κ
  rw [hrhs] at h
  have hμ := profileMean_pos (m := m) (k := k) hκ
  have := h.mul_left (profileMean m k κ ^ 2)⁻¹
  convert this using 1
  · ext r; field_simp
  · unfold relVariance; field_simp; ring

theorem phiGen_zero (m k κ : ℕ) : phiGen m k κ 0 = 1 := by
  simp [phiGen]

theorem phiGen_nonneg (m k κ : ℕ) (r : ℤ) : 0 ≤ phiGen m k κ r := by
  unfold phiGen
  have h4 : 0 ≤ Real.sinc (π * r * piHat m κ / (2 * ((m : ℝ) + 1))) ^ 4 := by positivity
  exact mul_nonneg (mul_nonneg h4 (prod_nonneg fun _ _ => sq_nonneg _))
    (prod_nonneg fun _ _ => sq_nonneg _)

/-! ### The function `φ_k` -/

/-- **`φ_k(r)`** as in Section 7.5, with the normalized `sinc y = sin(πy)/(πy)` written as
Mathlib's `Real.sinc (π y)`:
`φ_k(r) = sinc⁴(r n_κ/(N 2^{κ+1})) ∏_{i=1}^{k-1} cos⁴(π r n_i/(N 2^i)) ∏_{i=k}^{κ-1} cos²(π r n_i/(N 2^i))`. -/
noncomputable def straddlePhi (m k κ : ℕ) (r : ℤ) : ℝ :=
  Real.sinc (π * (r * (m - κ + 1 : ℕ) / (((m : ℝ) + 1) * 2 ^ (κ + 1)))) ^ 4 *
    (∏ i ∈ Icc 1 (k - 1), Real.cos (π * r * (m - i + 1 : ℕ) / (((m : ℝ) + 1) * 2 ^ i)) ^ 4) *
    ∏ i ∈ Ico k κ, Real.cos (π * r * (m - i + 1 : ℕ) / (((m : ℝ) + 1) * 2 ^ i)) ^ 2

theorem phiGen_eq_straddlePhi {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) (r : ℤ) :
    phiGen m k κ r = straddlePhi m k κ r := by
  have hN := profilePeriod_pos m
  unfold phiGen straddlePhi
  have hcos : ∀ i, Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) =
      Real.cos (π * r * (m - i + 1 : ℕ) / (((m : ℝ) + 1) * 2 ^ i)) := by
    intro i; congr 1; unfold piHat; field_simp
  have hsinc : π * r * piHat m κ / (2 * ((m : ℝ) + 1)) =
      π * (r * (m - κ + 1 : ℕ) / (((m : ℝ) + 1) * 2 ^ (κ + 1))) := by
    unfold piHat; rw [pow_succ]; field_simp
  simp only [hcos, hsinc]
  have hI1 : Icc 1 (κ - 1) = Ico 1 κ := by ext x; simp only [mem_Icc, mem_Ico]; omega
  have hI2 : Icc 1 (k - 1) = Ico 1 k := by ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [hI1, ← prod_Ico_consecutive _ hk hkκ, hI2]
  rw [mul_assoc, mul_assoc, ← mul_assoc (∏ i ∈ Ico 1 k, _), ← prod_mul_distrib]
  congr 2
  refine prod_congr rfl fun i _ => ?_
  ring

/-- **Proposition 7.12(a)**: for `1 ≤ k ≤ κ`, `1 + V_k = ∑_{r ∈ ℤ} φ_k(r)`. -/
theorem hasSum_straddlePhi {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) :
    HasSum (fun r : ℤ => straddlePhi m k κ r) (1 + relVariance m k κ) := by
  have := hasSum_phiGen (m := m) (k := k) (κ := κ) (by omega)
  simp only [phiGen_eq_straddlePhi hk hkκ] at this
  exact this

theorem straddlePhi_zero {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) : straddlePhi m k κ 0 = 1 := by
  rw [← phiGen_eq_straddlePhi hk hkκ, phiGen_zero]

theorem straddlePhi_nonneg {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) (r : ℤ) :
    0 ≤ straddlePhi m k κ r := by
  rw [← phiGen_eq_straddlePhi hk hkκ]; exact phiGen_nonneg m k κ r

/-- **Proposition 7.12(a)**: `V_k = ∑_{r ≠ 0} φ_k(r)`. -/
theorem hasSum_straddlePhi_ne_zero {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) :
    HasSum (fun r : ℤ => if r = 0 then 0 else straddlePhi m k κ r) (relVariance m k κ) := by
  have h := (hasSum_straddlePhi (m := m) hk hkκ).update 0 0
  rw [straddlePhi_zero hk hkκ] at h
  convert h using 1
  · ext r
    by_cases hr : r = 0
    · subst hr; simp
    · simp [hr]
  · ring

theorem relVariance_eq_tsum {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) :
    relVariance m k κ = ∑' r : ℤ, if r = 0 then 0 else straddlePhi m k κ r :=
  (hasSum_straddlePhi_ne_zero hk hkκ).tsum_eq.symm

/-! ### Proposition 7.12(c): the fine floor -/

/-- `F_k = ∑_{t ≠ 0} φ_k(N 2^{k-1} t)`, the contribution of the multiples of `N 2^{k-1}`. -/
noncomputable def fineFloorK (m k κ : ℕ) : ℝ :=
  ∑' t : ℤ, if t = 0 then 0 else straddlePhi m k κ (((m : ℤ) + 1) * 2 ^ (k - 1) * t)

/-- The term `sinc⁴(t n 2^{-D-2}) ∏_{e=1}^{D} cos²(π t (n + D + 1 - e) 2^{-e})` of `F(n, D)`
(normalized `sinc`, written as `Real.sinc (π ·)`). -/
noncomputable def fineFloorTerm (n D : ℕ) (t : ℤ) : ℝ :=
  Real.sinc (π * (t * n / 2 ^ (D + 2))) ^ 4 *
    ∏ e ∈ Icc 1 D, Real.cos (π * t * (n + D + 1 - e : ℕ) / 2 ^ e) ^ 2

/-- `F(n, D) = ∑_{t ≠ 0} sinc⁴(t n 2^{-D-2}) ∏_{e=1}^{D} cos²(π t (n + D + 1 - e) 2^{-e})`. -/
noncomputable def fineFloor (n D : ℕ) : ℝ :=
  ∑' t : ℤ, if t = 0 then 0 else fineFloorTerm n D t

theorem fineFloorTerm_nonneg (n D : ℕ) (t : ℤ) : 0 ≤ fineFloorTerm n D t := by
  unfold fineFloorTerm
  have h4 : 0 ≤ Real.sinc (π * (t * n / 2 ^ (D + 2))) ^ 4 := by positivity
  exact mul_nonneg h4 (prod_nonneg fun _ _ => sq_nonneg _)

theorem fineIndex_ne_zero {m k : ℕ} {t : ℤ} (ht : t ≠ 0) :
    ((m : ℤ) + 1) * 2 ^ (k - 1) * t ≠ 0 :=
  mul_ne_zero (by positivity) ht

/-- The family `t ↦ φ_k(N 2^{k-1} t)` (`t ≠ 0`) is a subfamily of `r ↦ φ_k(r)` (`r ≠ 0`). -/
theorem hasSum_fineFloorK_aux {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) :
    Summable (fun t : ℤ => if t = 0 then 0 else straddlePhi m k κ (((m : ℤ) + 1) * 2 ^ (k - 1) * t)) ∧
      fineFloorK m k κ ≤ relVariance m k κ := by
  set g : ℤ → ℝ := fun r => if r = 0 then 0 else straddlePhi m k κ r with hgdef
  have hg : HasSum g (relVariance m k κ) := hasSum_straddlePhi_ne_zero hk hkκ
  have hg0 : ∀ r, 0 ≤ g r := fun r => by
    by_cases hr : r = 0
    · simp [g, hr]
    · simp only [g, hr, ↓reduceIte]; exact straddlePhi_nonneg hk hkκ r
  have hinj : Function.Injective (fun t : ℤ => ((m : ℤ) + 1) * 2 ^ (k - 1) * t) := by
    intro a b h
    have hpos : ((m : ℤ) + 1) * 2 ^ (k - 1) ≠ 0 := by positivity
    exact mul_left_cancel₀ hpos h
  have hcomp : (fun t : ℤ => if t = 0 then 0 else straddlePhi m k κ (((m : ℤ) + 1) * 2 ^ (k - 1) * t))
      = g ∘ (fun t : ℤ => ((m : ℤ) + 1) * 2 ^ (k - 1) * t) := by
    ext t
    by_cases ht : t = 0
    · simp [g, ht]
    · simp [g, ht, fineIndex_ne_zero (m := m) (k := k) ht]
  refine ⟨?_, ?_⟩
  · rw [hcomp]; exact hg.summable.comp_injective hinj
  · have := tsum_comp_le_tsum_of_inj hg.summable hg0 hinj
    rw [hg.tsum_eq, ← hcomp] at this
    exact this

/-- **Proposition 7.12(c)**, first part: `V_k ≥ F_k`. -/
theorem fineFloorK_le_relVariance {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) :
    fineFloorK m k κ ≤ relVariance m k κ :=
  (hasSum_fineFloorK_aux hk hkκ).2

/-- The terms of `F_k` are those of `F(n_κ, κ - k)`, for `1 ≤ k < κ ≤ m`. -/
theorem straddlePhi_fine_eq {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k < κ) (hκm : κ ≤ m) (t : ℤ) :
    straddlePhi m k κ (((m : ℤ) + 1) * 2 ^ (k - 1) * t) = fineFloorTerm (m - κ + 1) (κ - k) t := by
  unfold straddlePhi fineFloorTerm
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hsinc : π * (((((m : ℤ) + 1) * 2 ^ (k - 1) * t : ℤ) : ℝ) * ((m - κ + 1 : ℕ) : ℝ) /
      (((m : ℝ) + 1) * 2 ^ (κ + 1))) =
      π * ((t : ℝ) * ((m - κ + 1 : ℕ) : ℝ) / 2 ^ (κ - k + 2)) := by
    have hp : (2 : ℝ) ^ (κ + 1) = 2 ^ (k - 1) * 2 ^ (κ - k + 2) := by
      rw [← pow_add]; congr 1; omega
    rw [hp]; push_cast; field_simp
  have hone : ∏ i ∈ Icc 1 (k - 1), Real.cos (π * ((((m : ℤ) + 1) * 2 ^ (k - 1) * t : ℤ) : ℝ) *
      ((m - i + 1 : ℕ) : ℝ) / (((m : ℝ) + 1) * 2 ^ i)) ^ 4 = 1 := by
    refine prod_eq_one fun i hi => ?_
    have hi' : i ≤ k - 1 := (mem_Icc.mp hi).2
    have harg : π * ((((m : ℤ) + 1) * 2 ^ (k - 1) * t : ℤ) : ℝ) * ((m - i + 1 : ℕ) : ℝ) /
        (((m : ℝ) + 1) * 2 ^ i) = π * (0 + ((t * (m - i + 1 : ℕ) * 2 ^ (k - 1 - i) : ℤ) : ℝ)) := by
      have hp : (2 : ℝ) ^ (k - 1) = 2 ^ (k - 1 - i) * 2 ^ i := by
        rw [← pow_add]; congr 1; omega
      push_cast; rw [hp]; field_simp; ring
    rw [harg, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, cos_sq_pi_mul_add_int, mul_zero, cos_zero]
    norm_num
  have hmap : Ico k κ = (Icc 1 (κ - k)).map (addLeftEmbedding (k - 1)) := by
    ext x
    simp only [mem_Ico, mem_map, mem_Icc, addLeftEmbedding_apply]
    constructor
    · intro hx; exact ⟨x - (k - 1), by omega, by omega⟩
    · rintro ⟨e, he, rfl⟩; omega
  have hprod : ∏ i ∈ Ico k κ, Real.cos (π * ((((m : ℤ) + 1) * 2 ^ (k - 1) * t : ℤ) : ℝ) *
      ((m - i + 1 : ℕ) : ℝ) / (((m : ℝ) + 1) * 2 ^ i)) ^ 2 =
      ∏ e ∈ Icc 1 (κ - k), Real.cos (π * t * ((m - κ + 1 + (κ - k) + 1 - e : ℕ) : ℝ) / 2 ^ e) ^ 2 := by
    rw [hmap, prod_map]
    refine prod_congr rfl fun e he => ?_
    have he' := mem_Icc.mp he
    simp only [addLeftEmbedding_apply]
    have hnat : m - (k - 1 + e) + 1 = m - κ + 1 + (κ - k) + 1 - e := by omega
    rw [hnat, pow_add]
    push_cast
    field_simp
  rw [hsinc, hone, hprod, mul_one]

/-- **Proposition 7.12(c)**, second part: `F_k = F(n_κ, κ - k)` for `1 ≤ k < κ ≤ m`. -/
theorem fineFloorK_eq {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k < κ) (hκm : κ ≤ m) :
    fineFloorK m k κ = fineFloor (m - κ + 1) (κ - k) := by
  unfold fineFloorK fineFloor
  congr 1; ext t
  by_cases ht : t = 0
  · simp [ht]
  simp only [ht, ↓reduceIte]
  exact straddlePhi_fine_eq hk hkκ hκm t

/-- The family defining `F(n, D)` is summable (`n ≥ 1`, `D ≥ 1`). -/
theorem summable_fineFloorTerm {n D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D) :
    Summable (fun t : ℤ => if t = 0 then 0 else fineFloorTerm n D t) := by
  have h := (hasSum_fineFloorK_aux (m := n + D) (k := 1) (κ := D + 1) le_rfl (by omega)).1
  convert h using 1
  ext t
  by_cases ht : t = 0
  · simp [ht]
  simp only [ht, ↓reduceIte]
  rw [straddlePhi_fine_eq le_rfl (by omega) (by omega)]
  congr 1; omega

end MergeDepth
