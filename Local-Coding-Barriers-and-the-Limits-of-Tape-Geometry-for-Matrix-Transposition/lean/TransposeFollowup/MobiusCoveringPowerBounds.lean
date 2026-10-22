import TransposeFollowup.CoveringPowerEnvelope
import TransposeFollowup.MobiusSmallBallVolume

/-! Conversion of finite ENNReal covering profiles to real power bounds.
The ball volume is the actual Haar volume, with its scalar retained. -/
namespace TransposeFollowup.RealMobius
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem covering_profile_power_bounds {η h Q α θ : ℝ} {N : ℕ} {n n₃ V : ℝ≥0∞}
    (hη : 0 < η) (hηhalf : η ≤ 1 / 2) (hlarge : 2 ^ 100 ≤ h)
    (hN : (N : ℝ) ≤ h) (hQ0 : 0 ≤ Q) (hQ : Q ≤ h)
    (hα : 0 < α) (hαinv : α⁻¹ ^ 4 ≤ h) (hθ : 0 < θ) (hθinv : θ⁻¹ ≤ h)
    (hc : (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) ≤ h)
    (hci : (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ)⁻¹ ≤ h)
    (hnt : n ≠ ⊤) (hVt : V ≠ ⊤) :
    let q := ENNReal.ofReal θ
    let K₀ := 64 * (N : ℝ≥0∞) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
    let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
    let A₆ := ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52)
    let D := 393216 ^ 4 * A₆ * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100) * M
    let v := (Measure.haar : Measure Group) (mobiusIdentityBall η)
    n₃ * q ^ 2 ≤ 6561 * D * n →
    q ≤ 128 * 6561 * 393216 ^ 4 * K₀ * K * L ^ 2 * M * V * n * v →
    n * q ^ 3 * V * v ≤ A₆ * 2 ^ 72 * K₀ ^ 2 * L ^ 2 * K ^ 107 →
    n₃.toReal ≤ h ^ 30000 * n.toReal ∧
      1 ≤ h ^ 30000 * n.toReal * V.toReal * η ^ 3 ∧
      n.toReal * V.toReal * η ^ 3 ≤ h ^ 30000 := by
  dsimp only
  let q := ENNReal.ofReal θ
  let K₀ := 64 * (N : ℝ≥0∞) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
  let A₆ := ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52)
  let D := 393216 ^ 4 * A₆ * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100) * M
  let v := (Measure.haar : Measure Group) (mobiusIdentityBall η)
  intro htrip hlo hhi
  have hq0 : q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hθ
  have hK₀t : K₀ ≠ ⊤ := by dsimp only [K₀]; finiteness
  have hLt : L ≠ ⊤ := by dsimp only [L]; finiteness
  have hKt : K ≠ ⊤ := by dsimp only [K]; finiteness
  have hMt : M ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA₆t : A₆ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hC₆t : 2 ^ 68 * K₀ * L ^ 2 * K ^ 100 ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hK₀t) (ENNReal.pow_ne_top hLt))
    (ENNReal.pow_ne_top hKt)
  have hDt : D ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hA₆t) hC₆t) hMt
  have hvt : v ≠ ⊤ := (mobiusIdentityBall_haar_lt_top hη).ne
  have htr := ENNReal.toReal_mono (show 6561 * D * n ≠ ⊤ by finiteness) htrip
  have hl := ENNReal.toReal_mono
    (show 128 * 6561 * 393216 ^ 4 * K₀ * K * L ^ 2 * M * V * n * v ≠ ⊤ by finiteness) hlo
  have hGt : A₆ * 2 ^ 72 * K₀ ^ 2 * L ^ 2 * K ^ 107 ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA₆t (by finiteness))
      (ENNReal.pow_ne_top hK₀t)) (ENNReal.pow_ne_top hLt)) (ENNReal.pow_ne_top hKt)
  have hu := ENNReal.toReal_mono hGt hhi
  have hM0 : 0 ≤ 33 ^ 4 * Q ^ 8 / α ^ 4 := by positivity
  have hA0 : 0 ≤ ((2 : ℝ) ^ 21 + 1) ^ 4 * Q ^ 52 := mul_nonneg
    (pow_nonneg (by norm_num) 4) (pow_nonneg hQ0 52)
  dsimp only [D, A₆, M, K, L, K₀, q] at htr hl hu
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hθ.le,
    ENNReal.toReal_ofReal hM0, ENNReal.toReal_ofReal hA0] at htr hl hu
  have hvlo := ENNReal.toReal_mono hvt (haar_identityBall_lower hη hηhalf)
  have hvhi := ENNReal.toReal_mono (by finiteness) (haar_identityBall_upper hη hηhalf)
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (show 0 ≤ η ^ 3 / 512 by positivity)] at hvlo
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (show 0 ≤ 96 * η ^ 3 by positivity)] at hvhi
  have hc0 : (0 : ℝ) < (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) := by
    exact_mod_cast haar_column_factor_pos
  obtain ⟨ht, hf, hg⟩ := covering_profile_coefficient_bounds hlarge hN hQ0 hQ hα hαinv hθ hθinv
  exact covering_profile_power_envelope hlarge hθ hη hc0 hc hci
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ht hf hg htr hl hu (by simpa only [mul_div_assoc] using hvlo)
    (by convert hvhi using 1; ring)

end TransposeFollowup.RealMobius
