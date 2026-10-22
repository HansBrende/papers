import TransposeFollowup.ApproximatePowerCover
import TransposeFollowup.CoveringPolynomialLoss

/-! The fixed product needed by commuting extraction has a polynomial
covering cost in the existing profile envelope. The finite translate
witness is the actual approximate-group witness, not an added premise. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem fixed_power_coefficient_bound (n : ℕ) {h Q α q y : ℝ} {N : ℕ}
    (hlarge : 2 ^ 100 ≤ h) (hN : (N : ℝ) ≤ h) (hQ0 : 0 ≤ Q) (hQ : Q ≤ h)
    (hα : 0 < α) (hαinv : α⁻¹ ^ 4 ≤ h) (hq : 0 < q) (hqinv : q⁻¹ ≤ h)
    (hy0 : 0 ≤ y) :
    let K₀ := 64 * (N : ℝ) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ) ^ 55 * L ^ 21
    y ≤ 512 * K ^ 16 →
      (8 * (2 * Q) ^ (4 * n + 3) + 1) ^ 4 * y ^ (2 * n + 1) * (33 ^ 4 * Q ^ 8 / α ^ 4) ≤ h ^ (8802 * n + 4427) := by
  dsimp only
  intro hy
  let K₀ := 64 * (N : ℝ) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ) ^ 55 * L ^ 21
  have hh : 0 ≤ h := (by norm_num : (0 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h1 : 1 ≤ h := (by norm_num : (1 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h2 : 2 ≤ h := (by norm_num : (2 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h9 : 9 ≤ h := (by norm_num : (9 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h512 : 512 ≤ h := (by norm_num : (512 : ℝ) ≤ 2 ^ 100).trans hlarge
  have hK0 : 0 ≤ K := by dsimp only [K, L, K₀]; positivity
  obtain ⟨_, _, hK, hM⟩ := covering_basic_coefficient_bounds hlarge hN hQ0 hQ hα hαinv hq hqinv
  have hyb : y ≤ h ^ 4385 := by
    calc
      y ≤ 512 * K ^ 16 := hy
      _ ≤ h * (h ^ 274) ^ 16 := mul_le_mul h512 (pow_le_pow_left₀ hK0 hK 16) (pow_nonneg hK0 16) hh
      _ = _ := by ring
  have h2Q : 2 * Q ≤ h ^ 2 := by
    calc
      2 * Q ≤ h * h := mul_le_mul h2 hQ hQ0 hh
      _ = _ := by ring
  have hQpow : (2 * Q) ^ (4 * n + 3) ≤ h ^ (2 * (4 * n + 3)) := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Q) h2Q (4 * n + 3)
  have hp1 : 1 ≤ h ^ (2 * (4 * n + 3)) := one_le_pow₀ h1
  have h9sq : 9 ≤ h ^ 2 := h9.trans (by nlinarith)
  have hbase : 8 * (2 * Q) ^ (4 * n + 3) + 1 ≤ h ^ (2 * (4 * n + 3) + 2) := by
    calc
      _ ≤ 9 * h ^ (2 * (4 * n + 3)) := by nlinarith
      _ ≤ h ^ 2 * h ^ (2 * (4 * n + 3)) := mul_le_mul_of_nonneg_right h9sq (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hfour : (8 * (2 * Q) ^ (4 * n + 3) + 1) ^ 4 ≤ h ^ ((2 * (4 * n + 3) + 2) * 4) := by
    have hb0 : 0 ≤ 8 * (2 * Q) ^ (4 * n + 3) + 1 := add_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg (by norm_num) hQ0) (4 * n + 3))) zero_le_one
    simpa only [← pow_mul] using pow_le_pow_left₀ hb0 hbase 4
  have hypow : y ^ (2 * n + 1) ≤ h ^ (4385 * (2 * n + 1)) := by
    simpa only [← pow_mul] using pow_le_pow_left₀ hy0 hyb (2 * n + 1)
  have hM0 : 0 ≤ 33 ^ 4 * Q ^ 8 / α ^ 4 := div_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg hQ0 8)) (pow_nonneg hα.le 4)
  calc
    _ ≤ h ^ ((2 * (4 * n + 3) + 2) * 4) * h ^ (4385 * (2 * n + 1)) * h ^ 10 := mul_le_mul
      (mul_le_mul hfour hypow (pow_nonneg hy0 (2 * n + 1)) (pow_nonneg hh ((2 * (4 * n + 3) + 2) * 4))) hM hM0
      (mul_nonneg (pow_nonneg hh ((2 * (4 * n + 3) + 2) * 4)) (pow_nonneg hh (4385 * (2 * n + 1))))
    _ = h ^ (8802 * n + 4427) := by
      rw [← pow_add, ← pow_add]
      exact congrArg (fun k : ℕ => h ^ k) (by omega)

theorem localized_fixed_power_coveringNumber_envelope (n : ℕ) {U : Set G} (Y : Finset G)
    {h Q α θ : ℝ} {N : ℕ} {η : ℝ≥0}
    (hlarge : 2 ^ 100 ≤ h) (hN : (N : ℝ) ≤ h) (hQ1 : 1 ≤ Q) (hQ : Q ≤ h)
    (hα : 0 < α) (hαone : α ≤ 1) (hαinv : α⁻¹ ^ 4 ≤ h)
    (hθ : 0 < θ) (hθinv : θ⁻¹ ≤ h) (hη : 0 < η)
    (hU : U ⊆ matrixEntryBox Q) (hUi : U⁻¹ = U)
    (hY : (Y : Set G) ⊆ U ^ 2) (hdouble : U ^ 2 ⊆ (Y : Set G) * U) :
    let q := ENNReal.ofReal θ
    let K₀ := 64 * (N : ℝ≥0∞) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
    (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 →
    let A := U ^ 2 ∩ mobiusIdentityBall α
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A ^ (n + 1))) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A ^ (n + 1))) : ℝ≥0∞).toReal ≤
        h ^ (8802 * n + 4427) * (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal := by
  dsimp only
  intro hcard
  let q := ENNReal.ofReal θ
  let K₀ := 64 * (N : ℝ≥0∞) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  have hq0 : q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hθ
  have hK₀t : K₀ ≠ ⊤ := by dsimp only [K₀]; finiteness
  have hLt : L ≠ ⊤ := by dsimp only [L]; finiteness
  have hKt : K ≠ ⊤ := by dsimp only [K]; finiteness
  have hcardR := ENNReal.toReal_mono (show 512 * K ^ 16 ≠ ⊤ by finiteness) hcard
  dsimp only [K, L, K₀, q] at hcardR
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hθ.le] at hcardR
  have hcoef := fixed_power_coefficient_bound n hlarge hN (by linarith : 0 ≤ Q) hQ
    hα hαinv hθ hθinv (Nat.cast_nonneg Y.card) hcardR
  obtain ⟨hAfin, hpowfin, hbound⟩ := localized_set_pow_coveringNumber Y n
    hQ1 hα hαone hη hU hUi hY hdouble
  exact ⟨hAfin, hpowfin, hbound.trans (mul_le_mul_of_nonneg_right hcoef ENNReal.toReal_nonneg)⟩

end TransposeFollowup.SL2Projection
