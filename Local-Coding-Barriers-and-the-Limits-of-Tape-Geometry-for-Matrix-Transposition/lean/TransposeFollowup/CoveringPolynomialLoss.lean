import Mathlib.Tactic

/-! Conservative common-base bounds for the explicit nonflattening
coefficients. Fixed constants, the level count and support size are paid
by one parameter; no scale-dependent constant is hidden. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

theorem covering_basic_coefficient_bounds {h Q α q : ℝ} {N : ℕ}
    (hlarge : 2 ^ 100 ≤ h) (hN : (N : ℝ) ≤ h) (hQ0 : 0 ≤ Q) (hQ : Q ≤ h)
    (hα : 0 < α) (hαinv : α⁻¹ ^ 4 ≤ h) (hq : 0 < q) (hqinv : q⁻¹ ≤ h) :
    let K₀ := 64 * (N : ℝ) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ) ^ 55 * L ^ 21
    let M := 33 ^ 4 * Q ^ 8 / α ^ 4
    K₀ ≤ h ^ 5 ∧ L ≤ h ^ 13 ∧ K ≤ h ^ 274 ∧ M ≤ h ^ 10 := by
  let K₀ := 64 * (N : ℝ) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ) ^ 55 * L ^ 21
  let M := 33 ^ 4 * Q ^ 8 / α ^ 4
  have hh : 0 ≤ h := (by norm_num : (0 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h64 : (64 : ℝ) ≤ h := (by norm_num : (64 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h8 : (8 : ℝ) ≤ h := (by norm_num : (8 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h55 : (2 : ℝ) ^ 55 ≤ h := (by norm_num : (2 : ℝ) ^ 55 ≤ 2 ^ 100).trans hlarge
  have h33 : (33 : ℝ) ^ 4 ≤ h := (by norm_num : (33 : ℝ) ^ 4 ≤ 2 ^ 100).trans hlarge
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hK₀ : K₀ ≤ h ^ 5 := by
    calc
      K₀ ≤ h * h ^ 4 := by dsimp only [K₀]; gcongr
      _ = _ := by ring
  have hL : L ≤ h ^ 13 := by
    calc
      L = 8 * K₀ ^ 2 * (q⁻¹) ^ 2 := by dsimp only [L]; rw [div_eq_mul_inv, inv_pow]; ring
      _ ≤ h * (h ^ 5) ^ 2 * h ^ 2 := by gcongr
      _ = _ := by ring
  have hK : K ≤ h ^ 274 := by
    calc
      K ≤ h * (h ^ 13) ^ 21 := by dsimp only [K]; gcongr
      _ = _ := by ring
  have hM : M ≤ h ^ 10 := by
    calc
      M = 33 ^ 4 * Q ^ 8 * (α⁻¹) ^ 4 := by dsimp only [M]; rw [div_eq_mul_inv, inv_pow]
      _ ≤ h * h ^ 8 * h := by gcongr
      _ = _ := by ring
  exact ⟨hK₀, hL, hK, hM⟩

theorem covering_profile_coefficient_bounds {h Q α q : ℝ} {N : ℕ}
    (hlarge : 2 ^ 100 ≤ h) (hN : (N : ℝ) ≤ h) (hQ0 : 0 ≤ Q) (hQ : Q ≤ h)
    (hα : 0 < α) (hαinv : α⁻¹ ^ 4 ≤ h) (hq : 0 < q) (hqinv : q⁻¹ ≤ h) :
    let K₀ := 64 * (N : ℝ) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ) ^ 55 * L ^ 21
    let M := 33 ^ 4 * Q ^ 8 / α ^ 4
    let A₆ := (2 ^ 21 + 1) ^ 4 * Q ^ 52
    let D := 393216 ^ 4 * A₆ * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100) * M
    6561 * D * (q⁻¹) ^ 2 ≤ h ^ 27499 ∧
      (128 * 6561 * 393216 ^ 4 * K₀ * K * L ^ 2 * M) * q⁻¹ ≤ h ^ 319 ∧
      (A₆ * 2 ^ 72 * K₀ ^ 2 * L ^ 2 * K ^ 107) * (q⁻¹) ^ 3 ≤ h ^ 29411 := by
  let K₀ := 64 * (N : ℝ) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ) ^ 55 * L ^ 21
  let M := 33 ^ 4 * Q ^ 8 / α ^ 4
  let A₆ := (2 ^ 21 + 1) ^ 4 * Q ^ 52
  let D := 393216 ^ 4 * A₆ * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100) * M
  have hh : 0 ≤ h := (by norm_num : (0 : ℝ) ≤ 2 ^ 100).trans hlarge
  have hA : ((2 : ℝ) ^ 21 + 1) ^ 4 ≤ h :=
    (by norm_num : ((2 : ℝ) ^ 21 + 1) ^ 4 ≤ 2 ^ 100).trans hlarge
  have hd : (393216 : ℝ) ^ 4 ≤ h := (by norm_num : (393216 : ℝ) ^ 4 ≤ 2 ^ 100).trans hlarge
  have h6561 : (6561 : ℝ) ≤ h := (by norm_num : (6561 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h128 : (128 : ℝ) ≤ h := (by norm_num : (128 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h68 : (2 : ℝ) ^ 68 ≤ h := (by norm_num : (2 : ℝ) ^ 68 ≤ 2 ^ 100).trans hlarge
  have h72 : (2 : ℝ) ^ 72 ≤ h := (by norm_num : (2 : ℝ) ^ 72 ≤ 2 ^ 100).trans hlarge
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hA0 : 0 ≤ A₆ := mul_nonneg
    (pow_nonneg (add_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 21) zero_le_one) 4)
    (pow_nonneg hQ0 52)
  obtain ⟨hK₀, hL, hK, hM⟩ := covering_basic_coefficient_bounds hlarge hN hQ0 hQ hα hαinv hq hqinv
  have hA₆ : A₆ ≤ h ^ 53 := by
    calc
      A₆ ≤ h * h ^ 52 := mul_le_mul hA (pow_le_pow_left₀ hQ0 hQ 52) (pow_nonneg hQ0 52) hh
      _ = _ := by ring
  have hm {a b : ℝ} {i j : ℕ} (ha : 0 ≤ a ∧ a ≤ h ^ i) (hb : 0 ≤ b ∧ b ≤ h ^ j) :
      0 ≤ a * b ∧ a * b ≤ h ^ (i + j) :=
    ⟨mul_nonneg ha.1 hb.1,
      (mul_le_mul ha.2 hb.2 hb.1 (pow_nonneg hh i)).trans_eq (pow_add h i j).symm⟩
  have hpd : 0 ≤ (393216 : ℝ) ^ 4 ∧ (393216 : ℝ) ^ 4 ≤ h ^ 1 :=
    ⟨pow_nonneg (by norm_num) 4, by simpa only [pow_one] using hd⟩
  have hp68 : 0 ≤ (2 : ℝ) ^ 68 ∧ (2 : ℝ) ^ 68 ≤ h ^ 1 :=
    ⟨pow_nonneg (by norm_num) 68, by simpa only [pow_one] using h68⟩
  have hp72 : 0 ≤ (2 : ℝ) ^ 72 ∧ (2 : ℝ) ^ 72 ≤ h ^ 1 :=
    ⟨pow_nonneg (by norm_num) 72, by simpa only [pow_one] using h72⟩
  have hp6561 : 0 ≤ (6561 : ℝ) ∧ (6561 : ℝ) ≤ h ^ 1 :=
    ⟨by norm_num, by simpa only [pow_one] using h6561⟩
  have hp128 : 0 ≤ (128 : ℝ) ∧ (128 : ℝ) ≤ h ^ 1 :=
    ⟨by norm_num, by simpa only [pow_one] using h128⟩
  have hpK₀ : 0 ≤ K₀ ∧ K₀ ≤ h ^ 5 := ⟨hK₀0, hK₀⟩
  have hpK₀2 : 0 ≤ K₀ ^ 2 ∧ K₀ ^ 2 ≤ h ^ 10 :=
    ⟨sq_nonneg _, by simpa only [← pow_mul] using pow_le_pow_left₀ hK₀0 hK₀ 2⟩
  have hpL2 : 0 ≤ L ^ 2 ∧ L ^ 2 ≤ h ^ 26 :=
    ⟨sq_nonneg _, by simpa only [← pow_mul] using pow_le_pow_left₀ hL0 hL 2⟩
  have hpK : 0 ≤ K ∧ K ≤ h ^ 274 := ⟨hK0, hK⟩
  have hpK100 : 0 ≤ K ^ 100 ∧ K ^ 100 ≤ h ^ 27400 :=
    ⟨pow_nonneg hK0 100, by simpa only [← pow_mul] using pow_le_pow_left₀ hK0 hK 100⟩
  have hpK107 : 0 ≤ K ^ 107 ∧ K ^ 107 ≤ h ^ 29318 :=
    ⟨pow_nonneg hK0 107, by simpa only [← pow_mul] using pow_le_pow_left₀ hK0 hK 107⟩
  have hpM : 0 ≤ M ∧ M ≤ h ^ 10 := ⟨hM0, hM⟩
  have hpA : 0 ≤ A₆ ∧ A₆ ≤ h ^ 53 := ⟨hA0, hA₆⟩
  have hpq : 0 ≤ q⁻¹ ∧ q⁻¹ ≤ h ^ 1 :=
    ⟨inv_nonneg.mpr hq.le, by simpa only [pow_one] using hqinv⟩
  have hpq2 : 0 ≤ (q⁻¹) ^ 2 ∧ (q⁻¹) ^ 2 ≤ h ^ 2 :=
    ⟨sq_nonneg _, pow_le_pow_left₀ hpq.1 hqinv 2⟩
  have hpq3 : 0 ≤ (q⁻¹) ^ 3 ∧ (q⁻¹) ^ 3 ≤ h ^ 3 :=
    ⟨pow_nonneg hpq.1 3, pow_le_pow_left₀ hpq.1 hqinv 3⟩
  have hpD : 0 ≤ D ∧ D ≤ h ^ 27496 :=
    hm (hm (hm hpd hpA) (hm (hm (hm hp68 hpK₀) hpL2) hpK100)) hpM
  refine ⟨(hm (hm hp6561 hpD) hpq2).2, ?_, ?_⟩
  · exact (hm (hm (hm (hm (hm (hm (hm hp128 hp6561) hpd) hpK₀) hpK) hpL2) hpM) hpq).2
  · exact (hm (hm (hm (hm (hm hpA hp72) hpK₀2) hpL2) hpK107) hpq3).2

theorem localized_separation_coefficient_bound {h Q α q : ℝ} {N : ℕ}
    (hlarge : 2 ^ 100 ≤ h) (hN : (N : ℝ) ≤ h) (hQ0 : 0 ≤ Q) (hQ : Q ≤ h)
    (hα : 0 < α) (hαinv : α⁻¹ ^ 4 ≤ h) (hq : 0 < q) (hqinv : q⁻¹ ≤ h) :
    let K₀ := 64 * (N : ℝ) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ) ^ 55 * L ^ 21
    let M := 33 ^ 4 * Q ^ 8 / α ^ 4
    (32768 * K₀ * L ^ 2 * K ^ 4 * M) * (q⁻¹) ^ 2 ≤ h ^ 1140 := by
  let K₀ := 64 * (N : ℝ) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ) ^ 55 * L ^ 21
  let M := 33 ^ 4 * Q ^ 8 / α ^ 4
  have hh : 0 ≤ h := (by norm_num : (0 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h32768 : (32768 : ℝ) ≤ h := (by norm_num : (32768 : ℝ) ≤ 2 ^ 100).trans hlarge
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  obtain ⟨hK₀, hL, hK, hM⟩ := covering_basic_coefficient_bounds hlarge hN hQ0 hQ hα hαinv hq hqinv
  have h1 := mul_le_mul h32768 hK₀ hK₀0 hh
  have h2 := mul_le_mul h1 (pow_le_pow_left₀ hL0 hL 2) (sq_nonneg L)
    (show 0 ≤ h * h ^ 5 by positivity)
  have h3 := mul_le_mul h2 (pow_le_pow_left₀ hK0 hK 4) (pow_nonneg hK0 4)
    (show 0 ≤ h * h ^ 5 * (h ^ 13) ^ 2 by positivity)
  have h4 := mul_le_mul h3 hM hM0
    (show 0 ≤ h * h ^ 5 * (h ^ 13) ^ 2 * (h ^ 274) ^ 4 by positivity)
  have h5 := mul_le_mul h4 (pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hqinv 2) (sq_nonneg (q⁻¹))
    (show 0 ≤ h * h ^ 5 * (h ^ 13) ^ 2 * (h ^ 274) ^ 4 * h ^ 10 by positivity)
  exact h5.trans_eq (by ring)

end TransposeFollowup
