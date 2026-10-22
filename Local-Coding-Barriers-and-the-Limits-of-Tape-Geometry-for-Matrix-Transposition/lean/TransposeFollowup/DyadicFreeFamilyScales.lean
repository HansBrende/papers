import TransposeFollowup.RationalPackedFamily

/-! Fixed-seed numerical scales for the rational near-identity free family.
The seed is independent of the requested radius. -/
namespace TransposeFollowup.RationalFreePair
open Classical BoundedCoordinatePacking
set_option autoImplicit false

noncomputable def dyadicRadius (r : ℕ) : ℝ := 1 / (2 : ℝ) ^ r

noncomputable def dyadicEntryBound (r : ℕ) : ℝ :=
  (1 + 8 / (baseDenominator 9999 : ℝ)) ^ (32 * r)

def dyadicDenominator (r : ℕ) : ℕ := seedDenominator 9999 ^ (64 * r)

theorem fixed_seed_growth : (1 + 8 / (baseDenominator 9999 : ℝ)) ^ 64 ≤ 2 := by
  norm_num [baseDenominator]

theorem fixed_seed_denominator : seedDenominator 9999 = 900030000 := by
  norm_num [seedDenominator, baseDenominator]

theorem dyadicRadius_pos (r : ℕ) : 0 < dyadicRadius r := by unfold dyadicRadius; positivity

theorem dyadicRadius_le_one (r : ℕ) : dyadicRadius r ≤ 1 := by
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

theorem dyadicEntryBound_one_le (r : ℕ) : 1 ≤ dyadicEntryBound r := by
  exact one_le_pow₀ (by norm_num [baseDenominator])

theorem dyadicEntryBound_pow_eight (r : ℕ) :
    dyadicEntryBound r ^ 8 ≤ ((2 : ℝ) ^ r) ^ 4 := by
  calc
    _ = ((1 + 8 / (baseDenominator 9999 : ℝ)) ^ 64) ^ (4 * r) := by
      simp only [dyadicEntryBound, ← pow_mul]
      congr 1
      omega
    _ ≤ (2 : ℝ) ^ (4 * r) := pow_le_pow_left₀ (by positivity) fixed_seed_growth _
    _ = _ := by rw [← pow_mul]; congr 1; omega

theorem dyadic_bin_four_le (r : ℕ) :
    (binCount (dyadicEntryBound r) (dyadicRadius r / (8 * dyadicEntryBound r)) : ℝ) ^ 4 ≤
      17 ^ 4 * ((2 : ℝ) ^ r) ^ 8 := by
  have h := binCount_near_identity_le (dyadicEntryBound_one_le r)
    (dyadicRadius_pos r) (dyadicRadius_le_one r)
  calc
    _ ≤ (17 * dyadicEntryBound r ^ 2 / dyadicRadius r) ^ 4 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h _
    _ = 17 ^ 4 * dyadicEntryBound r ^ 8 * ((2 : ℝ) ^ r) ^ 4 := by
      unfold dyadicRadius
      rw [div_div_eq_mul_div]
      ring
    _ ≤ 17 ^ 4 * (((2 : ℝ) ^ r) ^ 4) * ((2 : ℝ) ^ r) ^ 4 := by
      gcongr
      exact dyadicEntryBound_pow_eight r
    _ = _ := by ring

theorem dyadic_bin_budget {r : ℕ} (hr : 5 ≤ r) :
    binCount (dyadicEntryBound r) (dyadicRadius r / (8 * dyadicEntryBound r)) ^ 4 *
      2 ^ (4 * r) ≤ 2 ^ (16 * r) := by
  have hc : (17 : ℝ) ^ 4 ≤ ((2 : ℝ) ^ r) ^ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ 20 := by norm_num
      _ ≤ (2 : ℝ) ^ (r * 4) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := pow_mul _ _ _
  have hk : (binCount (dyadicEntryBound r)
      (dyadicRadius r / (8 * dyadicEntryBound r)) : ℝ) ^ 4 ≤ (2 : ℝ) ^ (12 * r) := by
    calc
      _ ≤ 17 ^ 4 * ((2 : ℝ) ^ r) ^ 8 := dyadic_bin_four_le r
      _ ≤ ((2 : ℝ) ^ r) ^ 4 * ((2 : ℝ) ^ r) ^ 8 := by gcongr
      _ = (2 : ℝ) ^ (12 * r) := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
  have hnat : binCount (dyadicEntryBound r)
      (dyadicRadius r / (8 * dyadicEntryBound r)) ^ 4 ≤ 2 ^ (12 * r) := by exact_mod_cast hk
  calc
    _ ≤ 2 ^ (12 * r) * 2 ^ (4 * r) := Nat.mul_le_mul_right _ hnat
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem dyadic_card_with_base {r : ℕ} (hr : 1 ≤ r) :
    2 ^ (3 * r) + 1 ≤ (2 : ℕ) ^ (4 * r) := by
  have hp : 1 ≤ (2 : ℕ) ^ (3 * r) := Nat.one_le_pow _ _ (by omega)
  have hq : 2 ≤ (2 : ℕ) ^ r := by
    simpa using (pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hr)
  have he : 2 ^ (4 * r) = (2 : ℕ) ^ (3 * r) * 2 ^ r := by
    rw [← pow_add]
    congr 1
    omega
  rw [he]
  nlinarith

theorem dyadic_packing_budget {r : ℕ} (hr : 5 ≤ r) :
    binCount (dyadicEntryBound r) (dyadicRadius r / (8 * dyadicEntryBound r)) ^ 4 *
      (2 ^ (3 * r) + 1) ≤ 2 ^ (16 * r) :=
  (Nat.mul_le_mul_left _ (dyadic_card_with_base (by omega))).trans (dyadic_bin_budget hr)

theorem dyadicDenominator_pos (r : ℕ) : 0 < dyadicDenominator r :=
  pow_pos (seedDenominator_pos _) _

theorem dyadicDenominator_lower (r : ℕ) : (2 : ℕ) ^ r ≤ dyadicDenominator r := by
  calc
    _ ≤ (2 : ℕ) ^ (64 * r) := pow_le_pow_right' (by norm_num) (by omega)
    _ ≤ _ := pow_le_pow_left' (by rw [fixed_seed_denominator]; norm_num) _

theorem dyadicDenominator_upper (r : ℕ) : dyadicDenominator r ≤ (2 : ℕ) ^ (1920 * r) := by
  calc
    _ ≤ ((2 : ℕ) ^ 30) ^ (64 * r) := by
      apply pow_le_pow_left'
      rw [fixed_seed_denominator]
      norm_num
    _ = _ := by rw [← pow_mul]; congr 1; omega

theorem dyadicDenominator_card_bound (r : ℕ) :
    dyadicDenominator r ≤ ((2 : ℕ) ^ (3 * r)) ^ 640 := by
  have he : ((2 : ℕ) ^ (3 * r)) ^ 640 = 2 ^ (1920 * r) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [he]
  exact dyadicDenominator_upper r

end TransposeFollowup.RationalFreePair
