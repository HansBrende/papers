import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Explicit exponent margins absorb the profile loss and the factor4
from dyadic interpolation into one uniform cardinal lower bound. -/
namespace TransposeFollowup
set_option autoImplicit false

theorem separated_power_absorption {η ρ R δ ε κ n : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 256)
    (hρscale : ρ ≤ η ^ ε) (hκ : 0 < κ) (hδ : δ ≤ ε * κ / 2)
    (hR : 0 ≤ R) (hRρ : R ≤ 4 * ρ) (hn : 0 ≤ n)
    (hmass : 1 ≤ η ^ (-δ) * n * R ^ κ) :
    ρ ^ (-κ / 4) ≤ n := by
  have hroot : ρ ^ (1 / 4 : ℝ) ≤ 1 / 4 := by
    have hh := Real.rpow_le_rpow hρ.le hρsmall (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have he : (1 / 256 : ℝ) ^ (1 / 4 : ℝ) = 1 / 4 := by
      rw [show (1 / 256 : ℝ) = (1 / 4 : ℝ) ^ (4 : ℕ) by norm_num]
      simpa only [Nat.cast_ofNat, one_div] using
        Real.pow_rpow_inv_natCast (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rwa [he] at hh
  have hRpower : R ≤ ρ ^ (3 / 4 : ℝ) := by
    calc
      R ≤ 4 * ρ := hRρ
      _ = 4 * ρ ^ (1 / 4 : ℝ) * ρ ^ (3 / 4 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hρ]
        norm_num
      _ ≤ 4 * (1 / 4) * ρ ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by norm_num))
          (Real.rpow_nonneg hρ.le _)
      _ = _ := by ring
  have hl : ρ ^ (κ / 2) ≤ η ^ δ := by
    calc
      _ ≤ (η ^ ε) ^ (κ / 2) := Real.rpow_le_rpow hρ.le hρscale (by positivity)
      _ = η ^ (ε * κ / 2) := by rw [← Real.rpow_mul hη.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hη hηone hδ
  have hm : η ^ δ ≤ n * R ^ κ := by
    have hh := mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hη.le δ)
    have he : η ^ δ * η ^ (-δ) = 1 := by rw [← Real.rpow_add hη]; simp
    simpa only [mul_one, ← mul_assoc, he, one_mul] using hh
  have hu : R ^ κ ≤ ρ ^ (3 * κ / 4) := by
    calc
      _ ≤ (ρ ^ (3 / 4 : ℝ)) ^ κ := Real.rpow_le_rpow hR hRpower hκ.le
      _ = _ := by rw [← Real.rpow_mul hρ.le]; congr 1; ring
  have hh : ρ ^ (κ / 2) ≤ n * ρ ^ (3 * κ / 4) :=
    (hl.trans hm).trans (mul_le_mul_of_nonneg_left hu hn)
  have hd := (div_le_iff₀ (Real.rpow_pos_of_pos hρ (3 * κ / 4))).mpr hh
  rw [← Real.rpow_sub hρ] at hd
  simpa only [show κ / 2 - 3 * κ / 4 = -κ / 4 by ring] using hd

end TransposeFollowup
