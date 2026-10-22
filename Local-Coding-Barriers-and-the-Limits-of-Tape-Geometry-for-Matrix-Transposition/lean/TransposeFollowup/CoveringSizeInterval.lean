import TransposeFollowup.CoveringPowerEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Intermediate covering-number size and small tripling, with explicit
exponent margins. These arithmetic lemmas make no product-growth claim. -/
namespace TransposeFollowup
set_option autoImplicit false

theorem covering_envelope_size_interval {η δ κ γ β n n₃ V : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hn : 0 ≤ n)
    (hδκ : δ ≤ κ / 2) (hδγ : δ ≤ γ / 2) (hδβ : δ ≤ β)
    (hVlo : η ^ (-γ) ≤ V) (hVhi : V ≤ η ^ (-3 + κ))
    (htrip : n₃ ≤ η ^ (-δ) * n)
    (hlo : 1 ≤ η ^ (-δ) * n * V * η ^ 3)
    (hhi : n * V * η ^ 3 ≤ η ^ (-δ)) :
    η ^ (-κ / 2) ≤ n ∧ n ≤ η ^ (-3 + γ / 2) ∧ n₃ ≤ η ^ (-β) * n := by
  have helo : η ^ (-δ) * η ^ (-3 + κ) * η ^ 3 = η ^ (κ - δ) := by
    rw [← Real.rpow_natCast η 3, ← Real.rpow_add hη, ← Real.rpow_add hη]
    congr 1
    norm_num
    ring
  have helower : 1 ≤ n * η ^ (κ - δ) := by
    calc
      1 ≤ η ^ (-δ) * n * V * η ^ 3 := hlo
      _ ≤ η ^ (-δ) * n * η ^ (-3 + κ) * η ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hVhi (mul_nonneg (Real.rpow_nonneg hη.le _) hn))
          (pow_nonneg hη.le 3)
      _ = n * (η ^ (-δ) * η ^ (-3 + κ) * η ^ 3) := by ring
      _ = _ := by rw [helo]
  have hnlo : η ^ (-(κ - δ)) ≤ n := by
    have he := (div_le_iff₀ (Real.rpow_pos_of_pos hη (κ - δ))).mpr helower
    simpa only [one_div, Real.rpow_neg hη.le] using he
  have hehi : η ^ (-γ) * η ^ 3 = η ^ (3 - γ) := by
    rw [← Real.rpow_natCast η 3, ← Real.rpow_add hη]
    congr 1
    norm_num
    ring
  have heupper : n * η ^ (3 - γ) ≤ η ^ (-δ) := by
    calc
      _ = n * η ^ (-γ) * η ^ 3 := by rw [← hehi]; ring
      _ ≤ n * V * η ^ 3 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hVlo hn) (pow_nonneg hη.le 3)
      _ ≤ _ := hhi
  have hnhi : n ≤ η ^ (-δ - (3 - γ)) := by
    rw [Real.rpow_sub hη]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hη (3 - γ))).mpr heupper
  exact ⟨(Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith)).trans hnlo,
    hnhi.trans (Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith)),
    htrip.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith)) hn)⟩

theorem exists_covering_loss_exponent {κ γ β : ℝ} (hκ : 0 < κ) (hγ : 0 < γ) (hβ : 0 < β) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ 30000 * s ≤ κ / 2 ∧
      30000 * s ≤ γ / 2 ∧ 30000 * s ≤ β := by
  let s := min 1 (min (κ / 60000) (min (γ / 60000) (β / 30000)))
  have hs : 0 < s := lt_min zero_lt_one (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hsk : s ≤ κ / 60000 := (min_le_right _ _).trans (min_le_left _ _)
  have hsg : s ≤ γ / 60000 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsb : s ≤ β / 30000 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨s, hs, min_le_left _ _, by linarith, by linarith, by linarith⟩

end TransposeFollowup
