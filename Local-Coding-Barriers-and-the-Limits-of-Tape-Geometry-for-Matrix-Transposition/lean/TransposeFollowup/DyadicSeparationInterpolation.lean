import TransposeFollowup.DyadicWalkSupportScale

/-! Choose a coarser dyadic radius inside the proved index window, and
choose a fixed scale threshold making that window cover all required radii. -/
namespace TransposeFollowup
set_option autoImplicit false

theorem exists_quarter_scale_between {j J : ℕ} {ρ : ℝ}
    (hηρ : (1 / 4 : ℝ) ^ j < ρ) (hρJ : ρ ≤ (1 / 4 : ℝ) ^ J) :
    ∃ v : ℕ, J ≤ v ∧ v ≤ j ∧ ρ ≤ (1 / 4 : ℝ) ^ v ∧ (1 / 4 : ℝ) ^ v < 4 * ρ := by
  have hρ : 0 < ρ := (by positivity : (0 : ℝ) < (1 / 4 : ℝ) ^ j).trans hηρ
  have hρone : ρ ≤ 1 := hρJ.trans (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨v, hvlow, hvhi⟩ := exists_nat_pow_near_of_lt_one hρ hρone
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
  have hJv : J ≤ v := by
    by_contra hn
    have hh := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) (show v + 1 ≤ J by omega)
    exact (not_lt_of_ge (hρJ.trans hh)) hvlow
  have hvj : v ≤ j := by
    by_contra hn
    have hh := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) (show j ≤ v by omega)
    exact (not_lt_of_ge (hvhi.trans hh)) hηρ
  refine ⟨v, hJv, hvj, hvhi, ?_⟩
  rw [pow_succ] at hvlow
  linarith

theorem exists_separation_window_threshold {ε : ℝ} (hε : 0 < ε) (J : ℕ) :
    ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j →
      ((1 / 4 : ℝ) ^ j) ^ ε ≤ min (1 / 256) ((1 / 4 : ℝ) ^ J) := by
  let C := min (1 / 256 : ℝ) ((1 / 4 : ℝ) ^ J)
  have hC : 0 < C := lt_min (by norm_num) (by positivity)
  obtain ⟨J₀, hJ₀⟩ := exists_quarter_scale_threshold (Real.rpow_pos_of_pos hC (1 / ε))
  refine ⟨J₀, ?_⟩
  intro j hj
  have hh := Real.rpow_le_rpow (by positivity) (hJ₀ j hj) hε.le
  have he : (C ^ (1 / ε)) ^ ε = C := by
    rw [← Real.rpow_mul hC.le, one_div_mul_cancel hε.ne', Real.rpow_one]
  rwa [he] at hh

end TransposeFollowup
