import TransposeFollowup.DyadicSeparationInterpolation

/-! Uniform dyadic thresholds absorb any fixed positive coefficient. -/
namespace TransposeFollowup.SL2Projection
set_option autoImplicit false

theorem exists_dyadic_scaled_rpow_bound {c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → c * ((1 / 4 : ℝ) ^ j) ^ e ≤ 1 := by
  obtain ⟨Jc, hJc⟩ := exists_quarter_scale_threshold (one_div_pos.mpr hc)
  obtain ⟨J, hJ⟩ := exists_separation_window_threshold he Jc
  refine ⟨J, ?_⟩
  intro j hj
  have hh : ((1 / 4 : ℝ) ^ j) ^ e ≤ 1 / c :=
    ((hJ j hj).trans (min_le_right _ _)).trans (hJc Jc le_rfl)
  have hh' := (le_div_iff₀ hc).mp hh
  linarith

end TransposeFollowup.SL2Projection
