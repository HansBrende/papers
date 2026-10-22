import TransposeFollowup.SL2OffDiagonalBounds

/-! Nearby exact triangular determinant-one matrices, with every entry
and approximation constant explicit. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
set_option autoImplicit false
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℂ

theorem exists_upper_approximation {g : G} {M ε : ℝ}
    (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (ha : ‖g 0 0‖ ≤ M) (hd : ‖g 1 1‖ ≤ M)
    (halo : 1 / (2 * M) ≤ ‖g 0 0‖) (hb : ‖g 0 1‖ ≤ 1)
    (hc : ‖g 1 0‖ ≤ 16 * M ^ 4 * ε) (hbc : ‖g 0 1 * g 1 0‖ ≤ ε)
    (hsmall : 16 * M ^ 4 * ε ≤ 1) :
    ∃ h : G, h 1 0 = 0 ∧ (∀ i j, ‖g i j‖ ≤ 2 * M) ∧
      (∀ i j, ‖h i j‖ ≤ 2 * M) ∧ (∀ i j, ‖g i j - h i j‖ ≤ 16 * M ^ 4 * ε) := by
  have hM0 : 0 ≤ M := by linarith
  have hpos : 0 < ‖g 0 0‖ := lt_of_lt_of_le (by positivity) halo
  have hne : g 0 0 ≠ 0 := norm_pos_iff.mp hpos
  have hinv : ‖(g 0 0)⁻¹‖ ≤ 2 * M := by
    rw [norm_inv]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hpos).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * M)).mp halo
    nlinarith
  let h : G := ⟨!![g 0 0, g 0 1; 0, (g 0 0)⁻¹], by simp [Matrix.det_fin_two, hne]⟩
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have he : g 1 1 - (g 0 0)⁻¹ = (g 0 1 * g 1 0) * (g 0 0)⁻¹ := by
    field_simp
    linear_combination hdet
  have hcoef : 2 * M ≤ 16 * M ^ 4 := by
    have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hM),
      mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hM2)]
  have hdiff : ‖g 1 1 - (g 0 0)⁻¹‖ ≤ 16 * M ^ 4 * ε := by
    rw [he, norm_mul]
    calc
      _ ≤ ε * (2 * M) := by gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcoef hε]
  have hδ : 0 ≤ 16 * M ^ 4 * ε := by positivity
  refine ⟨h, rfl, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · change ‖g 0 0‖ ≤ _; linarith
    · change ‖g 0 1‖ ≤ _; linarith
    · change ‖g 1 0‖ ≤ _; linarith
    · change ‖g 1 1‖ ≤ _; linarith
  · intro i j
    fin_cases i <;> fin_cases j
    · change ‖g 0 0‖ ≤ _; linarith
    · change ‖g 0 1‖ ≤ _; linarith
    · change ‖(0 : ℂ)‖ ≤ _; simpa only [norm_zero] using (by linarith : 0 ≤ 2 * M)
    · exact hinv
  · intro i j
    fin_cases i <;> fin_cases j
    · change ‖g 0 0 - g 0 0‖ ≤ _; simpa only [sub_self, norm_zero] using hδ
    · change ‖g 0 1 - g 0 1‖ ≤ _; simpa only [sub_self, norm_zero] using hδ
    · change ‖g 1 0 - 0‖ ≤ _; simpa only [sub_zero] using hc
    · exact hdiff

end TransposeFollowup.SL2Escape
