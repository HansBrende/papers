import TransposeFollowup.ScalarDyadicBudgets

/-! A simultaneous exponent certificate for the two-stage trace-square
ledger. This proves the numerical margins, not the matrix-to-power
estimates that must supply their inputs. The scalar growth part reuses
the same margin proof as the nilpotent application. -/
namespace TransposeFollowup.SL2Projection
set_option autoImplicit false

/-- `Θ` pays concentration and reextraction; `θ` is the smaller original
frame exponent; `a` is the far-cutoff exponent. Keeping them distinct
allows fine trimming before the final scalar spacing is imposed. -/
theorem trace_square_two_stage_exponent_margins {κ₀ e : ℝ}
    (hκ₀ : 0 < κ₀) (hκ₀one : κ₀ ≤ 1) (he : 0 < e) (heone : e ≤ 1) :
    let Θ := min e κ₀ / 16384
    let θ := κ₀ * Θ / 1024
    let a := 5 * Θ / 16
    let gain := e / 32
    let d := 1 - 3 * Θ
    let κ := κ₀ / 12
    let g := e / 8
    let c := 100 * Θ
    let u := 1 - κ₀ / 3 + 84 * Θ
    let τ := 1 - 2 * Θ
    0 < Θ ∧ Θ < 1/4 ∧ 0 < θ ∧ θ ≤ Θ ∧ 0 < a ∧
      κ₀*a = 320*θ ∧ 289*θ < κ₀*a ∧ 278*θ < κ₀ ∧
      11*θ ≤ 8*Θ ∧ 12*Θ + 88*θ + 4*a ≤ 36*Θ ∧
      θ+a ≤ 3*Θ ∧ 12*θ+a ≤ 3*Θ ∧
      14*θ+a < 1 ∧ 3*Θ+13*θ+a < 1 ∧
      0 < gain ∧ 2*gain < g ∧ 691*Θ < 3*gain ∧
      0 < d ∧ d ≤ 1 ∧ 0 < κ ∧ κ ≤ 1 ∧
      0 ≤ g ∧ 0 ≤ c ∧ 4*g < d*e ∧ g+c < d*e ∧
      u < d*(1-κ) ∧ d < τ ∧
      289*Θ/3 < c ∧ 83*Θ < 84*Θ ∧ 173*Θ < g := by
  intro Θ θ a gain d κ g c u τ
  have hΘ : 0 < Θ := by dsimp only [Θ]; positivity
  have hΘe : Θ ≤ e/16384 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hΘκ : Θ ≤ κ₀/16384 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hΘone : Θ ≤ 1/16384 := hΘe.trans
    (div_le_div_of_nonneg_right heone (by norm_num))
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθΘ : θ ≤ Θ/1024 := by
    dsimp only [θ]
    exact div_le_div_of_nonneg_right
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hκ₀one hΘ.le)
      (by norm_num)
  have hθκ : θ ≤ κ₀/1024 := by
    dsimp only [θ]
    exact div_le_div_of_nonneg_right
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (show Θ ≤ 1 by linarith only [hΘone]) hκ₀.le)
      (by norm_num)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hproduct : κ₀*a = 320*θ := by dsimp only [a, θ]; ring
  have hmargins := scalar_exponent_margins_of_bounds hκ₀ hκ₀one he heone hΘ
    (by linarith only [hΘe, he] : Θ ≤ e/4096)
    (by linarith only [hΘκ, hκ₀] : Θ ≤ κ₀/4096)
  refine ⟨hΘ, ?_, hθ, ?_, ha, hproduct, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hmargins⟩
  · linarith only [hΘone]
  · linarith only [hθΘ, hΘ]
  · rw [hproduct]
    linarith only [hθ]
  · linarith only [hθκ, hκ₀]
  · linarith only [hθΘ, hΘ]
  · dsimp only [a]
    linarith only [hθΘ, hΘ]
  · dsimp only [a]
    linarith only [hθΘ, hΘ]
  · dsimp only [a]
    linarith only [hθΘ, hΘ]
  · dsimp only [a]
    linarith only [hθΘ, hΘone]
  · dsimp only [a]
    linarith only [hθΘ, hΘone]
  · dsimp only [gain]; positivity
  · dsimp only [gain, g]
    linarith only [he]
  · dsimp only [gain]
    linarith only [hΘe, he]

end TransposeFollowup.SL2Projection
