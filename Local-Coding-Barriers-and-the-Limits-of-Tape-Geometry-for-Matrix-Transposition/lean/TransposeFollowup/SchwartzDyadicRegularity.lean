import TransposeFollowup.ConcreteDyadicTransport

/-! Homogeneous regularity cost on arbitrary Schwartz functions, with
individual moment and derivative energy bounds at a dyadic scale. -/
namespace TransposeFollowup
open Classical MeasureTheory SchwartzMap
set_option autoImplicit false

theorem schwartz_toLp_real_smul (a : ℝ) (u : 𝓢(ℝ, ℂ)) :
    (a • u).toLp 2 volume = a • u.toLp 2 volume :=
  map_smul (SchwartzMap.toLpCLM ℝ ℂ 2 volume) a u

theorem schwartz_even_moment_real_smul (a : ℝ) (u : 𝓢(ℝ, ℂ)) (n : ℕ) :
    (∫ x, x ^ (2 * n) * ‖(a • u) x‖ ^ 2) = a ^ 2 * ∫ x, x ^ (2 * n) * ‖u x‖ ^ 2 := by
  simp only [smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem schwartz_deriv_even_moment_real_smul (a : ℝ) (u : 𝓢(ℝ, ℂ)) (n : ℕ) :
    (∫ x, x ^ (2 * n) * ‖deriv (a • u) x‖ ^ 2) = a ^ 2 * ∫ x, x ^ (2 * n) * ‖deriv u x‖ ^ 2 := by
  change (∫ x, x ^ (2 * n) * ‖(SchwartzMap.derivCLM ℝ ℂ (a • u)) x‖ ^ 2) = _
  rw [map_smul]
  exact schwartz_even_moment_real_smul a (SchwartzMap.derivCLM ℝ ℂ u) n

noncomputable def schwartzDyadicRegularityCost (j : ℕ) (u : 𝓢(ℝ, ℂ)) : ℝ :=
  ‖u.toLp 2 volume‖ ^ 2 + (∫ x, x ^ 2 * ‖u x‖ ^ 2) +
    dyadicBandWeight j * ((∫ x, ‖deriv u x‖ ^ 2) + (∫ x, x ^ 4 * ‖deriv u x‖ ^ 2))

theorem schwartzDyadicRegularityCost_nonneg (j : ℕ) (u : 𝓢(ℝ, ℂ)) :
    0 ≤ schwartzDyadicRegularityCost j u := by
  unfold schwartzDyadicRegularityCost
  exact add_nonneg (add_nonneg (sq_nonneg _) (integral_nonneg (fun x => by positivity)))
    (mul_nonneg (dyadicBandWeight_nonneg j)
      (add_nonneg (integral_nonneg (fun x => sq_nonneg _)) (integral_nonneg (fun x => by positivity))))

theorem schwartzDyadicRegularityCost_real_smul (a : ℝ) (j : ℕ) (u : 𝓢(ℝ, ℂ)) :
    schwartzDyadicRegularityCost j (a • u) = a ^ 2 * schwartzDyadicRegularityCost j u := by
  have hm := schwartz_even_moment_real_smul a u 1
  have hd := schwartz_deriv_even_moment_real_smul a u 0
  have hdm := schwartz_deriv_even_moment_real_smul a u 2
  simp only [Nat.mul_zero, pow_zero, one_mul] at hd
  simp only [Nat.mul_one] at hm
  simp only [show 2 * 2 = 4 from rfl] at hdm
  unfold schwartzDyadicRegularityCost
  rw [schwartz_toLp_real_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hm, hd, hdm]
  ring

theorem schwartzDyadicRegularityCost_components_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) :
    ‖u.toLp 2 volume‖ ^ 2 ≤ schwartzDyadicRegularityCost j u ∧
    (∫ x, x ^ 2 * ‖u x‖ ^ 2) ≤ schwartzDyadicRegularityCost j u ∧
    dyadicBandWeight j * ((∫ x, ‖deriv u x‖ ^ 2) + (∫ x, x ^ 4 * ‖deriv u x‖ ^ 2)) ≤
      schwartzDyadicRegularityCost j u := by
  have hm : 0 ≤ ∫ x, x ^ 2 * ‖u x‖ ^ 2 := integral_nonneg (fun x => by positivity)
  have hd : 0 ≤ ∫ x, ‖deriv u x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have hdm : 0 ≤ ∫ x, x ^ 4 * ‖deriv u x‖ ^ 2 := integral_nonneg (fun x => by positivity)
  have hw := mul_nonneg (dyadicBandWeight_nonneg j) (add_nonneg hd hdm)
  unfold schwartzDyadicRegularityCost
  exact ⟨by linarith, by linarith [sq_nonneg ‖u.toLp 2 volume‖],
    by linarith [sq_nonneg ‖u.toLp 2 volume‖]⟩

theorem schwartzDyadicRegularityCost_deriv_energy_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) :
    ((∫ x, ‖deriv u x‖ ^ 2) + (∫ x, x ^ 4 * ‖deriv u x‖ ^ 2)) ≤
      ((2 : ℝ) ^ j) ^ 2 * schwartzDyadicRegularityCost j u := by
  have h := mul_le_mul_of_nonneg_left (schwartzDyadicRegularityCost_components_le j u).2.2
    (sq_nonneg ((2 : ℝ) ^ j))
  simpa only [dyadicBandWeight, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ j ≠ 0), one_pow, one_mul] using h

theorem schwartz_deriv_first_moment_energy_le (u : 𝓢(ℝ, ℂ)) :
    (∫ x, x ^ 2 * ‖deriv u x‖ ^ 2) ≤
      (∫ x, ‖deriv u x‖ ^ 2) + (∫ x, x ^ 4 * ‖deriv u x‖ ^ 2) := by
  have hi0 := schwartz_integrable_norm_sq (SchwartzMap.derivCLM ℝ ℂ u)
  change Integrable (fun x => ‖deriv u x‖ ^ 2) at hi0
  have hi1 := schwartz_integrable_deriv_even_moment u 1
  have hi2 := schwartz_integrable_deriv_even_moment u 2
  simp only [Nat.mul_one] at hi1
  simp only [show 2 * 2 = 4 from rfl] at hi2
  rw [← integral_add hi0 hi2]
  apply integral_mono hi1 (hi0.add hi2)
  intro x
  have h : x ^ 2 ≤ 1 + x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 1)]
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg ‖deriv u x‖)
  simpa only [Pi.add_apply, add_mul, one_mul] using hmul

end TransposeFollowup
