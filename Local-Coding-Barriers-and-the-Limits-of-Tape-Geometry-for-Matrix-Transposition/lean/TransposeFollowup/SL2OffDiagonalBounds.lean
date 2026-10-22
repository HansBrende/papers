import TransposeFollowup.SL2TriangularBicommutator
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Explicit diagonal and normalized lower-entry estimates from small
individual and two-factor off-diagonal products in complex SL2. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
set_option autoImplicit false
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℂ
local notation "M" => Matrix (Fin 2) (Fin 2) ℂ

theorem complex_norm_le_of_sum_mul {a d : ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hs : ‖a + d‖ ≤ T) (hp : ‖a * d‖ ≤ 2) : ‖a‖ ≤ T + 2 := by
  have hh : ‖a‖ ^ 2 ≤ ‖a‖ * T + 2 := by
    calc
      _ = ‖a * a‖ := by rw [norm_mul]; ring
      _ = ‖a * (a + d) - a * d‖ := by congr 1; ring
      _ ≤ ‖a * (a + d)‖ + ‖a * d‖ := norm_sub_le _ _
      _ ≤ ‖a‖ * T + 2 := by rw [norm_mul]; gcongr
  by_contra hn
  push Not at hn
  have hn' : 0 ≤ ‖a‖ - (T + 2) := by linarith
  nlinarith [mul_nonneg hn' (norm_nonneg a)]

theorem diagonal_bounds_of_trace_offDiagonal {g : G} {T ε : ℝ}
    (hT : 0 ≤ T) (htr : ‖Matrix.trace (g : M)‖ ≤ T)
    (hε : ε ≤ 1 / 2) (hbc : ‖g 0 1 * g 1 0‖ ≤ ε) :
    ‖g 0 0‖ ≤ T + 2 ∧ ‖g 1 1‖ ≤ T + 2 ∧
      1 / (2 * (T + 2)) ≤ ‖g 0 0‖ ∧ 1 / (2 * (T + 2)) ≤ ‖g 1 1‖ := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hsum : ‖g 0 0 + g 1 1‖ ≤ T := by
    simpa only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using htr
  have hp : ‖g 0 0 * g 1 1‖ ≤ 2 := by
    have he : g 0 0 * g 1 1 = 1 + g 0 1 * g 1 0 := by linear_combination hdet
    rw [he]
    have hh := norm_add_le (1 : ℂ) (g 0 1 * g 1 0)
    norm_num only [norm_one] at hh
    linarith
  have ha := complex_norm_le_of_sum_mul hT hsum hp
  have hd := complex_norm_le_of_sum_mul (a := g 1 1) (d := g 0 0) hT (by simpa only [add_comm] using hsum)
    (by simpa only [mul_comm] using hp)
  have hlow : 1 / 2 ≤ ‖g 0 0‖ * ‖g 1 1‖ := by
    have hh := norm_sub_le (g 0 0 * g 1 1) (g 0 1 * g 1 0)
    rw [hdet, norm_one, norm_mul] at hh
    linarith
  have hpos : 0 < 2 * (T + 2) := by positivity
  refine ⟨ha, hd, (div_le_iff₀ hpos).mpr ?_, (div_le_iff₀ hpos).mpr ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg (g 0 0))]
  · nlinarith [mul_le_mul_of_nonneg_right ha (norm_nonneg (g 1 1))]

theorem normalized_lower_entry_bound {u x : G} {M₀ ε : ℝ}
    (hM : 1 ≤ M₀) (hε : 0 ≤ ε)
    (hu00 : ‖u 0 0‖ ≤ M₀) (hu11 : ‖u 1 1‖ ≤ M₀)
    (hx00 : ‖x 0 0‖ ≤ M₀) (hx11 : ‖x 1 1‖ ≤ M₀)
    (hulo : 1 / (2 * M₀) ≤ ‖u 1 1‖) (hxlo : 1 / (2 * M₀) ≤ ‖x 1 1‖)
    (hu01 : ‖u 0 1‖ = 1) (hx01 : ‖x 0 1‖ ≤ 1)
    (hu : ‖u 0 1 * u 1 0‖ ≤ ε) (hx : ‖x 0 1 * x 1 0‖ ≤ ε)
    (hux : ‖(u * x) 0 1 * (u * x) 1 0‖ ≤ ε) : ‖x 1 0‖ ≤ 16 * M₀ ^ 4 * ε := by
  have hM0 : 0 ≤ M₀ := by linarith
  have hMpos : 0 < 2 * M₀ := by linarith
  have huc : ‖u 1 0‖ ≤ ε := by simpa only [norm_mul, hu01, one_mul] using hu
  have hid : u 0 1 * x 1 1 * u 1 1 * x 1 0 =
      (u * x) 0 1 * (u * x) 1 0 - u 0 0 * x 0 1 * u 1 0 * x 0 0 -
        u 0 1 * x 1 1 * u 1 0 * x 0 0 - u 0 0 * x 0 1 * u 1 1 * x 1 0 := by
    change _ = ((u : M) * (x : M)) 0 1 * ((u : M) * (x : M)) 1 0 - _ - _ - _
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have ht₁ : ‖u 0 0 * x 0 1 * u 1 0 * x 0 0‖ ≤ M₀ ^ 2 * ε := by
    calc
      _ = ‖u 0 0‖ * ‖x 0 1‖ * ‖u 1 0‖ * ‖x 0 0‖ := by simp only [norm_mul]
      _ ≤ M₀ * 1 * ε * M₀ := by gcongr
      _ = _ := by ring
  have ht₂ : ‖u 0 1 * x 1 1 * u 1 0 * x 0 0‖ ≤ M₀ ^ 2 * ε := by
    calc
      _ = 1 * ‖x 1 1‖ * ‖u 1 0‖ * ‖x 0 0‖ := by simp only [norm_mul, hu01]
      _ ≤ 1 * M₀ * ε * M₀ := by gcongr
      _ = _ := by ring
  have ht₃ : ‖u 0 0 * x 0 1 * u 1 1 * x 1 0‖ ≤ M₀ ^ 2 * ε := by
    calc
      _ = ‖u 0 0‖ * ‖u 1 1‖ * ‖x 0 1 * x 1 0‖ := by simp only [norm_mul]; ring
      _ ≤ M₀ * M₀ * ε := by gcongr
      _ = _ := by ring
  have hmain : ‖x 1 1‖ * ‖u 1 1‖ * ‖x 1 0‖ ≤ (1 + 3 * M₀ ^ 2) * ε := by
    have h₁ := norm_sub_le ((u * x) 0 1 * (u * x) 1 0) (u 0 0 * x 0 1 * u 1 0 * x 0 0)
    have h₂ := norm_sub_le ((u * x) 0 1 * (u * x) 1 0 - u 0 0 * x 0 1 * u 1 0 * x 0 0)
      (u 0 1 * x 1 1 * u 1 0 * x 0 0)
    have h₃ := norm_sub_le ((u * x) 0 1 * (u * x) 1 0 - u 0 0 * x 0 1 * u 1 0 * x 0 0 -
      u 0 1 * x 1 1 * u 1 0 * x 0 0) (u 0 0 * x 0 1 * u 1 1 * x 1 0)
    rw [← hid] at h₃
    simp only [norm_mul, hu01, one_mul] at h₃
    simp only [norm_mul] at ht₃
    nlinarith
  have hdu : 1 ≤ ‖u 1 1‖ * (2 * M₀) := (div_le_iff₀ hMpos).mp hulo
  have hdx : 1 ≤ ‖x 1 1‖ * (2 * M₀) := (div_le_iff₀ hMpos).mp hxlo
  have hp : 1 ≤ 4 * M₀ ^ 2 * (‖x 1 1‖ * ‖u 1 1‖) := by
    have hh := mul_le_mul hdx hdu (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    nlinarith [hh]
  have hcoef : 4 * M₀ ^ 2 * (1 + 3 * M₀ ^ 2) ≤ 16 * M₀ ^ 4 := by
    have hM2 : 1 ≤ M₀ ^ 2 := one_le_pow₀ hM
    nlinarith [mul_nonneg (sq_nonneg M₀) (sub_nonneg.mpr hM2)]
  calc
    _ ≤ (4 * M₀ ^ 2 * (‖x 1 1‖ * ‖u 1 1‖)) * ‖x 1 0‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (x 1 0))
    _ = 4 * M₀ ^ 2 * (‖x 1 1‖ * ‖u 1 1‖ * ‖x 1 0‖) := by ring
    _ ≤ 4 * M₀ ^ 2 * ((1 + 3 * M₀ ^ 2) * ε) := by gcongr
    _ ≤ 16 * M₀ ^ 4 * ε := by nlinarith [mul_le_mul_of_nonneg_right hcoef hε]

end TransposeFollowup.SL2Escape
