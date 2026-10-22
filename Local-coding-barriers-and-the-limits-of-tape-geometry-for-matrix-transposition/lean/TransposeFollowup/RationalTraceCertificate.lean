import TransposeFollowup.RationalBicommutator
import TransposeFollowup.SL2TraceCertificate
import Mathlib.Analysis.Complex.Basic

/-! A rational bicommutator has a quantitative trace certificate. The
same witness works after every invertible complex change of basis. -/
namespace TransposeFollowup.RationalFreePair
open Classical Matrix
open scoped commutatorElement
set_option autoImplicit false

local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "CMat" => Matrix (Fin 2) (Fin 2) ℂ

theorem denominatorCarrier_trace_integer {D : ℕ} {g : RealMobius.Group}
    (hg : g ∈ denominatorCarrier D) :
    ∃ z : ℤ, (D : ℝ) * Matrix.trace (g : RMat) = z := by
  obtain ⟨g, hg, rfl⟩ := hg
  obtain ⟨z₀, h₀⟩ := hg 0 0
  obtain ⟨z₁, h₁⟩ := hg 1 1
  have h : (D : ℚ) * (g 0 0 + g 1 1) = ((z₀ + z₁ : ℤ) : ℚ) := by
    rw [mul_add, h₀, h₁, Int.cast_add]
  refine ⟨z₀ + z₁, ?_⟩
  have hh := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at hh
  simpa only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, realEmbedding_entry, Int.cast_add] using hh

theorem denominatorCarrier_trace_separated {D : ℕ} (hD : 0 < D)
    {g h : RealMobius.Group} (hg : g ∈ denominatorCarrier D) (hh : h ∈ denominatorCarrier D)
    (hne : Matrix.trace (g : RMat) ≠ Matrix.trace (h : RMat)) :
    1 / (D : ℝ) ≤ |Matrix.trace (g : RMat) - Matrix.trace (h : RMat)| := by
  obtain ⟨z, hz⟩ := denominatorCarrier_trace_integer hg
  obtain ⟨w, hw⟩ := denominatorCarrier_trace_integer hh
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hzw : z - w ≠ 0 := by
    intro he
    have he' : (z : ℝ) = w := by exact_mod_cast (sub_eq_zero.mp he)
    exact hne (mul_left_cancel₀ hd.ne' (hz.trans (he'.trans hw.symm)))
  have hzwi : (1 : ℤ) ≤ |z - w| := by have := abs_pos.mpr hzw; omega
  have hdiff : (D : ℝ) * (Matrix.trace (g : RMat) - Matrix.trace (h : RMat)) =
      ((z - w : ℤ) : ℝ) := by rw [mul_sub, hz, hw, Int.cast_sub]
  have habs := congrArg abs hdiff
  rw [abs_mul, abs_of_pos hd] at habs
  have hlow : (1 : ℝ) ≤ |((z - w : ℤ) : ℝ)| := by exact_mod_cast hzwi
  rw [← habs] at hlow
  exact (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using hlow)

theorem real_trace_difference_units_conj (P : CMatˣ) (b g : RMat) :
    ‖Matrix.trace ((P : CMat) * (b * g).map Complex.ofReal * (↑P⁻¹ : CMat)) -
      Matrix.trace ((P : CMat) * g.map Complex.ofReal * (↑P⁻¹ : CMat))‖ =
      |Matrix.trace (b * g) - Matrix.trace g| := by
  rw [Matrix.trace_units_conj, Matrix.trace_units_conj]
  have ht (m : RMat) : Matrix.trace (m.map Complex.ofReal) = Complex.ofReal (Matrix.trace m) := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  rw [ht, ht]
  change ‖Complex.ofReal (Matrix.trace (b * g)) - Complex.ofReal (Matrix.trace g)‖ = _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem rational_bicommutator_trace_certificate {D : ℕ} (hD : 0 < D)
    {a x y : RealMobius.Group} (ha : a ∈ denominatorCarrier D)
    (hx : x ∈ denominatorCarrier D) (hy : y ∈ denominatorCarrier D)
    (hne : ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1) :
    let B := ⁅⁅a, x⁆, ⁅a, y⁆⁆
    ∃ g : RealMobius.Group, (g = 1 ∨ g = a ∨ g = x ∨ g = y) ∧
      1 / (D : ℝ) ^ 17 ≤ |Matrix.trace ((B * g : RealMobius.Group) : RMat) -
        Matrix.trace (g : RMat)| ∧
      ∀ P : CMatˣ, 1 / (D : ℝ) ^ 17 ≤
        ‖Matrix.trace ((P : CMat) * ((B * g : RealMobius.Group) : RMat).map Complex.ofReal *
            (↑P⁻¹ : CMat)) -
          Matrix.trace ((P : CMat) * (g : RMat).map Complex.ofReal * (↑P⁻¹ : CMat))‖ := by
  dsimp only
  obtain ⟨g, hg, hneT⟩ := SL2Escape.bicommutator_trace_certificate a x y hne
  have hgD : g ∈ denominatorCarrier D := by
    rcases hg with rfl | rfl | rfl | rfl
    · exact denominatorCarrier_one D
    · exact ha
    · exact hx
    · exact hy
  have hBD := (rational_bicommutator_separated hD ha hx hy hne).1
  have hBgD : ⁅⁅a, x⁆, ⁅a, y⁆⁆ * g ∈ denominatorCarrier (D ^ 17) := by
    simpa only [show D ^ 16 * D = D ^ 17 by ring] using denominatorCarrier_mul hBD hgD
  have hgD' : g ∈ denominatorCarrier (D ^ 17) := by
    have hh := denominatorCarrier_mul (denominatorCarrier_one (D ^ 16)) hgD
    rw [show D ^ 16 * D = D ^ 17 by ring] at hh
    simpa only [one_mul] using hh
  have hsep : 1 / (D : ℝ) ^ 17 ≤
      |Matrix.trace ((⁅⁅a, x⁆, ⁅a, y⁆⁆ * g : RealMobius.Group) : RMat) - Matrix.trace (g : RMat)| := by
    simpa only [Nat.cast_pow] using denominatorCarrier_trace_separated (pow_pos hD 17) hBgD hgD' hneT
  refine ⟨g, hg, hsep, ?_⟩
  intro P
  simpa only [Matrix.SpecialLinearGroup.coe_mul, real_trace_difference_units_conj] using hsep

end TransposeFollowup.RationalFreePair
