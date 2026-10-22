import TransposeFollowup.SL2SpanCertificate
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Quantitative projection to the two-dimensional commuting algebra
spanned by a nonscalar real two-by-two matrix and the identity. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ

def scalarAffine (g : RMat) (s t : ℝ) : RMat :=
  !![s + t * g 0 0, t * g 0 1; t * g 1 0, s + t * g 1 1]

def noncentralCoordinates (g : RMat) : Fin 3 → ℝ := ![g 0 0 - g 1 1, g 0 1, g 1 0]

theorem scalarAffine_commute (g : RMat) (s t u v : ℝ) :
    scalarAffine g s t * scalarAffine g u v = scalarAffine g u v * scalarAffine g s t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarAffine, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem smul_scalarAffine (g : RMat) (s t r : ℝ) :
    r • scalarAffine g s t = scalarAffine g (r * s) (r * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarAffine] <;> ring

theorem exists_scalar_multiple_approx {u v : Fin 3 → ℝ} {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 ≤ ε) (hpivot : ∃ i, ρ ≤ |v i|)
    (hcross : ∀ i j, |v i * u j - v j * u i| ≤ ε) :
    ∃ t : ℝ, ∀ i, |u i - t * v i| ≤ ε / ρ := by
  obtain ⟨k, hk⟩ := hpivot
  have hv : 0 < |v k| := hρ.trans_le hk
  have hne : v k ≠ 0 := abs_pos.mp hv
  refine ⟨u k / v k, ?_⟩
  intro i
  calc
    _ = |v k * u i - v i * u k| / |v k| := by
      rw [← abs_div]
      congr 1
      field_simp
    _ ≤ ε / |v k| := div_le_div_of_nonneg_right (hcross k i) hv.le
    _ ≤ ε / ρ := div_le_div_of_nonneg_left hε hρ hk

theorem noncentral_cross_bound (g x : RMat) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ i j, |(g * x - x * g) i j| ≤ ε) :
    ∀ i j, |noncentralCoordinates g i * noncentralCoordinates x j -
      noncentralCoordinates g j * noncentralCoordinates x i| ≤ ε := by
  have h01 : |(g 0 0 - g 1 1) * x 0 1 - g 0 1 * (x 0 0 - x 1 1)| ≤ ε := by
    convert hc 0 1 using 1
    congr 1
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h10 : |(g 0 0 - g 1 1) * x 1 0 - g 1 0 * (x 0 0 - x 1 1)| ≤ ε := by
    have hh : |-(g * x - x * g) 1 0| ≤ ε := by simpa only [abs_neg] using hc 1 0
    convert hh using 1
    congr 1
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h00 : |g 0 1 * x 1 0 - g 1 0 * x 0 1| ≤ ε := by
    convert hc 0 0 using 1
    congr 1
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [noncentralCoordinates] using hε
  · exact h01
  · exact h10
  · change |g 0 1 * (x 0 0 - x 1 1) - (g 0 0 - g 1 1) * x 0 1| ≤ ε
    rw [abs_sub_comm]
    exact h01
  · simpa [noncentralCoordinates] using hε
  · exact h00
  · change |g 1 0 * (x 0 0 - x 1 1) - (g 0 0 - g 1 1) * x 1 0| ≤ ε
    rw [abs_sub_comm]
    exact h10
  · change |g 1 0 * x 0 1 - g 0 1 * x 1 0| ≤ ε
    rw [abs_sub_comm]
    exact h00
  · simpa [noncentralCoordinates] using hε

theorem exists_scalarAffine_approx (g x : RMat) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 ≤ ε) (hpivot : ∃ i, ρ ≤ |noncentralCoordinates g i|)
    (hc : ∀ i j, |(g * x - x * g) i j| ≤ ε) :
    ∃ s t : ℝ, ∀ i j, |x i j - scalarAffine g s t i j| ≤ ε / ρ := by
  obtain ⟨t, ht⟩ := exists_scalar_multiple_approx hρ hε hpivot (noncentral_cross_bound g x hε hc)
  let s := (x 0 0 + x 1 1 - t * (g 0 0 + g 1 1)) / 2
  have hδ : 0 ≤ ε / ρ := div_nonneg hε hρ.le
  have hdiag : |((x 0 0 - x 1 1) - t * (g 0 0 - g 1 1)) / 2| ≤ ε / ρ := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh := ht 0
    change |(x 0 0 - x 1 1) - t * (g 0 0 - g 1 1)| ≤ ε / ρ at hh
    linarith
  refine ⟨s, t, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · convert hdiag using 1
    congr 1
    dsimp [s, scalarAffine]
    ring
  · exact ht 1
  · exact ht 2
  · have hh : |-(((x 0 0 - x 1 1) - t * (g 0 0 - g 1 1)) / 2)| ≤ ε / ρ := by
      simpa only [abs_neg] using hdiag
    convert hh using 1
    congr 1
    dsimp [s, scalarAffine]
    ring

end TransposeFollowup.SL2Projection
