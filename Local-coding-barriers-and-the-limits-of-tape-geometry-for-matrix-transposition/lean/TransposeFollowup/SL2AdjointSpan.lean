import TransposeFollowup.SL2AdjointVolume
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! A bounded matrix frame with nonvanishing traces gives bounded linear
combinations of actual conjugations for every test commutator. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix MatrixFour
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

def matrixConjugationLinear (g : G) : RMat →ₗ[ℝ] RMat :=
  (LinearMap.mulRight ℝ ((g⁻¹ : G) : RMat)).comp
    (LinearMap.mulLeft ℝ (g : RMat))

theorem matrixConjugationLinear_apply (g : G) (b : RMat) :
    matrixConjugationLinear g b = (g : RMat) * b * ((g⁻¹ : G) : RMat) := rfl

theorem matrixConjugationLinear_mul (g h : G) (b : RMat) :
    matrixConjugationLinear g (matrixConjugationLinear h b) =
      matrixConjugationLinear (g * h) b := by
  simp only [matrixConjugationLinear_apply, _root_.mul_inv_rev,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

theorem exists_bounded_matrix_frame_coordinates (g : Fin 4 → G) (e : RMat) {M d : ℝ}
    (hM : 1 ≤ M) (hd : 0 < d) (hg : ∀ i j k, |g i j k| ≤ M)
    (hdet : d ≤ |(Matrix.of fun i j => matrixCoordinates (g j : RMat) i).det|)
    (he : ∀ i j, |e i j| ≤ 1) :
    ∃ c : Fin 4 → ℝ, (∀ i, |c i| ≤ 96 * M ^ 4 / d) ∧
      e = ∑ i, c i • (g i : RMat) := by
  let T : Matrix (Fin 4) (Fin 4) ℝ := fun i j => matrixCoordinates (g j : RMat) i
  have hne : T.det ≠ 0 := abs_pos.mp (hd.trans_le hdet)
  let c : Fin 4 → ℝ := T.det⁻¹ • T.cramer (matrixCoordinates e)
  have hc : T *ᵥ c = matrixCoordinates e := by
    simp only [c, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  have hT : ∀ i j, |T i j| ≤ M := by
    intro i j
    fin_cases i <;> exact hg j _ _
  have hv : ∀ i, |(T *ᵥ c) i| ≤ 1 := by
    rw [hc]
    intro i
    fin_cases i <;> exact he _ _
  have hn : ‖c‖ ≤ 96 * M ^ 4 / d := by
    simpa only [mul_one] using mulVec_inverse_bound hM hd hT hdet c zero_le_one hv
  refine ⟨c, fun i => ?_, ?_⟩
  · exact (show |c i| ≤ ‖c‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c i).trans hn
  · have hcoord (i : Fin 4) : matrixCoordinates (∑ j, c j • (g j : RMat)) i =
        matrixCoordinates e i := by
      rw [← hc]
      fin_cases i <;>
        simp [T, Matrix.mulVec, dotProduct, matrixCoordinates, Fin.sum_univ_succ] <;> ring
    ext i j
    fin_cases i <;> fin_cases j
    · exact (hcoord 0).symm
    · exact (hcoord 1).symm
    · exact (hcoord 2).symm
    · exact (hcoord 3).symm

theorem exists_bounded_adjoint_bracket_expansion (g : Fin 4 → G) (e : RMat)
    {M d τ : ℝ} (hM : 1 ≤ M) (hd : 0 < d) (hτ : 0 < τ)
    (hg : ∀ i j k, |g i j k| ≤ M)
    (hdet : d ≤ |(Matrix.of fun i j => matrixCoordinates (g j : RMat) i).det|)
    (htrace : ∀ i, τ ≤ |Matrix.trace (g i : RMat)|)
    (he : ∀ i j, |e i j| ≤ 1) :
    ∃ (v : Fin 4 × Bool → G) (a : Fin 4 × Bool → ℝ),
      (∀ i, v i = g i.1 ∨ v i = (g i.1)⁻¹) ∧
      (∀ i, |a i| ≤ 96 * M ^ 4 / (d * τ)) ∧
      ∀ b : RMat, e * b - b * e = ∑ i, a i • matrixConjugationLinear (v i) b := by
  obtain ⟨c, hc, heq⟩ := exists_bounded_matrix_frame_coordinates g e hM hd hg hdet he
  let r : Fin 4 → ℝ := fun i => c i / Matrix.trace (g i : RMat)
  let v : Fin 4 × Bool → G := fun i => if i.2 then (g i.1)⁻¹ else g i.1
  let a : Fin 4 × Bool → ℝ := fun i => if i.2 then -r i.1 else r i.1
  have ht (i : Fin 4) : Matrix.trace (g i : RMat) ≠ 0 :=
    abs_pos.mp (hτ.trans_le (htrace i))
  have hr (i : Fin 4) : |r i| ≤ 96 * M ^ 4 / (d * τ) := by
    dsimp only [r]
    rw [abs_div]
    calc
      _ ≤ (96 * M ^ 4 / d) / τ := div_le_div₀ (by positivity) (hc i) hτ (htrace i)
      _ = _ := by rw [div_div]
  refine ⟨v, a, ?_, ?_, ?_⟩
  · rintro ⟨i, s⟩
    cases s <;> simp [v]
  · rintro ⟨i, s⟩
    cases s <;> simpa [a] using hr i
  · intro b
    have hi (i : Fin 4) : r i • (matrixConjugationLinear (g i) b -
        matrixConjugationLinear ((g i)⁻¹) b) =
        c i • ((g i : RMat) * b - b * (g i : RMat)) := by
      simp only [matrixConjugationLinear_apply, inv_inv]
      rw [conjugation_sub_inverse_conjugation, smul_smul]
      simp only [r, div_mul_cancel₀ _ (ht i)]
    calc
      _ = ∑ i, c i • ((g i : RMat) * b - b * (g i : RMat)) := by
        rw [heq]
        simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
          smul_sub, Finset.sum_sub_distrib]
      _ = ∑ i, r i • (matrixConjugationLinear (g i) b -
          matrixConjugationLinear ((g i)⁻¹) b) := Finset.sum_congr rfl (fun i _ => (hi i).symm)
      _ = _ := by
        simp [v, a, Fintype.sum_prod_type, sub_eq_add_neg, add_comm]

end TransposeFollowup.SL2Projection
