import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-! Explicit four-coordinate inverse bounds and selection of a row to
replace by a prescribed normal vector. All constants are elementary. -/
namespace TransposeFollowup.MatrixFour
open Classical Matrix
set_option autoImplicit false

theorem abs_det_three_le {A : Matrix (Fin 3) (Fin 3) ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ i j, |A i j| ≤ M) : |A.det| ≤ 6 * M ^ 3 := by
  have ht (i j k l m n : Fin 3) : |A i j * A k l * A m n| ≤ M ^ 3 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ M * M * M := by gcongr <;> apply hA
      _ = _ := by ring
  rw [Matrix.det_fin_three]
  calc
    _ ≤ |A 0 0 * A 1 1 * A 2 2| + |A 0 0 * A 1 2 * A 2 1| +
        |A 0 1 * A 1 0 * A 2 2| + |A 0 1 * A 1 2 * A 2 0| +
        |A 0 2 * A 1 0 * A 2 1| + |A 0 2 * A 1 1 * A 2 0| := by
      have h₁ := norm_sub_le (A 0 0 * A 1 1 * A 2 2) (A 0 0 * A 1 2 * A 2 1)
      have h₂ := norm_sub_le (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1)
        (A 0 1 * A 1 0 * A 2 2)
      have h₃ := norm_add_le (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 -
        A 0 1 * A 1 0 * A 2 2) (A 0 1 * A 1 2 * A 2 0)
      have h₄ := norm_add_le (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 -
        A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0) (A 0 2 * A 1 0 * A 2 1)
      have h₅ := norm_sub_le (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 -
        A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1)
        (A 0 2 * A 1 1 * A 2 0)
      simp only [Real.norm_eq_abs] at h₁ h₂ h₃ h₄ h₅
      linarith
    _ ≤ M ^ 3 + M ^ 3 + M ^ 3 + M ^ 3 + M ^ 3 + M ^ 3 := by gcongr <;> apply ht
    _ = _ := by ring

theorem abs_det_four_le {A : Matrix (Fin 4) (Fin 4) ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ i j, |A i j| ≤ M) : |A.det| ≤ 24 * M ^ 4 := by
  rw [Matrix.det_succ_row_zero]
  calc
    _ ≤ ∑ j : Fin 4, |(-1 : ℝ) ^ (j : ℕ) * A 0 j * (A.submatrix Fin.succ j.succAbove).det| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, M * (6 * M ^ 3) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact mul_le_mul (hA 0 j)
        (abs_det_three_le hM (fun i k => hA _ _)) (abs_nonneg _) hM
    _ = _ := by simp; ring

theorem adjugate_entry_bound {A : Matrix (Fin 4) (Fin 4) ℝ} {M : ℝ}
    (hM : 1 ≤ M) (hA : ∀ i j, |A i j| ≤ M) :
    ∀ i j, |A.adjugate i j| ≤ 24 * M ^ 4 := by
  intro i j
  rw [Matrix.adjugate_apply]
  apply abs_det_four_le (by linarith)
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self, Pi.single_apply]
    split_ifs
    · simpa using hM
    · simpa using (show (0 : ℝ) ≤ M by linarith)
  · simpa only [Matrix.updateRow_ne hk] using hA k l

theorem mulVec_inverse_bound {A : Matrix (Fin 4) (Fin 4) ℝ} {M d Y : ℝ}
    (hM : 1 ≤ M) (hd : 0 < d) (hA : ∀ i j, |A i j| ≤ M)
    (hdet : d ≤ |A.det|) (v : Fin 4 → ℝ) (hY : 0 ≤ Y)
    (hv : ∀ i, |(A *ᵥ v) i| ≤ Y) : ‖v‖ ≤ 96 * M ^ 4 * Y / d := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs, le_div_iff₀ hd]
  have he : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hb := adjugate_entry_bound hM hA
  calc
    |v i| * d ≤ |A.det| * |v i| := by nlinarith [abs_nonneg (v i)]
    _ = |(A.adjugate *ᵥ (A *ᵥ v)) i| := by rw [he]; simp [abs_mul]
    _ ≤ ∑ j : Fin 4, |A.adjugate i j * (A *ᵥ v) j| := by
      change |∑ j : Fin 4, A.adjugate i j * (A *ᵥ v) j| ≤ _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, (24 * M ^ 4) * Y := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hb i j) (hv j) (abs_nonneg _) (by positivity)
    _ = _ := by simp; ring

theorem exists_normal_row {A : Matrix (Fin 4) (Fin 4) ℝ} {M d : ℝ}
    (hM : 0 < M) (hd : 0 < d) (hA : ∀ i j, |A i j| ≤ M)
    (hdet : d ≤ |A.det|) (v : Fin 4 → ℝ) (j : Fin 4) (hv : 1 / 2 ≤ |v j|) :
    ∃ i : Fin 4, d / (8 * M) ≤ |(A.updateRow i v).det| := by
  by_contra hn
  push Not at hn
  have he := congrFun (Matrix.mulVec_cramer Aᵀ v) j
  have hlow : d / 2 ≤ |A.det * v j| := by rw [abs_mul]; nlinarith
  have hhigh : |A.det * v j| < d / 2 := by
    calc
      _ = |∑ i : Fin 4, A i j * (Aᵀ.cramer v) i| := by
        simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.det_transpose,
          Pi.smul_apply, smul_eq_mul] using congrArg abs he.symm
      _ ≤ ∑ i : Fin 4, |A i j * (Aᵀ.cramer v) i| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _i : Fin 4, M * (d / (8 * M)) := by
        apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
        intro i _
        rw [abs_mul, Matrix.cramer_transpose_apply]
        exact (mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _)).trans_lt
          (mul_lt_mul_of_pos_left (hn i) hM)
      _ = d / 2 := by simp; field_simp; ring
  exact (not_lt_of_ge hlow) hhigh

end TransposeFollowup.MatrixFour
