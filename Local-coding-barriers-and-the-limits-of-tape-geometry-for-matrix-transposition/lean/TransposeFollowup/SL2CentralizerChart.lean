import TransposeFollowup.SL2CentralizerTrace
import TransposeFollowup.SL2ConjugacyFiber

/-! Quantitative real coordinates on the positive-trace branch of a
determinant-one centralizer. No inverse discriminant is used. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem scalarAffine_eq_smul_add (b : RMat) (c t : ℝ) :
    scalarAffine b c t = c • (1 : RMat) + t • b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarAffine]

theorem scalarAffine_trace (b : RMat) (c t : ℝ) :
    Matrix.trace (scalarAffine b c t) = 2 * c + t * Matrix.trace b := by
  simp only [scalarAffine, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem sl2_centered_coordinate_equation (b : RMat) (u : G) {c t : ℝ}
    (hb : Matrix.trace b = 0) (hu : (u : RMat) = scalarAffine b c t) :
    c ^ 2 + b.det * t ^ 2 = 1 := by
  have he := scalarAffine_discriminant b c t
  have hd : (scalarAffine b c t).det = 1 := hu ▸ u.property
  rw [scalarAffine_trace, hb, hd] at he
  nlinarith only [he]

theorem centered_scalar_constant_bounds {c p t q d D r : ℝ}
    (hD : 0 ≤ D) (hr : 0 ≤ r) (hd : |d| ≤ D)
    (hc : 1 / 2 ≤ c) (hp : 1 / 2 ≤ p)
    (ht : |t| ≤ r) (hq : |q| ≤ r)
    (hec : c ^ 2 + d * t ^ 2 = 1) (hep : p ^ 2 + d * q ^ 2 = 1) :
    |c - 1| ≤ D * r ^ 2 ∧ |c - p| ≤ 2 * D * r * |t - q| := by
  have hsq : t ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr ht
  have hc1 : 1 ≤ |c + 1| := by rw [abs_of_pos (by linarith)]; linarith
  have hcp : 1 ≤ |c + p| := by rw [abs_of_pos (by linarith)]; linarith
  constructor
  · calc
      |c - 1| ≤ |c - 1| * |c + 1| := le_mul_of_one_le_right (abs_nonneg _) hc1
      _ = |d| * t ^ 2 := by
        rw [← abs_mul, show (c - 1) * (c + 1) = -(d * t ^ 2) by nlinarith only [hec],
          abs_neg, abs_mul, abs_sq]
      _ ≤ D * r ^ 2 := mul_le_mul hd hsq (sq_nonneg _) hD
  · have hsum : |t + q| ≤ 2 * r := (abs_add_le t q).trans (by linarith)
    calc
      |c - p| ≤ |c - p| * |c + p| := le_mul_of_one_le_right (abs_nonneg _) hcp
      _ = |d| * |t - q| * |t + q| := by
        rw [← abs_mul, show (c - p) * (c + p) = -(d * (t - q) * (t + q)) by
          nlinarith only [hec, hep], abs_neg, abs_mul, abs_mul]
      _ ≤ D * |t - q| * (2 * r) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hd (abs_nonneg _)) hsum
          (abs_nonneg _) (mul_nonneg hD (abs_nonneg _))
      _ = _ := by ring

theorem centered_matrix_linearization (b : RMat) (u v : G) {c p t q B D r : ℝ}
    (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hb : Matrix.trace b = 0) (hbn : ‖b‖ ≤ B) (hbd : |b.det| ≤ D)
    (hu : (u : RMat) = scalarAffine b c t) (hv : (v : RMat) = scalarAffine b p q)
    (hc : 1 / 2 ≤ c) (hp : 1 / 2 ≤ p) (ht : |t| ≤ r) (hq : |q| ≤ r) :
    ‖(u : RMat) - 1‖ ≤ 2 * D * r ^ 2 + B * r ∧
    ‖(u : RMat) - (v : RMat)‖ ≤ (4 * D * r + B) * |t - q| ∧
    ‖(u : RMat) - (v : RMat) - (t - q) • b‖ ≤ 4 * D * r * |t - q| := by
  obtain ⟨hcone, hcdiff⟩ := centered_scalar_constant_bounds hD hr hbd hc hp ht hq
    (sl2_centered_coordinate_equation b u hb hu) (sl2_centered_coordinate_equation b v hb hv)
  have hIn : ‖(1 : RMat)‖ ≤ 2 := by
    simpa using frobenius_norm_le_of_entry_bound (by norm_num : (0 : ℝ) ≤ 1)
      (by intro i j; fin_cases i <;> fin_cases j <;> norm_num : ∀ i j, |(1 : RMat) i j| ≤ 1)
  have hone : (u : RMat) - 1 = (c - 1) • (1 : RMat) + t • b := by
    rw [hu, scalarAffine_eq_smul_add]
    module
  have hdiff : (u : RMat) - (v : RMat) = (c - p) • (1 : RMat) + (t - q) • b := by
    rw [hu, hv, scalarAffine_eq_smul_add, scalarAffine_eq_smul_add]
    module
  have hnormc : ‖(c - p) • (1 : RMat)‖ ≤ 4 * D * r * |t - q| := by
    rw [norm_smul, Real.norm_eq_abs]
    have hh := mul_le_mul hcdiff hIn (norm_nonneg _) (by positivity : 0 ≤ 2 * D * r * |t - q|)
    convert hh using 1; ring
  have hnormt : ‖(t - q) • b‖ ≤ B * |t - q| := by
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right hbn (abs_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hone]
    calc
      _ ≤ ‖(c - 1) • (1 : RMat)‖ + ‖t • b‖ := norm_add_le _ _
      _ ≤ (D * r ^ 2) * 2 + r * B := by
        simp only [norm_smul, Real.norm_eq_abs]
        exact add_le_add (mul_le_mul hcone hIn (norm_nonneg _) (by positivity))
          (mul_le_mul ht hbn (norm_nonneg _) hr)
      _ = _ := by ring
  · rw [hdiff]
    calc
      _ ≤ ‖(c - p) • (1 : RMat)‖ + ‖(t - q) • b‖ := norm_add_le _ _
      _ ≤ 4 * D * r * |t - q| + B * |t - q| := add_le_add hnormc hnormt
      _ = _ := by ring
  · rw [hdiff, add_sub_cancel_right]
    exact hnormc

theorem centered_matrix_small_chart (b : RMat) (u v : G) {c p t q M r : ℝ}
    (hM : 1 ≤ M) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hb : Matrix.trace b = 0) (hbn : ‖b‖ ≤ M) (hbd : |b.det| ≤ M)
    (hu : (u : RMat) = scalarAffine b c t) (hv : (v : RMat) = scalarAffine b p q)
    (hc : 1 / 2 ≤ c) (hp : 1 / 2 ≤ p) (ht : |t| ≤ r) (hq : |q| ≤ r) :
    ‖(u : RMat) - 1‖ ≤ 3 * M * r ∧ ‖(v : RMat) - 1‖ ≤ 3 * M * r ∧
    ‖(u : RMat) - (v : RMat)‖ ≤ 5 * M * |t - q| ∧
    ‖(u : RMat) - (v : RMat) - (t - q) • b‖ ≤ 4 * M * r * |t - q| := by
  have hM0 : 0 ≤ M := by linarith
  have hu' := centered_matrix_linearization b u v hM0 hr hb hbn hbd hu hv hc hp ht hq
  have hv' := centered_matrix_linearization b v u hM0 hr hb hbn hbd hv hu hp hc hq ht
  have hs : 2 * M * r ^ 2 + M * r ≤ 3 * M * r := by
    have hr2 : r ^ 2 ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hr2 hM0]
  refine ⟨hu'.1.trans hs, hv'.1.trans hs, hu'.2.1.trans ?_, hu'.2.2⟩
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  nlinarith

end TransposeFollowup.SL2Projection
