import TransposeFollowup.SL2CentralizerChart

/-! Fixed-matrix scalar arithmetic in the positive nilpotent centralizer.
Addition is read linearly, and multiplication uses the square of the SAME
coefficient. Thus the inverse-final identity's constant projection
coefficient does not prevent scalar ring operations. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem scalarAffine_trace_right (b g : RMat) (c t : ℝ) :
    Matrix.trace (scalarAffine b c t * g) =
      c * Matrix.trace g + t * Matrix.trace (b * g) := by
  simp only [scalarAffine_eq_smul_add, add_mul, Matrix.smul_mul, one_mul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]

theorem scalarAffine_sandwich_trace (b g : RMat) (c t p q : ℝ)
    (hb : Matrix.trace b = 0) :
    Matrix.trace (scalarAffine b c t * g * scalarAffine b p q * g.adjugate) =
      2 * c * p * g.det + t * q * ((b * g - g * b).det - 2 * b.det * g.det) := by
  have hb' : b 1 1 = -b 0 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hb
    linarith
  rw [Matrix.adjugate_fin_two]
  simp only [scalarAffine, Matrix.det_fin_two, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hb']
  ring

theorem centered_trace_arithmetic (b : RMat) (u v g : G) {c t p q : ℝ}
    (hb : Matrix.trace b = 0)
    (hu : (u : RMat) = scalarAffine b c t) (hv : (v : RMat) = scalarAffine b p q) :
    let ℓ := Matrix.trace (b * (g : RMat))
    let τ := Matrix.trace (g : RMat)
    Matrix.trace ((u * v * g : G) : RMat) =
        (c * p - b.det * t * q) * τ + (c * q + t * p) * ℓ ∧
      Matrix.trace ((u * g * v * g⁻¹ : G) : RMat) =
        2 * c * p + t * q * ((2 - τ ^ 2) * b.det - ℓ ^ 2) := by
  constructor
  · simp only [Matrix.SpecialLinearGroup.coe_mul, hu, hv, scalarAffine_mul,
      hb, mul_zero, add_zero, scalarAffine_trace_right]
    ring
  · have hD := SL2Escape.pairSpanMatrix_det_trace_polynomial b (g : RMat)
    simp only [SL2Escape.pairSpanMatrix_det, hb, Matrix.SpecialLinearGroup.det_coe,
      zero_pow (by norm_num : 2 ≠ 0), zero_mul, sub_zero, mul_one, add_zero] at hD
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hu, hv]
    rw [scalarAffine_sandwich_trace b (g : RMat) c t p q hb, hD,
      Matrix.SpecialLinearGroup.det_coe]
    ring

theorem nilpotent_positive_trace_arithmetic (b : RMat) (u v g : G) {c t p q : ℝ}
    (hb : Matrix.trace b = 0) (hbd : b.det = 0)
    (hu : (u : RMat) = scalarAffine b c t) (hv : (v : RMat) = scalarAffine b p q)
    (hc : 1 / 2 ≤ c) (hp : 1 / 2 ≤ p) :
    let ℓ := Matrix.trace (b * (g : RMat))
    c = 1 ∧ p = 1 ∧
      Matrix.trace ((u * v * g : G) : RMat) = Matrix.trace (g : RMat) + ℓ * (t + q) ∧
      Matrix.trace ((u * g * v * g⁻¹ : G) : RMat) = 2 - ℓ ^ 2 * (t * q) := by
  have hce := sl2_centered_coordinate_equation b u hb hu
  have hpe := sl2_centered_coordinate_equation b v hb hv
  rw [hbd] at hce hpe
  have hc1 : c = 1 := by nlinarith only [hce, hc]
  have hp1 : p = 1 := by nlinarith only [hpe, hp]
  subst c p
  obtain ⟨hadd, hmul⟩ := centered_trace_arithmetic b u v g hb hu hv
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [hadd, hbd]
    ring
  · rw [hmul, hbd]
    ring

theorem centered_trace_arithmetic_error (b : RMat) (u v g : G) {c t p q κ r T L : ℝ}
    (hb : Matrix.trace b = 0) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hbd : |b.det| ≤ κ) (hsmall : κ * r ^ 2 ≤ 1)
    (hu : (u : RMat) = scalarAffine b c t) (hv : (v : RMat) = scalarAffine b p q)
    (hc : 1 / 2 ≤ c) (hp : 1 / 2 ≤ p) (ht : |t| ≤ r) (hq : |q| ≤ r)
    (hT : 0 ≤ T)
    (hg : |Matrix.trace (g : RMat)| ≤ T) (hbg : |Matrix.trace (b * (g : RMat))| ≤ L) :
    let ℓ := Matrix.trace (b * (g : RMat))
    |Matrix.trace ((u * v * g : G) : RMat) - (Matrix.trace (g : RMat) + ℓ * (t + q))| ≤
        4 * κ * r ^ 2 * T + 2 * κ * r ^ 3 * L ∧
      |Matrix.trace ((u * g * v * g⁻¹ : G) : RMat) - (2 - ℓ ^ 2 * (t * q))| ≤
        κ * r ^ 2 * (8 + T ^ 2) := by
  have hce := sl2_centered_coordinate_equation b u hb hu
  have hpe := sl2_centered_coordinate_equation b v hb hv
  have hc1 := (centered_scalar_constant_bounds hκ hr hbd hc hp ht hq hce hpe).1
  have hp1 := (centered_scalar_constant_bounds hκ hr hbd hp hc hq ht hpe hce).1
  have hp2 : |p| ≤ 2 := by rw [abs_of_nonneg (by linarith : 0 ≤ p)]; linarith [(abs_le.mp hp1).2]
  have hcp : |c * p - 1| ≤ 3 * κ * r ^ 2 := by
    calc
      _ = |(c - 1) * p + (p - 1)| := by congr 1; ring
      _ ≤ |(c - 1) * p| + |p - 1| := abs_add_le _ _
      _ ≤ (κ * r ^ 2) * 2 + κ * r ^ 2 := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hc1 hp2 (abs_nonneg _) (by positivity)) hp1
      _ = _ := by ring
  have htq : |t * q| ≤ r ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul ht hq (abs_nonneg _) hr
  have hdet : |b.det * t * q| ≤ κ * r ^ 2 := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul hbd htq (abs_nonneg _) hκ
  have ha : |c * p - b.det * t * q - 1| ≤ 4 * κ * r ^ 2 := by
    have hh := norm_sub_le (c * p - 1) (b.det * t * q)
    simp only [Real.norm_eq_abs] at hh
    rw [show c * p - 1 - b.det * t * q = c * p - b.det * t * q - 1 by ring] at hh
    linarith
  have hb' : |c * q + t * p - (t + q)| ≤ 2 * κ * r ^ 3 := by
    calc
      _ = |(c - 1) * q + t * (p - 1)| := by congr 1; ring
      _ ≤ |(c - 1) * q| + |t * (p - 1)| := abs_add_le _ _
      _ ≤ (κ * r ^ 2) * r + r * (κ * r ^ 2) := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hc1 hq (abs_nonneg _) (by positivity))
          (mul_le_mul ht hp1 (abs_nonneg _) hr)
      _ = _ := by ring
  have hg2 : |2 - Matrix.trace (g : RMat) ^ 2| ≤ 2 + T ^ 2 := by
    have hh := norm_sub_le (2 : ℝ) (Matrix.trace (g : RMat) ^ 2)
    simp only [Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num, abs_sq] at hh
    have hs : Matrix.trace (g : RMat) ^ 2 ≤ T ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hT).mpr hg
    linarith
  obtain ⟨hadd, hmul⟩ := centered_trace_arithmetic b u v g hb hu hv
  refine ⟨?_, ?_⟩
  · rw [hadd, show
        (c * p - b.det * t * q) * Matrix.trace (g : RMat) +
          (c * q + t * p) * Matrix.trace (b * (g : RMat)) -
          (Matrix.trace (g : RMat) + Matrix.trace (b * (g : RMat)) * (t + q)) =
        (c * p - b.det * t * q - 1) * Matrix.trace (g : RMat) +
          (c * q + t * p - (t + q)) * Matrix.trace (b * (g : RMat)) by ring]
    exact (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul ha hg (abs_nonneg _) (by positivity))
        (mul_le_mul hb' hbg (abs_nonneg _) (by positivity)))
  · rw [hmul, show
        2 * c * p + t * q * ((2 - Matrix.trace (g : RMat) ^ 2) * b.det -
          Matrix.trace (b * (g : RMat)) ^ 2) -
          (2 - Matrix.trace (b * (g : RMat)) ^ 2 * (t * q)) =
        2 * (c * p - 1) + (b.det * t * q) * (2 - Matrix.trace (g : RMat) ^ 2) by ring]
    calc
      _ ≤ |2 * (c * p - 1)| + |(b.det * t * q) * (2 - Matrix.trace (g : RMat) ^ 2)| :=
        abs_add_le _ _
      _ ≤ 2 * (3 * κ * r ^ 2) + (κ * r ^ 2) * (2 + T ^ 2) := by
        rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
        exact add_le_add (mul_le_mul_of_nonneg_left hcp (by norm_num))
          (mul_le_mul hdet hg2 (abs_nonneg _) (by positivity))
      _ = _ := by ring

end TransposeFollowup.SL2Projection
