import TransposeFollowup.MatrixFourBounds
import TransposeFollowup.SL2SpanCertificate
import TransposeFollowup.FrobeniusClosedRefinement

/-! Quantitative three-coordinate projection of the determinant-one
quadric. The missing coordinate is controlled by the exact determinant
identity on a sufficiently small patch. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix MatrixFour
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false

def determinantNormal (z : Fin 4 → ℝ) : Fin 4 → ℝ := ![z 3, -z 2, -z 1, z 0]

theorem determinant_normal_remainder (z x y : Fin 4 → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ i, |x i - z i| ≤ r) (hy : ∀ i, |y i - z i| ≤ r)
    (hdet : x 0 * x 3 - x 1 * x 2 = y 0 * y 3 - y 1 * y 2) :
    |determinantNormal z ⬝ᵥ (x - y)| ≤ 4 * r * ‖x - y‖ := by
  have hv (i : Fin 4) : |x i - y i| ≤ ‖x - y‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
  have hp (i j : Fin 4) :
      |(x i - z i) * (x j - z j) - (y i - z i) * (y j - z j)| ≤ 2 * r * ‖x - y‖ := by
    rw [show (x i - z i) * (x j - z j) - (y i - z i) * (y j - z j) =
      (x i - y i) * (x j - z j) + (y i - z i) * (x j - y j) by ring]
    calc
      _ ≤ |(x i - y i) * (x j - z j)| + |(y i - z i) * (x j - y j)| := abs_add_le _ _
      _ = |x i - y i| * |x j - z j| + |y i - z i| * |x j - y j| := by rw [abs_mul, abs_mul]
      _ ≤ ‖x - y‖ * r + r * ‖x - y‖ := by gcongr <;> first | apply hv | apply hx | apply hy
      _ = _ := by ring
  have he : determinantNormal z ⬝ᵥ (x - y) =
      ((x 1 - z 1) * (x 2 - z 2) - (y 1 - z 1) * (y 2 - z 2)) -
      ((x 0 - z 0) * (x 3 - z 3) - (y 0 - z 0) * (y 3 - z 3)) := by
    norm_num [determinantNormal, dotProduct, Fin.sum_univ_succ, Pi.sub_apply]
    linear_combination hdet
  rw [he]
  have hh := norm_sub_le
    ((x 1 - z 1) * (x 2 - z 2) - (y 1 - z 1) * (y 2 - z 2))
    ((x 0 - z 0) * (x 3 - z 3) - (y 0 - z 0) * (y 3 - z 3))
  simp only [Real.norm_eq_abs] at hh
  linarith [hp 1 2, hp 0 3]

theorem local_three_coordinate_bound {T : Matrix (Fin 4) (Fin 4) ℝ}
    (z : Fin 4 → ℝ) (i : Fin 4) {M d r t : ℝ}
    (hM : 1 ≤ M) (hd : 0 < d) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hT : ∀ j k, |T j k| ≤ M) (hz : ∀ j, |determinantNormal z j| ≤ M)
    (hdetT : d ≤ |(T.updateRow i (determinantNormal z)).det|)
    (hsmall : 768 * M ^ 4 * r ≤ d)
    (x y : Fin 4 → ℝ)
    (hx : ∀ j, |x j - z j| ≤ r) (hy : ∀ j, |y j - z j| ≤ r)
    (hdet : x 0 * x 3 - x 1 * x 2 = y 0 * y 3 - y 1 * y 2)
    (htrace : ∀ j, j ≠ i → |(T *ᵥ (x - y)) j| ≤ t) :
    ‖x - y‖ ≤ 192 * M ^ 4 * t / d := by
  let D := T.updateRow i (determinantNormal z)
  have hD : ∀ j k, |D j k| ≤ M := by
    intro j k
    by_cases hj : j = i
    · subst j; simpa only [D, Matrix.updateRow_self] using hz k
    · simpa only [D, Matrix.updateRow_ne hj] using hT j k
  have hn := determinant_normal_remainder z x y hr hx hy hdet
  have hv : ∀ j, |(D *ᵥ (x - y)) j| ≤ 4 * r * ‖x - y‖ + t := by
    intro j
    by_cases hj : j = i
    · subst j
      have he : (D *ᵥ (x - y)) i = determinantNormal z ⬝ᵥ (x - y) := by
        simp only [D, Matrix.mulVec, Matrix.updateRow_self]
      rw [he]
      linarith
    · have he : (D *ᵥ (x - y)) j = (T *ᵥ (x - y)) j := by
        simp only [D, Matrix.mulVec, Matrix.updateRow_ne hj]
      rw [he]
      have hp : 0 ≤ 4 * r * ‖x - y‖ := by positivity
      linarith [htrace j hj]
  have hb := mulVec_inverse_bound hM hd hD hdetT (x - y) (by positivity) hv
  have hb' := (le_div_iff₀ hd).mp hb
  have hs := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (x - y))
  rw [le_div_iff₀ hd]
  nlinarith only [hb', hs]

theorem exists_local_three_coordinate_projection {T : Matrix (Fin 4) (Fin 4) ℝ}
    (z : Fin 4 → ℝ) {M d r : ℝ}
    (hM : 1 ≤ M) (hd : 0 < d) (hr : 0 ≤ r)
    (hT : ∀ j k, |T j k| ≤ M) (hz : ∀ j, |determinantNormal z j| ≤ M)
    (hz0 : 1 / 2 ≤ |z 0|) (hdetT : d ≤ |T.det|)
    (hsmall : 6144 * M ^ 5 * r ≤ d) :
    ∃ i : Fin 4, d / (8 * M) ≤ |(T.updateRow i (determinantNormal z)).det| ∧
      ∀ (x y : Fin 4 → ℝ) {t : ℝ}, 0 ≤ t →
        (∀ j, |x j - z j| ≤ r) → (∀ j, |y j - z j| ≤ r) →
        x 0 * x 3 - x 1 * x 2 = y 0 * y 3 - y 1 * y 2 →
        (∀ j, j ≠ i → |(T *ᵥ (x - y)) j| ≤ t) →
        ‖x - y‖ ≤ 1536 * M ^ 5 * t / d := by
  have hM0 : 0 < M := by linarith
  obtain ⟨i, hi⟩ := exists_normal_row hM0 hd hT hdetT (determinantNormal z) 3
    (by change 1 / 2 ≤ |z 0|; exact hz0)
  refine ⟨i, hi, ?_⟩
  intro x y t ht hx hy hdet htrace
  have hm : 768 * M ^ 4 * r ≤ d / (8 * M) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * M)).mpr
    convert hsmall using 1; ring
  have hh := local_three_coordinate_bound z i hM (by positivity : (0 : ℝ) < d / (8 * M))
    hr ht hT hz hi hm x y hx hy hdet htrace
  convert hh using 1
  field_simp
  ring

local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

def matrixCoordinates (a : RMat) : Fin 4 → ℝ := ![a 0 0, a 0 1, a 1 0, a 1 1]

def traceFrame (g : Fin 4 → G) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i => determinantNormal (matrixCoordinates (g i : RMat))

theorem traceFrame_det (g : Fin 4 → G) :
    (traceFrame g).det = (Matrix.of fun i j => matrixCoordinates (g j : RMat) i).det := by
  let J : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 1; 0, 0, -1, 0; 0, -1, 0, 0; 1, 0, 0, 0]
  have hJ : J.det = 1 := by
    norm_num [J, Matrix.det_succ_row_zero, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove]
  have he : traceFrame g = (Matrix.of fun i j => matrixCoordinates (g j : RMat) i)ᵀ * J := by
    ext i j
    fin_cases j <;> norm_num [traceFrame, determinantNormal, matrixCoordinates, J,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_succ]
  rw [he, Matrix.det_mul, Matrix.det_transpose, hJ, mul_one]

theorem traceFrame_pair_det (p q : G) :
    (traceFrame ![1, p, q, p * q]).det =
      (SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det := by
  rw [traceFrame_det]
  apply congrArg Matrix.det
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCoordinates, SL2Escape.pairSpanMatrix, Matrix.SpecialLinearGroup.coe_mul]

theorem normal_dot_matrix (g : G) (x : RMat) :
    determinantNormal (matrixCoordinates (g : RMat)) ⬝ᵥ matrixCoordinates x =
      Matrix.trace (((g⁻¹ : G) : RMat) * x) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  change _ = Matrix.trace ((!![g 1 1, -g 0 1; -g 1 0, g 0 0] : RMat) * x)
  norm_num [determinantNormal, matrixCoordinates, dotProduct, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem traceFrame_difference (g : Fin 4 → G) (x y : G) (i : Fin 4) :
    (traceFrame g *ᵥ (matrixCoordinates (x : RMat) - matrixCoordinates (y : RMat))) i =
      Matrix.trace (((g i)⁻¹ * x : G) : RMat) - Matrix.trace (((g i)⁻¹ * y : G) : RMat) := by
  rw [Matrix.mulVec_sub]
  change determinantNormal (matrixCoordinates (g i : RMat)) ⬝ᵥ matrixCoordinates (x : RMat) -
    determinantNormal (matrixCoordinates (g i : RMat)) ⬝ᵥ matrixCoordinates (y : RMat) = _
  rw [normal_dot_matrix, normal_dot_matrix]
  rfl

theorem frobenius_dist_le_coordinate_norm (a b : RMat) :
    dist a b ≤ 2 * ‖matrixCoordinates a - matrixCoordinates b‖ := by
  have hv (i : Fin 4) :
      |matrixCoordinates a i - matrixCoordinates b i| ≤ ‖matrixCoordinates a - matrixCoordinates b‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (matrixCoordinates a - matrixCoordinates b) i
  have hs (i : Fin 4) := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr (hv i)
  simp only [sq_abs] at hs
  apply (frobenius_dist_le_iff (by positivity)).mpr
  simp only [Fin.sum_univ_two]
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  change (a 0 0 - b 0 0) ^ 2 ≤ ‖matrixCoordinates a - matrixCoordinates b‖ ^ 2 at h0
  change (a 0 1 - b 0 1) ^ 2 ≤ ‖matrixCoordinates a - matrixCoordinates b‖ ^ 2 at h1
  change (a 1 0 - b 1 0) ^ 2 ≤ ‖matrixCoordinates a - matrixCoordinates b‖ ^ 2 at h2
  change (a 1 1 - b 1 1) ^ 2 ≤ ‖matrixCoordinates a - matrixCoordinates b‖ ^ 2 at h3
  nlinarith only [h0, h1, h2, h3]

theorem exists_local_three_trace_projection (g : Fin 4 → G) (z : G) {M d r : ℝ}
    (hM : 1 ≤ M) (hd : 0 < d) (hr : 0 ≤ r)
    (hg : ∀ i j k, |g i j k| ≤ M) (hz : ∀ j k, |z j k| ≤ M)
    (hz0 : 1 / 2 ≤ |z 0 0|) (hdet : d ≤ |(traceFrame g).det|)
    (hsmall : 6144 * M ^ 5 * r ≤ d) :
    ∃ i : Fin 4, ∀ (x y : G) {t : ℝ}, 0 ≤ t →
      (∀ j k, |x j k - z j k| ≤ r) → (∀ j k, |y j k - z j k| ≤ r) →
      (∀ j, j ≠ i → |Matrix.trace (((g j)⁻¹ * x : G) : RMat) -
        Matrix.trace (((g j)⁻¹ * y : G) : RMat)| ≤ t) →
      dist (x : RMat) (y : RMat) ≤ 3072 * M ^ 5 * t / d := by
  have hT : ∀ i j, |traceFrame g i j| ≤ M := by
    intro i j
    fin_cases j <;> simpa [traceFrame, determinantNormal, matrixCoordinates] using
      (show ∀ j k, |g i j k| ≤ M from hg i) _ _
  have hn : ∀ j, |determinantNormal (matrixCoordinates (z : RMat)) j| ≤ M := by
    intro j
    fin_cases j <;> simpa [determinantNormal, matrixCoordinates] using hz _ _
  obtain ⟨i, _hi, hall⟩ := exists_local_three_coordinate_projection (matrixCoordinates (z : RMat))
    hM hd hr hT hn (by exact hz0) hdet hsmall
  refine ⟨i, ?_⟩
  intro x y t ht hx hy htrace
  have hx' : ∀ j, |matrixCoordinates (x : RMat) j - matrixCoordinates (z : RMat) j| ≤ r := by
    intro j
    fin_cases j <;> simpa [matrixCoordinates] using hx _ _
  have hy' : ∀ j, |matrixCoordinates (y : RMat) j - matrixCoordinates (z : RMat) j| ≤ r := by
    intro j
    fin_cases j <;> simpa [matrixCoordinates] using hy _ _
  have hxy : matrixCoordinates (x : RMat) 0 * matrixCoordinates (x : RMat) 3 -
      matrixCoordinates (x : RMat) 1 * matrixCoordinates (x : RMat) 2 =
      matrixCoordinates (y : RMat) 0 * matrixCoordinates (y : RMat) 3 -
      matrixCoordinates (y : RMat) 1 * matrixCoordinates (y : RMat) 2 := by
    change x 0 0 * x 1 1 - x 0 1 * x 1 0 = y 0 0 * y 1 1 - y 0 1 * y 1 0
    simpa only [Matrix.det_fin_two] using x.property.trans y.property.symm
  have hb := hall (matrixCoordinates (x : RMat)) (matrixCoordinates (y : RMat)) ht hx' hy' hxy
    (by intro j hj; rw [traceFrame_difference]; exact htrace j hj)
  calc
    _ ≤ 2 * ‖matrixCoordinates (x : RMat) - matrixCoordinates (y : RMat)‖ :=
      frobenius_dist_le_coordinate_norm _ _
    _ ≤ 2 * (1536 * M ^ 5 * t / d) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end TransposeFollowup.SL2Projection
