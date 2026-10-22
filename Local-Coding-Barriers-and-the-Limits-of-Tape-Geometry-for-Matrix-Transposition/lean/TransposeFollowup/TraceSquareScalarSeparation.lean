import TransposeFollowup.MixedReadoutDistance

/-! The trace-square coordinate is quantitatively invertible on a single
sign branch away from the identity. No upper bound on the noncentral
coordinate is required. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem traceSquareScalar_noncentral (b : RMat) (u : G) {s t : ℝ}
    (hb : Matrix.trace b = 0) (hu : (u : RMat) = scalarAffine b s t) :
    traceSquareScalar u = 4/3 - (8/3 : ℝ)*b.det*t^2 := by
  rw [traceSquareScalar_centered b u hb hu]
  have hh := sl2_centered_coordinate_equation b u hb hu
  linarith only [hh]

theorem traceSquareScalar_abs_sub (b : RMat) (u v : G) {s t p q : ℝ}
    (hb : Matrix.trace b = 0)
    (hu : (u : RMat) = scalarAffine b s t) (hv : (v : RMat) = scalarAffine b p q) :
    |traceSquareScalar u - traceSquareScalar v| =
      (8/3 : ℝ)*|b.det| *|t-q| *|t+q| := by
  rw [traceSquareScalar_noncentral b u hb hu, traceSquareScalar_noncentral b v hb hv,
    show (4/3 - (8/3 : ℝ)*b.det*t^2) - (4/3 - (8/3 : ℝ)*b.det*q^2) =
      -((8/3 : ℝ)*b.det*(t-q)*(t+q)) by ring,
    abs_neg, abs_mul, abs_mul, abs_mul]
  norm_num

theorem traceSquareScalar_inverse_distance (b : RMat) (u v : G) {s t p q M L r : ℝ}
    (hM : 1 ≤ M) (hL : 0 < L) (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : Matrix.trace b = 0) (hbn : ‖b‖ ≤ M) (hbd : |b.det| ≤ M)
    (hgap : L ≤ |b.det|)
    (hu : (u : RMat) = scalarAffine b s t) (hv : (v : RMat) = scalarAffine b p q)
    (hun : dist (u : RMat) 1 ≤ 1/2) (hvn : dist (v : RMat) 1 ≤ 1/2)
    (hfar : r ≤ dist (u : RMat) 1) (hsign : 0 ≤ t*q) :
    dist (u : RMat) (v : RMat) ≤
      3*M^2/(L*r) * |traceSquareScalar u - traceSquareScalar v| := by
  let F := |traceSquareScalar u - traceSquareScalar v|
  have hF : 0 ≤ F := abs_nonneg _
  have hM0 : 0 ≤ M := by linarith
  have hLr : 0 < L*r := mul_pos hL hr
  have hscalar (x : G) (c a : ℝ) (hx : (x : RMat) = scalarAffine b c a)
      (hn : dist (x : RMat) 1 ≤ 1/2) : 1/2 ≤ c := by
    have hh := trace_error_le_frobenius_dist (x : RMat) 1
    have ht : Matrix.trace (x : RMat) = 2*c := by
      rw [hx, scalarAffine_trace, hb, mul_zero, add_zero]
    rw [ht] at hh
    norm_num only [Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat] at hh
    linarith only [(abs_le.mp hh).1, hn]
  have hs := hscalar u s t hu hun
  have hp := hscalar v p q hv hvn
  have hcp : 1 ≤ |s+p| := by rw [abs_of_pos (by linarith)]; linarith
  have hFsp : F = (8/3 : ℝ)*|s-p| *|s+p| := by
    dsimp only [F]
    rw [traceSquareScalar_centered b u hb hu, traceSquareScalar_centered b v hb hv,
      show ((8/3 : ℝ)*s^2-4/3) - ((8/3 : ℝ)*p^2-4/3) =
        (8/3 : ℝ)*(s-p)*(s+p) by ring, abs_mul, abs_mul]
    norm_num
  have hsp : |s-p| ≤ (3/8 : ℝ)*F := by
    have hh := le_mul_of_one_le_right (abs_nonneg (s-p)) hcp
    rw [hFsp]
    nlinarith only [hh]
  have htq : |t| ≤ |t+q| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    nlinarith only [hsign, sq_nonneg q]
  have htfar : r ≤ 3*M*|t+q| := by
    exact (hfar.trans (centered_near_one_distance_coefficient b u hM hb hbn hbd hu hun)).trans
      (mul_le_mul_of_nonneg_left htq (by positivity))
  have htcoef : L*r*|t-q| ≤ (9/8 : ℝ)*M*F := by
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htfar hL.le) (abs_nonneg (t-q))
    have h₂ := mul_le_mul_of_nonneg_right hgap
      (show 0 ≤ 3*M*|t+q| *|t-q| by positivity)
    rw [show F = (8/3 : ℝ)*|b.det| *|t-q| *|t+q| from
      traceSquareScalar_abs_sub b u v hb hu hv]
    nlinarith only [h₁, h₂]
  have hdiff : (u : RMat) - (v : RMat) = (s-p) • (1 : RMat) + (t-q) • b := by
    rw [hu, hv, scalarAffine_eq_smul_add, scalarAffine_eq_smul_add]
    module
  have hdist : dist (u : RMat) (v : RMat) ≤ (3/4 : ℝ)*F + M*|t-q| := by
    rw [dist_eq_norm, hdiff]
    calc
      _ ≤ ‖(s-p) • (1 : RMat)‖ + ‖(t-q) • b‖ := norm_add_le _ _
      _ ≤ ((3/8 : ℝ)*F)*2 + |t-q| *M := by
        simp only [norm_smul, Real.norm_eq_abs]
        exact add_le_add
          (mul_le_mul hsp frobenius_norm_one_two (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left hbn (abs_nonneg _))
      _ = _ := by ring
  have hLrM : L*r ≤ M^2 := by
    have hLM := hgap.trans hbd
    have hh := mul_le_mul hLM hr1 hr.le hM0
    nlinarith only [hh, hM]
  have h₁ := mul_le_mul_of_nonneg_left hdist hLr.le
  have h₂ := mul_le_mul_of_nonneg_left htcoef hM0
  have h₃ := mul_le_mul_of_nonneg_right hLrM hF
  have h₄ : 0 ≤ M^2*F := by positivity
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hLr).mpr
  nlinarith only [h₁, h₂, h₃, h₄]

end TransposeFollowup.SL2Projection
