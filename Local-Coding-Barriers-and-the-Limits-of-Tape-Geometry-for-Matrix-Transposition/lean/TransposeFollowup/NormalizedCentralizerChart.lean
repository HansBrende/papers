import TransposeFollowup.SL2CentralizerChart
import TransposeFollowup.SL2NearIdentityProducts

/-! Chart coordinates and separation after normalizing a small commuting
cluster. Distances are native Frobenius distances and all losses are explicit. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem scalarAffine_recenter (z : RMat) (s t : ℝ) :
    scalarAffine z s t = scalarAffine (z - (Matrix.trace z / 2) • (1 : RMat))
      (s + t * Matrix.trace z / 2) t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarAffine] <;> ring

theorem scalarAffine_noncentral (b : RMat) (c t : ℝ) :
    noncentralCoordinates (scalarAffine b c t) = t • noncentralCoordinates b := by
  ext i
  fin_cases i
  · simp [noncentralCoordinates, scalarAffine]
    ring
  · simp [noncentralCoordinates, scalarAffine]
  · simp [noncentralCoordinates, scalarAffine]

theorem centered_parameters_of_distance (b : RMat) (u : G) {c t ρ R : ℝ}
    (hb : Matrix.trace b = 0) (hρ : 0 < ρ)
    (hpivot : ∃ i, ρ ≤ |noncentralCoordinates b i|)
    (hu : (u : RMat) = scalarAffine b c t)
    (hclose : dist (u : RMat) 1 ≤ R) :
    |c - 1| ≤ R ∧ |t| ≤ 2 * R / ρ := by
  have hR : 0 ≤ R := dist_nonneg.trans hclose
  have hentry (i j : Fin 2) : |u i j - (1 : RMat) i j| ≤ R :=
    (entry_error_le_frobenius_dist (u : RMat) 1 i j).trans hclose
  have htr : u 0 0 + u 1 1 = 2 * c := by
    have hh := congrArg Matrix.trace hu
    rw [scalarAffine_trace, hb] at hh
    simpa only [mul_zero, add_zero, Matrix.trace, Matrix.diag, Fin.sum_univ_two] using hh
  have hc : |c - 1| ≤ R := by
    have h00 : |u 0 0 - 1| ≤ R := hentry 0 0
    have h11 : |u 1 1 - 1| ≤ R := hentry 1 1
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp h00).1, (abs_le.mp h00).2,
      (abs_le.mp h11).1, (abs_le.mp h11).2]
  have hnc (i : Fin 3) : |noncentralCoordinates (u : RMat) i| ≤ 2 * R := by
    fin_cases i
    · change |u 0 0 - u 1 1| ≤ 2 * R
      have hh := norm_sub_le (u 0 0 - 1) (u 1 1 - 1)
      simp only [Real.norm_eq_abs, sub_sub_sub_cancel_right] at hh
      exact hh.trans (by have h00 := hentry 0 0; have h11 := hentry 1 1; change |u 0 0 - 1| ≤ R at h00; change |u 1 1 - 1| ≤ R at h11; linarith)
    · have hh : |u 0 1| ≤ R := by simpa using hentry 0 1
      exact hh.trans (by linarith)
    · have hh : |u 1 0| ≤ R := by simpa using hentry 1 0
      exact hh.trans (by linarith)
  obtain ⟨i, hi⟩ := hpivot
  have ht := hnc i
  rw [hu, scalarAffine_noncentral, Pi.smul_apply, smul_eq_mul, abs_mul] at ht
  refine ⟨hc, (le_div_iff₀ hρ).mpr ?_⟩
  exact (mul_le_mul_of_nonneg_left hi (abs_nonneg t)).trans ht

theorem normalized_parameter_distance_bound (b : RMat) (h x y : G)
    {c p t q M B r : ℝ} (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hb : Matrix.trace b = 0) (hbn : ‖b‖ ≤ M) (hbd : |b.det| ≤ M)
    (hh : ∀ i j, |h i j| ≤ B)
    (hx : ((h⁻¹ * x : G) : RMat) = scalarAffine b c t)
    (hy : ((h⁻¹ * y : G) : RMat) = scalarAffine b p q)
    (hc : 1 / 2 ≤ c) (hp : 1 / 2 ≤ p) (ht : |t| ≤ r) (hq : |q| ≤ r) :
    dist (x : RMat) (y : RMat) ≤ 10 * B * M * |t - q| := by
  have hchart := (centered_matrix_small_chart b (h⁻¹ * x) (h⁻¹ * y)
    hM hr hr1 hb hbn hbd hx hy hc hp ht hq).2.2.1
  have hhn := frobenius_norm_le_of_entry_bound hB hh
  have hx' : (h : RMat) * ((h⁻¹ * x : G) : RMat) = (x : RMat) :=
    congrArg (fun z : G => (z : RMat)) (show h * (h⁻¹ * x) = x by group)
  have hy' : (h : RMat) * ((h⁻¹ * y : G) : RMat) = (y : RMat) :=
    congrArg (fun z : G => (z : RMat)) (show h * (h⁻¹ * y) = y by group)
  have hd := frobenius_dist_left_mul (h : RMat) ((h⁻¹ * x : G) : RMat) ((h⁻¹ * y : G) : RMat)
  rw [hx', hy'] at hd
  have hxy : dist ((h⁻¹ * x : G) : RMat) ((h⁻¹ * y : G) : RMat) ≤ 5 * M * |t - q| := by
    simpa only [dist_eq_norm] using hchart
  calc
    _ ≤ ‖(h : RMat)‖ * dist ((h⁻¹ * x : G) : RMat) ((h⁻¹ * y : G) : RMat) := hd
    _ ≤ (2 * B) * (5 * M * |t - q|) := mul_le_mul hhn hxy dist_nonneg (by positivity)
    _ = _ := by ring

end TransposeFollowup.SL2Projection
