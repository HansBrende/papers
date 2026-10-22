import TransposeFollowup.SL2CentralizerChart
import TransposeFollowup.TripleProductLinearization

/-! An explicit two-point remainder bound for three determinant-one
centralizer charts. A quantitative frame will convert it into inverse control. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix MatrixFour
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem centered_triple_product_remainder (b : Fin 3 → RMat) (u v : Fin 3 → G)
    (c p t q : Fin 3 → ℝ) {M r : ℝ}
    (hM : 1 ≤ M) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hsmall : 3 * M * r ≤ 1)
    (hb : ∀ i, Matrix.trace (b i) = 0)
    (hbn : ∀ i, ‖b i‖ ≤ M) (hbd : ∀ i, |(b i).det| ≤ M)
    (hu : ∀ i, (u i : RMat) = scalarAffine (b i) (c i) (t i))
    (hv : ∀ i, (v i : RMat) = scalarAffine (b i) (p i) (q i))
    (hc : ∀ i, 1 / 2 ≤ c i) (hp : ∀ i, 1 / 2 ≤ p i)
    (ht : ∀ i, |t i| ≤ r) (hq : ∀ i, |q i| ≤ r) :
    ‖((u 0 * u 1 * u 2 : G) : RMat) - ((v 0 * v 1 * v 2 : G) : RMat) -
      ((t 0 - q 0) • b 0 + (t 1 - q 1) • b 1 + (t 2 - q 2) • b 2)‖ ≤
        192 * M ^ 2 * r * ‖t - q‖ := by
  let N := ‖t - q‖
  have hM0 : 0 ≤ M := by linarith
  have hN : 0 ≤ N := norm_nonneg _
  have hcoord (i : Fin 3) : |t i - q i| ≤ N := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (t - q) i
  have hchart (i : Fin 3) := centered_matrix_small_chart (b i) (u i) (v i)
    hM hr hr1 (hb i) (hbn i) (hbd i) (hu i) (hv i) (hc i) (hp i) (ht i) (hq i)
  have hdiff (i : Fin 3) : ‖(u i : RMat) - (v i : RMat)‖ ≤ 5 * M * N :=
    (hchart i).2.2.1.trans (mul_le_mul_of_nonneg_left (hcoord i) (by positivity))
  have hlin (i : Fin 3) :
      ‖(u i : RMat) - (v i : RMat) - (t i - q i) • b i‖ ≤ 4 * M * r * N :=
    (hchart i).2.2.2.trans (mul_le_mul_of_nonneg_left (hcoord i) (by positivity))
  have hI : ‖(1 : RMat)‖ ≤ 2 := by
    simpa using frobenius_norm_le_of_entry_bound (by norm_num : (0 : ℝ) ≤ 1)
      (by intro i j; fin_cases i <;> fin_cases j <;> norm_num : ∀ i j, |(1 : RMat) i j| ≤ 1)
  have hprod := triple_product_linear_remainder
    (fun i => (u i : RMat)) (fun i => (v i : RMat)) hI hsmall
      (fun i => (hchart i).1) (fun i => (hchart i).2.1) hdiff
  let U : RMat := ((u 0 * u 1 * u 2 : G) : RMat) - ((v 0 * v 1 * v 2 : G) : RMat)
  let V : RMat := ((u 0 : RMat) - (v 0 : RMat)) +
    ((u 1 : RMat) - (v 1 : RMat)) + ((u 2 : RMat) - (v 2 : RMat))
  let L : RMat := (t 0 - q 0) • b 0 + (t 1 - q 1) • b 1 + (t 2 - q 2) • b 2
  have hUV : ‖U - V‖ ≤ 12 * (3 * M * r) * (5 * M * N) := hprod
  have hVL : ‖V - L‖ ≤ 12 * M * r * N := by
    have he : V - L = ((u 0 : RMat) - (v 0 : RMat) - (t 0 - q 0) • b 0) +
      ((u 1 : RMat) - (v 1 : RMat) - (t 1 - q 1) • b 1) +
      ((u 2 : RMat) - (v 2 : RMat) - (t 2 - q 2) • b 2) := by dsimp only [V, L]; module
    rw [he]
    have hh := norm_add₃_le
      (a := (u 0 : RMat) - (v 0 : RMat) - (t 0 - q 0) • b 0)
      (b := (u 1 : RMat) - (v 1 : RMat) - (t 1 - q 1) • b 1)
      (c := (u 2 : RMat) - (v 2 : RMat) - (t 2 - q 2) • b 2)
    linarith only [hh, hlin 0, hlin 1, hlin 2]
  change ‖U - L‖ ≤ 192 * M ^ 2 * r * N
  have htriangle : ‖U - L‖ ≤ ‖U - V‖ + ‖V - L‖ := norm_sub_le_norm_sub_add_norm_sub U V L
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hbudget := mul_le_mul_of_nonneg_right hMM (by positivity : 0 ≤ 12 * r * N)
  nlinarith only [htriangle, hUV, hVL, hbudget]

theorem centered_triple_product_inverse (b : Fin 3 → RMat) (u v : Fin 3 → G)
    (c p t q : Fin 3 → ℝ) (T : Matrix (Fin 4) (Fin 4) ℝ) {M r d : ℝ}
    (hM : 1 ≤ M) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hd : 0 < d)
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hT : ∀ i j, |T i j| ≤ M) (hdet : d ≤ |T.det|)
    (hcolumns : ∀ i j, T i j.succ = matrixCoordinates (b j) i)
    (hb : ∀ i, Matrix.trace (b i) = 0)
    (hbn : ∀ i, ‖b i‖ ≤ M) (hbd : ∀ i, |(b i).det| ≤ M)
    (hu : ∀ i, (u i : RMat) = scalarAffine (b i) (c i) (t i))
    (hv : ∀ i, (v i : RMat) = scalarAffine (b i) (p i) (q i))
    (hc : ∀ i, 1 / 2 ≤ c i) (hp : ∀ i, 1 / 2 ≤ p i)
    (ht : ∀ i, |t i| ≤ r) (hq : ∀ i, |q i| ≤ r) :
    ‖t - q‖ ≤ 192 * M ^ 4 / d *
      dist ((u 0 * u 1 * u 2 : G) : RMat) ((v 0 * v 1 * v 2 : G) : RMat) := by
  let N := ‖t - q‖
  let U : RMat := ((u 0 * u 1 * u 2 : G) : RMat) - ((v 0 * v 1 * v 2 : G) : RMat)
  let L : RMat := (t 0 - q 0) • b 0 + (t 1 - q 1) • b 1 + (t 2 - q 2) • b 2
  let w : Fin 4 → ℝ := Fin.cons 0 (t - q)
  have hNw : N ≤ ‖w‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
    intro i
    simpa only [w, Fin.cons_succ] using norm_le_pi_norm w i.succ
  have hrem : ‖U - L‖ ≤ 192 * M ^ 2 * r * N :=
    centered_triple_product_remainder b u v c p t q hM hr hr1 hsmall hb hbn hbd hu hv hc hp ht hq
  have hLn : ‖L‖ ≤ ‖U‖ + 192 * M ^ 2 * r * N := by
    have hh : ‖L‖ ≤ ‖U‖ + ‖U - L‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le U (U - L)
    linarith only [hh, hrem]
  have hTw (i : Fin 4) : (T *ᵥ w) i = matrixCoordinates L i := by
    simp only [w, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, hcolumns]
    fin_cases i <;> simp [L, matrixCoordinates, Pi.sub_apply] <;> ring
  have hvalue : ∀ i, |(T *ᵥ w) i| ≤ ‖U‖ + 192 * M ^ 2 * r * N := by
    intro i
    rw [hTw]
    have hentry (j k : Fin 2) : |L j k| ≤ ‖L‖ := by
      simpa only [Matrix.zero_apply, sub_zero, dist_zero_right] using
        entry_error_le_frobenius_dist L 0 j k
    fin_cases i <;> exact (hentry _ _).trans hLn
  have hinv := mulVec_inverse_bound hM hd hT hdet w (by positivity) hvalue
  have hn := (le_div_iff₀ hd).mp (hNw.trans hinv)
  have hab := mul_le_mul_of_nonneg_right habsorb (show 0 ≤ N from norm_nonneg _)
  change N ≤ 192 * M ^ 4 / d * ‖U‖
  rw [div_mul_eq_mul_div, le_div_iff₀ hd]
  nlinarith only [hn, hab]

end TransposeFollowup.SL2Projection
