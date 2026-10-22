import TransposeFollowup.SL2NearIdentityAdjointFrame
import TransposeFollowup.NilpotentScalarArithmetic

/-! The trace Gram determinant of an actual adjoint frame detects a
quantitative scalar-readout coefficient among three actual relative words. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
open scoped Matrix.Norms.Frobenius Pointwise
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem directionFrame_sq_eq_trace_gram (b x y : RMat)
    (hb : Matrix.trace b = 0) (hx : Matrix.trace x = 0) (hy : Matrix.trace y = 0) :
    (directionFrame b x y).det ^ 2 = -2 *
      (!![Matrix.trace (b * b), Matrix.trace (b * x), Matrix.trace (b * y);
          Matrix.trace (b * x), Matrix.trace (x * x), Matrix.trace (x * y);
          Matrix.trace (b * y), Matrix.trace (x * y), Matrix.trace (y * y)]).det := by
  have hb' : b 1 1 = -b 0 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hb
    linarith only [hb]
  have hx' : x 1 1 = -x 0 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hx
    linarith only [hx]
  have hy' : y 1 1 = -y 0 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hy
    linarith only [hy]
  rw [directionFrame_det_formula, Matrix.det_fin_three]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, hb', hx', hy']
  ring

theorem trace_mul_entry_bound (x y : RMat) {B : ℝ} (hB : 0 ≤ B)
    (hx : ∀ i j, |x i j| ≤ B) (hy : ∀ i j, |y i j| ≤ B) :
    |Matrix.trace (x * y)| ≤ 4 * B ^ 2 := by
  have hp (i j k l : Fin 2) : |x i j * y k l| ≤ B ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hx i j) (hy k l) (abs_nonneg _) hB
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  have h0 := abs_add_le (x 0 0 * y 0 0) (x 0 1 * y 1 0)
  have h1 := abs_add_le (x 1 0 * y 0 1) (x 1 1 * y 1 1)
  have h := abs_add_le (x 0 0 * y 0 0 + x 0 1 * y 1 0)
    (x 1 0 * y 0 1 + x 1 1 * y 1 1)
  linarith only [h, h0, h1, hp 0 0 0 0, hp 0 1 1 0, hp 1 0 0 1, hp 1 1 1 1]

theorem trace_gram_rank_one_perturbation_bound {c a b e B M : ℝ}
    (hM : 0 ≤ M) (hc : |c| ≤ 4 * B ^ 2)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (he : |e| ≤ M) (hMB : M ≤ 8 * B ^ 2) :
    |(!![c, c+a, c+b; c+a, c, c+e; c+b, c+e, c] : Matrix (Fin 3) (Fin 3) ℝ).det| ≤
      416 * B ^ 4 * M := by
  have hp {x y : ℝ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
      |x * y| ≤ (8 * B ^ 2) * M := by
    rw [abs_mul]
    exact mul_le_mul (hx.trans hMB) hy (abs_nonneg _) (by positivity)
  have hsum : |2*a*b+2*a*e+2*b*e-a^2-b^2-e^2| ≤ 9 * (8 * B ^ 2) * M := by
    have hab : |2*a*b| ≤ 2 * ((8 * B ^ 2) * M) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left (hp ha hb) (by norm_num)
    have hae : |2*a*e| ≤ 2 * ((8 * B ^ 2) * M) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left (hp ha he) (by norm_num)
    have hbe : |2*b*e| ≤ 2 * ((8 * B ^ 2) * M) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left (hp hb he) (by norm_num)
    have haa : |a^2| ≤ (8 * B ^ 2) * M := by simpa only [pow_two] using hp ha ha
    have hbb : |b^2| ≤ (8 * B ^ 2) * M := by simpa only [pow_two] using hp hb hb
    have hee : |e^2| ≤ (8 * B ^ 2) * M := by simpa only [pow_two] using hp he he
    have h1 := abs_add_le (2*a*b) (2*a*e)
    have h2 := abs_add_le (2*a*b+2*a*e) (2*b*e)
    have h3 := abs_sub (2*a*b+2*a*e+2*b*e) (a^2)
    have h4 := abs_sub (2*a*b+2*a*e+2*b*e-a^2) (b^2)
    have h5 := abs_sub (2*a*b+2*a*e+2*b*e-a^2-b^2) (e^2)
    linarith only [hab, hae, hbe, haa, hbb, hee, h1, h2, h3, h4, h5]
  have htriple : |2*a*b*e| ≤ 2 * (8 * B ^ 2) ^ 2 * M := by
    have hh := mul_le_mul (hp ha hb) (he.trans hMB) (abs_nonneg e) (by positivity : 0 ≤ 8 * B ^ 2 * M)
    rw [← abs_mul] at hh
    calc
      _ = 2 * |(a*b)*e| := by rw [show 2*a*b*e = 2*((a*b)*e) by ring, abs_mul]; norm_num
      _ ≤ 2 * ((8 * B ^ 2 * M) * (8 * B ^ 2)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hdet : ( !![c, c+a, c+b; c+a, c, c+e; c+b, c+e, c] : Matrix (Fin 3) (Fin 3) ℝ).det =
      c * (2*a*b+2*a*e+2*b*e-a^2-b^2-e^2) + 2*a*b*e := by
    rw [Matrix.det_fin_three]
    simp
    ring
  rw [hdet]
  calc
    _ ≤ |c * (2*a*b+2*a*e+2*b*e-a^2-b^2-e^2)| + |2*a*b*e| := abs_add_le _ _
    _ ≤ (4 * B ^ 2) * (9 * (8 * B ^ 2) * M) + 2 * (8 * B ^ 2) ^ 2 * M := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul hc hsum (abs_nonneg _) (by positivity)) htriple
    _ = _ := by ring

theorem exists_large_trace_gram_deviation (b x y : RMat) {B γ : ℝ}
    (hB : 0 < B) (hγ : 0 ≤ γ)
    (hb : Matrix.trace b = 0) (hx : Matrix.trace x = 0) (hy : Matrix.trace y = 0)
    (hxx : Matrix.trace (x*x) = Matrix.trace (b*b))
    (hyy : Matrix.trace (y*y) = Matrix.trace (b*b))
    (hbB : ∀ i j, |b i j| ≤ B) (hxB : ∀ i j, |x i j| ≤ B) (hyB : ∀ i j, |y i j| ≤ B)
    (hframe : γ ≤ |(directionFrame b x y).det|) :
    γ ^ 2 / (832 * B ^ 4) ≤ |Matrix.trace (b*x) - Matrix.trace (b*b)| ∨
    γ ^ 2 / (832 * B ^ 4) ≤ |Matrix.trace (b*y) - Matrix.trace (b*b)| ∨
    γ ^ 2 / (832 * B ^ 4) ≤ |Matrix.trace (x*y) - Matrix.trace (b*b)| := by
  let c := Matrix.trace (b*b)
  let a := Matrix.trace (b*x)-c
  let d := Matrix.trace (b*y)-c
  let e := Matrix.trace (x*y)-c
  let M := max |a| (max |d| |e|)
  have hM : 0 ≤ M := (abs_nonneg a).trans (le_max_left _ _)
  have ha : |a| ≤ M := le_max_left _ _
  have hd : |d| ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have he : |e| ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hc : |c| ≤ 4*B^2 := trace_mul_entry_bound b b hB.le hbB hbB
  have hMB : M ≤ 8*B^2 := by
    apply max_le
    · exact (abs_sub _ _).trans (by linarith only [trace_mul_entry_bound b x hB.le hbB hxB, hc])
    · apply max_le
      · exact (abs_sub _ _).trans (by linarith only [trace_mul_entry_bound b y hB.le hbB hyB, hc])
      · exact (abs_sub _ _).trans (by linarith only [trace_mul_entry_bound x y hB.le hxB hyB, hc])
  have hsq := directionFrame_sq_eq_trace_gram b x y hb hx hy
  rw [hxx, hyy] at hsq
  have heq : (!![Matrix.trace (b*b), Matrix.trace (b*x), Matrix.trace (b*y);
      Matrix.trace (b*x), Matrix.trace (b*b), Matrix.trace (x*y);
      Matrix.trace (b*y), Matrix.trace (x*y), Matrix.trace (b*b)]).det =
      (!![c,c+a,c+d; c+a,c,c+e; c+d,c+e,c] : Matrix (Fin 3) (Fin 3) ℝ).det := by
    dsimp only [c, a, d, e]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [heq] at hsq
  have hupper := trace_gram_rank_one_perturbation_bound hM hc ha hd he hMB
  have hγsq : γ^2 ≤ (directionFrame b x y).det^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hγ hframe 2
  have hh : γ^2 / (832*B^4) ≤ M := by
    apply (div_le_iff₀ (by positivity : 0 < 832*B^4)).mpr
    have hl := (abs_le.mp hupper).1
    nlinarith only [hγsq, hsq, hl]
  rcases (le_max_iff.mp hh) with h | h
  · exact Or.inl h
  · exact Or.inr (le_max_iff.mp h)

theorem matrixConjugationLinear_trace (g : G) (b : RMat) :
    Matrix.trace (matrixConjugationLinear g b) = Matrix.trace b := by
  rw [matrixConjugationLinear_apply, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]

theorem matrixConjugationLinear_product (g : G) (b x : RMat) :
    matrixConjugationLinear g b * matrixConjugationLinear g x =
      matrixConjugationLinear g (b*x) := by
  have hi : ((g⁻¹ : G) : RMat) * (g : RMat) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  simp only [matrixConjugationLinear_apply]
  calc
    _ = (g : RMat) * b * (((g⁻¹ : G) : RMat) * (g : RMat)) * x * ((g⁻¹ : G) : RMat) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hi]; simp only [mul_one, Matrix.mul_assoc]

theorem trace_adjoint_pair_coefficient (b : RMat) (u v : G) (hb : Matrix.trace b = 0) :
    Matrix.trace (matrixConjugationLinear u b * matrixConjugationLinear v b) =
      (b * ((u⁻¹*v : G) : RMat) - ((u⁻¹*v : G) : RMat) * b).det - 2*b.det := by
  have hv : matrixConjugationLinear v b =
      matrixConjugationLinear u (matrixConjugationLinear (u⁻¹*v) b) := by
    rw [matrixConjugationLinear_mul]
    simp only [mul_inv_cancel_left]
  rw [hv, matrixConjugationLinear_product, matrixConjugationLinear_trace]
  have hh := scalarAffine_sandwich_trace b ((u⁻¹*v : G) : RMat) 0 1 0 1 hb
  simpa only [scalarAffine_eq_smul_add, zero_smul, one_smul, zero_add,
    zero_mul, mul_zero, one_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
    matrixConjugationLinear_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_assoc] using hh

theorem exists_large_adjoint_coefficient (b : RMat) (u v : G) {B γ : ℝ}
    (hB : 0 < B) (hγ : 0 ≤ γ) (hb : Matrix.trace b = 0)
    (hbB : ∀ i j, |b i j| ≤ B)
    (huB : ∀ i j, |matrixConjugationLinear u b i j| ≤ B)
    (hvB : ∀ i j, |matrixConjugationLinear v b i j| ≤ B)
    (hframe : γ ≤ |(directionFrame b (matrixConjugationLinear u b)
      (matrixConjugationLinear v b)).det|) :
    ∃ g : G, (g=u ∨ g=v ∨ g=u⁻¹*v) ∧
      γ^2/(832*B^4) ≤ |(b*(g : RMat)-(g : RMat)*b).det| := by
  have hdiag (g : G) : Matrix.trace (matrixConjugationLinear g b * matrixConjugationLinear g b) =
      Matrix.trace (b*b) := by rw [matrixConjugationLinear_product, matrixConjugationLinear_trace]
  have hc : Matrix.trace (b*b) = -2*b.det := by
    have hh := trace_adjoint_pair_coefficient b 1 1 hb
    simpa only [matrixConjugationLinear_apply, Matrix.SpecialLinearGroup.coe_one, inv_one,
      one_mul, mul_one, sub_self, Matrix.det_zero, zero_sub, neg_mul] using hh
  have hpair (g : G) : Matrix.trace (b * matrixConjugationLinear g b) - Matrix.trace (b*b) =
      (b*(g : RMat)-(g : RMat)*b).det := by
    have hh := trace_adjoint_pair_coefficient b 1 g hb
    simp only [matrixConjugationLinear_apply, Matrix.SpecialLinearGroup.coe_one,
      inv_one, one_mul, mul_one] at hh
    change Matrix.trace (b * matrixConjugationLinear g b) = _ at hh
    rw [hh, hc]
    ring
  have hpairuv : Matrix.trace (matrixConjugationLinear u b * matrixConjugationLinear v b) -
      Matrix.trace (b*b) = (b*((u⁻¹*v : G) : RMat)-((u⁻¹*v : G) : RMat)*b).det := by
    rw [trace_adjoint_pair_coefficient b u v hb, hc]
    ring
  have hh := exists_large_trace_gram_deviation b (matrixConjugationLinear u b)
    (matrixConjugationLinear v b) hB hγ hb
    (by rw [matrixConjugationLinear_trace, hb]) (by rw [matrixConjugationLinear_trace, hb])
    (hdiag u) (hdiag v) hbB huB hvB hframe
  rw [hpair u, hpair v, hpairuv] at hh
  rcases hh with h | h | h
  · exact ⟨u, Or.inl rfl, h⟩
  · exact ⟨v, Or.inr (Or.inl rfl), h⟩
  · exact ⟨u⁻¹*v, Or.inr (Or.inr rfl), h⟩

end TransposeFollowup.SL2Projection
