import TransposeFollowup.CentralizerTraceSquareScalar
import TransposeFollowup.NilpotentArithmeticWords

/-! Quantitative separation of the inverse-final mixed readout from the
identity. The two actual coefficient gaps control a commutator norm, so
the loss is inverse-linear in the gap, without an inverse-frame argument. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem sl2_inverse_frobenius_distance (u v : G) :
    dist ((u⁻¹ : G) : RMat) ((v⁻¹ : G) : RMat) = dist (u : RMat) (v : RMat) := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [frobenius_dist_sq, frobenius_dist_sq]
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem sl2_inverse_distance_one (u : G) :
    dist ((u⁻¹ : G) : RMat) 1 = dist (u : RMat) 1 := by
  simpa only [inv_one, Matrix.SpecialLinearGroup.coe_one] using
    sl2_inverse_frobenius_distance u 1

theorem frobenius_norm_one_two : ‖(1 : RMat)‖ ≤ 2 := by
  simpa using frobenius_norm_le_of_entry_bound (by norm_num : (0 : ℝ) ≤ 1)
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num :
      ∀ i j, |(1 : RMat) i j| ≤ 1)

theorem frobenius_norm_of_near_one (u : RMat) (h : dist u 1 ≤ 1) : ‖u‖ ≤ 3 := by
  have hh := norm_le_norm_sub_add u 1
  rw [← dist_eq_norm] at hh
  linarith [frobenius_norm_one_two]

theorem det_le_two_frobenius_sq (a : RMat) : |a.det| ≤ 2 * ‖a‖ ^ 2 := by
  have he (i j : Fin 2) : |a i j| ≤ ‖a‖ := by
    simpa only [Matrix.zero_apply, sub_zero, dist_zero_right] using
      entry_error_le_frobenius_dist a 0 i j
  rw [Matrix.det_fin_two]
  calc
    _ ≤ |a 0 0 * a 1 1| + |a 0 1 * a 1 0| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (a 0 0 * a 1 1) (a 0 1 * a 1 0)
    _ ≤ ‖a‖ * ‖a‖ + ‖a‖ * ‖a‖ := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (he 0 0) (he 1 1) (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul (he 0 1) (he 1 0) (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem commutator_norm_bound (b E : RMat) :
    ‖b * E - E * b‖ ≤ 2 * ‖b‖ * ‖E‖ := by
  calc
    _ ≤ ‖b * E‖ + ‖E * b‖ := norm_sub_le _ _
    _ ≤ ‖b‖ * ‖E‖ + ‖E‖ * ‖b‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

/-- Recover both noncentral coefficients of an error in three matrix
directions. The scalar coefficient requires no bound. -/
theorem two_direction_error_coefficients (b c E : RMat) {s t q M ρ : ℝ}
    (hρ : 0 < ρ) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hdet : ρ ^ 2 ≤ |(b * c - c * b).det|)
    (hE : E = s • (1 : RMat) + t • c - q • b) :
    |t| ≤ 4 * M * ‖E‖ / ρ ∧ |q| ≤ 4 * M * ‖E‖ / ρ := by
  let C := b * c - c * b
  have hC : ρ / 2 ≤ ‖C‖ := by
    have hh := hdet.trans (det_le_two_frobenius_sq C)
    nlinarith [norm_nonneg C]
  have he₁ : b * E - E * b = t • C := by
    rw [hE]
    dsimp only [C]
    simp only [mul_add, mul_sub, add_mul, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, one_mul, smul_sub]
    module
  have he₂ : c * E - E * c = q • C := by
    rw [hE]
    dsimp only [C]
    simp only [mul_add, mul_sub, add_mul, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, one_mul, smul_sub]
    module
  have bound (r : ℝ) (a : RMat) (ha : ‖a‖ ≤ M) (he : a * E - E * a = r • C) :
      |r| ≤ 4 * M * ‖E‖ / ρ := by
    have hh := commutator_norm_bound a E
    rw [he, norm_smul, Real.norm_eq_abs] at hh
    have hm := mul_le_mul_of_nonneg_right ha (norm_nonneg E)
    have hr := mul_le_mul_of_nonneg_left hC (abs_nonneg r)
    apply (le_div_iff₀ hρ).mpr
    nlinarith only [hh, hm, hr]
  exact ⟨bound t b hb he₁, bound q c hc he₂⟩

theorem centered_near_one_distance_coefficient (b : RMat) (u : G) {s t M : ℝ}
    (hM : 1 ≤ M) (hb : Matrix.trace b = 0) (hbn : ‖b‖ ≤ M) (hbd : |b.det| ≤ M)
    (hu : (u : RMat) = scalarAffine b s t) (hnear : dist (u : RMat) 1 ≤ 1/2) :
    dist (u : RMat) 1 ≤ 3 * M * |t| := by
  have hs : 1/2 ≤ s := by
    have hh := trace_error_le_frobenius_dist (u : RMat) 1
    rw [hu, scalarAffine_trace, hb] at hh
    simp only [mul_zero, add_zero, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat] at hh
    rw [← hu] at hh
    linarith [(abs_le.mp hh).1]
  by_cases ht : |t| ≤ 1
  · simpa only [dist_eq_norm] using
      (centered_matrix_small_chart b u u hM (abs_nonneg t) ht hb hbn hbd
        hu hu hs hs le_rfl le_rfl).1
  · have hMt : 1 ≤ M * |t| :=
      one_le_mul_of_one_le_of_one_le hM (le_of_lt (lt_of_not_ge ht))
    linarith

theorem near_one_distance_le_square (u : G) (hnear : dist (u : RMat) 1 ≤ 1) :
    dist (u : RMat) 1 ≤ dist ((u * u : G) : RMat) 1 := by
  let x : RMat := (u : RMat) - 1
  have hx : ‖x‖ ≤ 1 := hnear
  have he : (2 : ℝ) • x = ((u * u : G) : RMat) - 1 - x * x := by
    dsimp only [x]
    simp only [Matrix.SpecialLinearGroup.coe_mul, sub_mul, mul_sub, one_mul, mul_one,
      two_smul]
    abel
  have hh := norm_sub_le (((u * u : G) : RMat) - 1) (x * x)
  rw [← he, norm_smul, Real.norm_eq_abs] at hh
  rw [show |(2 : ℝ)| = 2 by norm_num] at hh
  have hm := norm_mul_le x x
  change ‖x‖ ≤ ‖((u * u : G) : RMat) - 1‖
  nlinarith [norm_nonneg x]

theorem mixed_readout_distance_bound (b : RMat) (u v g : G) {s t p q M ρ : ℝ}
    (hM : 1 ≤ M) (hρ : 0 < ρ) (hb : Matrix.trace b = 0)
    (hbn : ‖b‖ ≤ M) (hbd : |b.det| ≤ M)
    (hbg : ‖matrixConjugationLinear g b‖ ≤ M)
    (hu : (u : RMat) = scalarAffine b s t) (hv : (v : RMat) = scalarAffine b p q)
    (hun : dist (u : RMat) 1 ≤ 1/8) (hvn : dist (v : RMat) 1 ≤ 1/8)
    (hD : ρ ≤ |(b * (g : RMat) - (g : RMat) * b).det|)
    (hD' : ρ ≤ |(b * (g : RMat) - (g : RMat) * b).det - 4 * b.det|) :
    max (dist (u : RMat) 1) (dist (v : RMat) 1) ≤
      144 * M ^ 2 / ρ * dist ((v * u⁻¹ * g * (v * u) * g⁻¹ : G) : RMat) 1 := by
  let a : G := v * u
  let w : G := u * v⁻¹
  let W : G := v * u⁻¹ * g * (v * u) * g⁻¹
  let c : RMat := matrixConjugationLinear g b
  let E : RMat := matrixConjugationLinear g (a : RMat) - (w : RMat)
  have hcomm : Commute u v := by
    apply Subtype.ext
    change (u : RMat) * (v : RMat) = (v : RMat) * (u : RMat)
    rw [hu, hv]
    exact scalarAffine_commute b s t p q
  have hpair (x y : G) (hx : dist (x : RMat) 1 ≤ 1/8)
      (hy : dist (y : RMat) 1 ≤ 1/8) :
      dist ((x * y : G) : RMat) 1 ≤ 1/2 := by
    have hyn := frobenius_norm_of_near_one (y : RMat) (hy.trans (by norm_num))
    have hh := dist_triangle ((x * y : G) : RMat) (y : RMat) 1
    have he : dist ((x * y : G) : RMat) (y : RMat) ≤ dist (x : RMat) 1 * ‖(y : RMat)‖ := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, one_mul] using
        frobenius_dist_right_mul (x : RMat) 1 (y : RMat)
    have hm := mul_le_mul hx hyn (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/8)
    linarith
  have han : dist (a : RMat) 1 ≤ 1/2 := hpair v u hvn hun
  have hwn : dist (w : RMat) 1 ≤ 1/2 :=
    hpair u v⁻¹ hun (by rw [sl2_inverse_distance_one]; exact hvn)
  have hwnorm : ‖(w : RMat)‖ ≤ 3 :=
    frobenius_norm_of_near_one _ (hwn.trans (by norm_num))
  have hwinorm : ‖((w⁻¹ : G) : RMat)‖ ≤ 3 := by
    apply frobenius_norm_of_near_one
    rw [sl2_inverse_distance_one]
    exact hwn.trans (by norm_num)
  obtain ⟨ha, _, _⟩ := sl2_scalarAffine_product_coordinates b v u hv hu
  obtain ⟨_, hw, _⟩ := sl2_scalarAffine_product_coordinates b u v hu hv
  simp only [hb, mul_zero, add_zero] at ha hw
  have hEform : E = ((p*s-q*t*b.det) - (s*p+t*q*b.det)) • (1 : RMat) +
      (p*t+q*s) • c - (t*p-s*q) • b := by
    dsimp only [E, a, w, c]
    rw [ha, hw, matrixConjugation_scalarAffine, scalarAffine_eq_smul_add,
      scalarAffine_eq_smul_add]
    module
  have hdet : ρ ^ 2 ≤ |(b * c - c * b).det| := by
    dsimp only [c]
    rw [commutator_conjugate_det b g hb, abs_mul]
    have hh : ρ ≤ |4*b.det - (b*(g:RMat)-(g:RMat)*b).det| := by
      simpa only [abs_sub_comm] using hD'
    simpa only [pow_two] using mul_le_mul hD hh (by positivity) (abs_nonneg _)
  obtain ⟨hta, htw⟩ := two_direction_error_coefficients b c E hρ hbn hbg hdet hEform
  have hab : dist (a : RMat) 1 ≤ 12 * M^2 * ‖E‖ / ρ := by
    have hh := centered_near_one_distance_coefficient b a hM hb hbn hbd ha han
    have hm := mul_le_mul_of_nonneg_left hta (by positivity : 0 ≤ 3*M)
    apply hh.trans
    convert hm using 1; ring
  have hwb : dist (w : RMat) 1 ≤ 12 * M^2 * ‖E‖ / ρ := by
    have hh := centered_near_one_distance_coefficient b w hM hb hbn hbd hw hwn
    have hm := mul_le_mul_of_nonneg_left htw (by positivity : 0 ≤ 3*M)
    apply hh.trans
    convert hm using 1; ring
  have hEword : E = (w : RMat) * ((W : RMat) - 1) := by
    have he : w * W = g * a * g⁻¹ := by dsimp only [w, W, a]; group
    rw [mul_sub, mul_one, ← Matrix.SpecialLinearGroup.coe_mul, he]
    rfl
  have hEn : ‖E‖ ≤ 3 * dist (W : RMat) 1 := by
    rw [hEword]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right hwnorm (norm_nonneg _))
  have husq : a * w = u * u := by
    change (v*u)*(u*v⁻¹) = u*u
    rw [hcomm.inv_right.eq, ← hcomm.eq]
    group
  have hvsq : a * w⁻¹ = v * v := by
    change (v*u)*(u*v⁻¹)⁻¹ = v*v
    rw [hcomm.inv_right.eq]
    group
  have hprod (z : G) (hz : ‖(z : RMat)‖ ≤ 3)
      (hzd : dist (z : RMat) 1 ≤ 12 * M^2 * ‖E‖ / ρ) :
      dist ((a * z : G) : RMat) 1 ≤ 48 * M^2 * ‖E‖ / ρ := by
    have hh := dist_triangle ((a * z : G) : RMat) (z : RMat) 1
    have he : dist ((a * z : G) : RMat) (z : RMat) ≤ dist (a : RMat) 1 * ‖(z : RMat)‖ := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, one_mul] using
        frobenius_dist_right_mul (a : RMat) 1 (z : RMat)
    have hm := mul_le_mul hab hz (norm_nonneg _) (by positivity)
    calc
      _ ≤ dist (a : RMat) 1 * ‖(z : RMat)‖ + dist (z : RMat) 1 :=
        hh.trans (add_le_add he le_rfl)
      _ ≤ (12 * M^2 * ‖E‖ / ρ)*3 + 12 * M^2 * ‖E‖ / ρ := add_le_add hm hzd
      _ = _ := by ring
  have hfinal : 48 * M^2 * ‖E‖ / ρ ≤ 144 * M^2 / ρ * dist (W : RMat) 1 := by
    have hh := mul_le_mul_of_nonneg_left hEn (by positivity : 0 ≤ 48*M^2/ρ)
    convert hh using 1 <;> ring
  apply max_le
  · have hh := hprod w hwnorm hwb
    rw [husq] at hh
    exact (near_one_distance_le_square u (hun.trans (by norm_num))).trans (hh.trans hfinal)
  · have hh := hprod w⁻¹ hwinorm (by rw [sl2_inverse_distance_one]; exact hwb)
    rw [hvsq] at hh
    exact (near_one_distance_le_square v (hvn.trans (by norm_num))).trans (hh.trans hfinal)

end TransposeFollowup.SL2Projection
