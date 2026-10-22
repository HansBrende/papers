import TransposeFollowup.AdjointCoefficientSelection
import TransposeFollowup.ActualCentralizerPacking
import TransposeFollowup.InverseFinalScalarIdentity
import TransposeFollowup.TraceBucketCover

/-! Select one actual word with both coefficients in the inverse-final
scalar readout bounded away from zero. The word length is at most 204;
the lower bound is polynomial in the original frame and distance bounds. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem commutator_square_det (b g : RMat) :
    (b*(g*g)-(g*g)*b).det = (Matrix.trace g)^2 * (b*g-g*b).det := by
  have he : b*(g*g)-(g*g)*b = Matrix.trace g • (b*g-g*b) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two] <;> ring
  rw [he, Matrix.det_smul]
  simp

theorem scalar_coefficient_two_choice {a c L ρ : ℝ}
    (hρ : 0 < ρ) (ha : ρ ≤ |a|) (hL : 9/4 ≤ L) :
    (ρ/4 ≤ |a| ∧ ρ/4 ≤ |a-c|) ∨
      (ρ/4 ≤ |L*a| ∧ ρ/4 ≤ |L*a-c|) := by
  by_cases h : ρ/4 ≤ |a-c|
  · exact Or.inl ⟨(by linarith only [hρ, ha]), h⟩
  have hbad : |a-c| < ρ/4 := lt_of_not_ge h
  have hprod : ρ ≤ |L*a| := by
    rw [abs_mul, abs_of_pos (by linarith only [hL] : 0 < L)]
    exact ha.trans (le_mul_of_one_le_left (abs_nonneg a) (by linarith only [hL]))
  have hlower : (5/4 : ℝ)*ρ ≤ |(L-1)*a| := by
    rw [abs_mul, abs_of_pos (by linarith only [hL] : 0 < L-1)]
    exact mul_le_mul (by linarith only [hL]) ha hρ.le (by linarith only [hL])
  have htri : |(L-1)*a| ≤ |L*a-c| + |a-c| := by
    convert abs_sub (L*a-c) (a-c) using 1
    congr 1
    ring
  exact Or.inr ⟨by linarith only [hprod, hρ], by linarith only [hlower, htri, hbad, hρ]⟩

theorem exists_two_coefficient_word (b : RMat) (g : G) {ρ : ℝ}
    (hρ : 0 < ρ) (hcoef : ρ ≤ |(b*(g : RMat)-(g : RMat)*b).det|)
    (htrace : 3/2 ≤ Matrix.trace (g : RMat)) :
    ∃ w : G, (w=g ∨ w=g*g) ∧
      ρ/4 ≤ |(b*(w : RMat)-(w : RMat)*b).det| ∧
      ρ/4 ≤ |(b*(w : RMat)-(w : RMat)*b).det - 4*b.det| := by
  have hsq : (b*((g*g : G) : RMat)-((g*g : G) : RMat)*b).det =
      (Matrix.trace (g : RMat))^2 * (b*(g : RMat)-(g : RMat)*b).det := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using commutator_square_det b (g : RMat)
  have hh := scalar_coefficient_two_choice (c := 4*b.det) hρ hcoef
    (show (9/4 : ℝ) ≤ (Matrix.trace (g : RMat))^2 by nlinarith only [htrace])
  rcases hh with h | h
  · exact ⟨g, Or.inl rfl, h⟩
  · exact ⟨g*g, Or.inr rfl, by simpa only [hsq] using h⟩

theorem exists_actual_two_readout_coefficients {A : Set G} {α d r : ℝ} {p q z : G}
    (hA1 : 1 ∈ A) (hAi : A⁻¹=A) (hα : 0<α) (hαone : α≤1)
    (hA : A ⊆ mobiusIdentityBall α) (hsmall : 4*(5:ℝ)^102*α≤1)
    (hp : p∈A^34) (hq : q∈A^34) (hpq : p*q∈A^34)
    (hd : 0<d) (hspan : d≤|(SL2Escape.pairSpanMatrix (p:RMat) (q:RMat)).det|)
    (hz : z∈mobiusIdentityBall (1/2)) (hr : 0<r) (hfar : r≤dist (z:RMat) 1) :
    let b := (z:RMat)-(Matrix.trace (z:RMat)/2) • (1:RMat)
    let Γ := (r/8)^3/(3456*(96*((4:ℝ)^34)^4/d)^3)
    let B := 128*((4:ℝ)^68)^2
    ∃ g∈A^204,
      Γ^2/(3328*B^4) ≤ |(b*(g:RMat)-(g:RMat)*b).det| ∧
      Γ^2/(3328*B^4) ≤ |(b*(g:RMat)-(g:RMat)*b).det-4*b.det| := by
  let b := (z:RMat)-(Matrix.trace (z:RMat)/2) • (1:RMat)
  let Γ := (r/8)^3/(3456*(96*((4:ℝ)^34)^4/d)^3)
  let R := (4:ℝ)^68
  let B := 128*R^2
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hB : 0<B := by dsimp only [B,R]; positivity
  have hΓ : 0<Γ := by dsimp only [Γ]; positivity
  have h34 : 2*(5:ℝ)^34*α≤1 := by
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤5) (by norm_num : 34≤102)) hα.le
    linarith only [hh, hsmall, mul_pos (by positivity : 0<(5:ℝ)^102) hα]
  obtain ⟨u,hu,v,hv,hframe⟩ := exists_adjoint_frame_from_actual_spanning
    hA1 hAi hα hαone hA h34 hp hq hpq hd hspan hz hr hfar
  have hu68 : u∈A^68 := Set.pow_subset_pow_right hA1 (by norm_num) hu
  have hAb := hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hword (w:G) (hw:w∈A^68) : ∀i j, |w i j|≤R := by
    intro i j
    simpa only [R, show (2:ℝ)*2=4 by norm_num] using set_pow_subset_matrixEntryBox hAb 68 hw i j
  have hbn : ‖b‖≤32 := (centered_near_identity_generator_bounds z hz).1
  have hnb : ‖b‖≤B := hbn.trans (by dsimp only [B]; nlinarith only [hR])
  have hconj (w:G) (hw:w∈A^68) : ‖matrixConjugationLinear w b‖≤B := by
    have hh := (matrixConjugation_trace_det_norm w b (zero_le_one.trans hR) (hword w hw) hbn).2.2
    convert hh using 1
    dsimp only [B]
    ring
  have hentry (x:RMat) (hx:‖x‖≤B) (i j:Fin 2) : |x i j|≤B := by
    have hh := entry_error_le_frobenius_dist x 0 i j
    simp only [Matrix.zero_apply, sub_zero, dist_zero_right] at hh
    exact hh.trans hx
  obtain ⟨g,hg,hcoef⟩ := exists_large_adjoint_coefficient b u v hB hΓ.le
    (centered_generator_coordinates (z:RMat)).1
    (hentry b hnb) (hentry _ (hconj u hu68)) (hentry _ (hconj v hv)) hframe
  have hg102 : g∈A^102 := by
    rcases hg with rfl | rfl | rfl
    · exact Set.pow_subset_pow_right hA1 (by norm_num) hu
    · exact Set.pow_subset_pow_right hA1 (by norm_num) hv
    · have hui : u⁻¹∈A^34 := by simpa only [← inv_pow,hAi] using Set.inv_mem_inv.mpr hu
      change u⁻¹*v∈A^(34+68)
      rw [pow_add]
      exact Set.mul_mem_mul hui hv
  have hgtrace : 3/2≤Matrix.trace (g:RMat) := by
    have hdist := set_pow_dist_from_one_le hα hαone hA 102 g hg102
    have he := trace_error_le_frobenius_dist (g:RMat) 1
    simp only [Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat] at he
    have hl := (abs_le.mp he).1
    linarith only [hsmall,hdist,hl]
  obtain ⟨w,hw,hfirst,hsecond⟩ := exists_two_coefficient_word b g
    (by positivity : 0<Γ^2/(832*B^4)) hcoef hgtrace
  have hw204 : w∈A^204 := by
    rcases hw with rfl | rfl
    · exact Set.pow_subset_pow_right hA1 (by norm_num) hg102
    · change g*g∈A^(102+102)
      rw [pow_add]
      exact Set.mul_mem_mul hg102 hg102
  have heq : Γ^2/(832*B^4)/4=Γ^2/(3328*B^4) := by ring
  exact ⟨w,hw204,by simpa only [heq] using hfirst,by simpa only [heq] using hsecond⟩

end TransposeFollowup.SL2Projection
