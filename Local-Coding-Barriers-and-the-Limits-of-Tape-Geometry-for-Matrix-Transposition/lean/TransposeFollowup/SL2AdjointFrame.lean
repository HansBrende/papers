import TransposeFollowup.SL2AdjointSpan
import TransposeFollowup.BilinearBracketSelection

/-! Select a quantitative adjoint frame using actual bounded words of a
symmetric set. The nonzero-trace budget is explicit. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
open scoped Pointwise
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem exists_adjoint_frame_of_bracket_expansion (b e : RMat)
    (v : Fin 4 × Bool → G) (a : Fin 4 × Bool → ℝ) {ρ C : ℝ}
    (hb : Matrix.trace b = 0) (he : Matrix.trace e = 0) (hed : e.det = 0)
    (hρ : 0 < ρ) (htrace : ρ / 3 ≤ |Matrix.trace (e * b)|) (hC : 0 < C)
    (ha : ∀ i, |a i| ≤ C)
    (hL : ∀ x : RMat, e * x - x * e = ∑ i, a i • matrixConjugationLinear (v i) x) :
    ∃ i j k, ρ ^ 3 / (3456 * C ^ 3) ≤
      |(directionFrame b (matrixConjugationLinear (v i) b)
        (matrixConjugationLinear (v j * v k) b)).det| := by
  let f : (Fin 4 × Bool) × (Fin 4 × Bool) × (Fin 4 × Bool) → ℝ := fun t =>
    |(directionFrame b (matrixConjugationLinear (v t.1) b)
      (matrixConjugationLinear (v t.2.1 * v t.2.2) b)).det|
  obtain ⟨t, _, ht⟩ := Finset.univ.exists_max_image f Finset.univ_nonempty
  have hbound := bilinear_iterated_sum_bound (directionVolume b)
    (fun i => matrixConjugationLinear (v i)) a (fun x => e * x - x * e) b hC.le ha hL
    (D := f t) (fun i j k => by
      rw [matrixConjugationLinear_mul, directionVolume_apply]
      exact ht (i, j, k) (Finset.mem_univ _))
  have hhigh : |(directionFrame b (e * b - b * e)
      (e * (e * b - b * e) - (e * b - b * e) * e)).det| ≤ 512 * C ^ 3 * f t := by
    simpa only [directionVolume_apply, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, show (4 * 2 : ℝ) ^ 3 = 512 by norm_num]
      using hbound
  have hlow : 4 * (ρ / 3) ^ 3 ≤ |(directionFrame b (e * b - b * e)
      (e * (e * b - b * e) - (e * b - b * e) * e)).det| := by
    rw [directionFrame_nilpotent_brackets b e hb he hed, abs_mul, abs_pow,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) htrace 3) (by norm_num)
  refine ⟨t.1, t.2.1, t.2.2, ?_⟩
  change ρ ^ 3 / (3456 * C ^ 3) ≤ f t
  apply (div_le_iff₀ (by positivity : 0 < 3456 * C ^ 3)).mpr
  nlinarith only [hlow, hhigh]

theorem exists_quantitative_adjoint_frame {A : Set G} {n : ℕ}
    (g : Fin 4 → G) (b : RMat) {M d τ ρ : ℝ}
    (hAi : A⁻¹ = A) (hgm : ∀ i, g i ∈ A ^ n)
    (hM : 1 ≤ M) (hd : 0 < d) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hg : ∀ i j k, |g i j k| ≤ M)
    (hdet : d ≤ |(Matrix.of fun i j => matrixCoordinates (g j : RMat) i).det|)
    (htrace : ∀ i, τ ≤ |Matrix.trace (g i : RMat)|)
    (hb : Matrix.trace b = 0) (hpivot : ∃ i, ρ ≤ |noncentralCoordinates b i|) :
    ∃ u ∈ A ^ n, ∃ v ∈ A ^ (2 * n),
      ρ ^ 3 / (3456 * (96 * M ^ 4 / (d * τ)) ^ 3) ≤
        |(directionFrame b (matrixConjugationLinear u b)
          (matrixConjugationLinear v b)).det| := by
  obtain ⟨e, he, hed, heb, het⟩ := exists_nilpotent_trace_test b hρ hpivot
  obtain ⟨v, a, hv, ha, hL⟩ := exists_bounded_adjoint_bracket_expansion
    g e hM hd hτ hg hdet htrace heb
  have hvA (i : Fin 4 × Bool) : v i ∈ A ^ n := by
    rcases hv i with hh | hh <;> rw [hh]
    · exact hgm i.1
    · have hi := Set.inv_mem_inv.mpr (hgm i.1)
      rwa [← inv_pow, hAi] at hi
  obtain ⟨i, j, k, hijk⟩ := exists_adjoint_frame_of_bracket_expansion b e v a
    hb he hed hρ het (by have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM; positivity) ha hL
  refine ⟨v i, hvA i, v j * v k, ?_, hijk⟩
  rw [two_mul, pow_add]
  exact Set.mul_mem_mul (hvA j) (hvA k)

end TransposeFollowup.SL2Projection
