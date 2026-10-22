import TransposeFollowup.SL2AdjointSpan
import TransposeFollowup.SL2SpanningTrace

/-! The existing bounded frame expansion detects any noncentral direction
by a single actual bounded word. The same coefficient will read both scalar
addition and multiplication in a nilpotent centralizer. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem exists_quantitative_frame_trace_test (g : Fin 4 → G) (b : RMat)
    {M d ρ : ℝ} (hM : 1 ≤ M) (hd : 0 < d) (hρ : 0 < ρ)
    (hg : ∀ i j k, |g i j k| ≤ M)
    (hdet : d ≤ |(Matrix.of fun i j => matrixCoordinates (g j : RMat) i).det|)
    (hpivot : ∃ i, ρ ≤ |noncentralCoordinates b i|) :
    ∃ i : Fin 4, ρ * d / (1152 * M ^ 4) ≤ |Matrix.trace (b * (g i : RMat))| := by
  obtain ⟨e, _het, _hed, heb, hetest⟩ := exists_nilpotent_trace_test b hρ hpivot
  obtain ⟨c, hc, heq⟩ := exists_bounded_matrix_frame_coordinates g e hM hd hg hdet heb
  obtain ⟨i, _hi, hmax⟩ := Finset.univ.exists_max_image
    (fun i : Fin 4 => |Matrix.trace (b * (g i : RMat))|) Finset.univ_nonempty
  have htrace : Matrix.trace (e * b) =
      ∑ j : Fin 4, c j * Matrix.trace (b * (g j : RMat)) := by
    rw [heq]
    simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.trace_mul_comm]
  have hupper : |Matrix.trace (e * b)| ≤
      4 * (96 * M ^ 4 / d) * |Matrix.trace (b * (g i : RMat))| := by
    rw [htrace]
    calc
      _ ≤ ∑ j : Fin 4, |c j * Matrix.trace (b * (g j : RMat))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 4, (96 * M ^ 4 / d) * |Matrix.trace (b * (g i : RMat))| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul (hc j) (hmax j hj) (abs_nonneg _) (by positivity)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  refine ⟨i, (div_le_iff₀ (by positivity : 0 < 1152 * M ^ 4)).mpr ?_⟩
  have hh := mul_le_mul_of_nonneg_right (hetest.trans hupper) hd.le
  field_simp at hh
  nlinarith only [hh]

theorem exists_actual_noncentral_trace_test (b : RMat) {A : Set G}
    {α d ρ : ℝ} {p q : G}
    (hA1 : 1 ∈ A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α)
    (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hd : 0 < d) (hρ : 0 < ρ)
    (hdet : d ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|)
    (hpivot : ∃ i, ρ ≤ |noncentralCoordinates b i|) :
    ∃ g ∈ A ^ 34,
      ρ * d / (1152 * ((4 : ℝ) ^ 34) ^ 4) ≤ |Matrix.trace (b * (g : RMat))| := by
  let g : Fin 4 → G := ![1, p, q, p * q]
  have hmem (i : Fin 4) : g i ∈ A ^ 34 := by
    fin_cases i
    · exact Set.one_mem_pow hA1
    · exact hp
    · exact hq
    · exact hpq
  have hpow : A ^ 34 ⊆ matrixEntryBox ((4 : ℝ) ^ 34) := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using set_pow_subset_matrixEntryBox
      (hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)) 34
  have hframe : d ≤ |(Matrix.of fun i j => matrixCoordinates (g j : RMat) i).det| := by
    rw [← traceFrame_det]
    simpa only [g, traceFrame_pair_det] using hdet
  obtain ⟨i, hi⟩ := exists_quantitative_frame_trace_test g b (by norm_num) hd hρ
    (fun i => hpow (hmem i)) hframe hpivot
  exact ⟨g i, hmem i, hi⟩

end TransposeFollowup.SL2Projection
