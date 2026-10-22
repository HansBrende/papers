import TransposeFollowup.SL2AdjointFrame
import TransposeFollowup.SL2NearIdentityProducts

/-! The existing bounded-word distance estimate supplies the trace budget
for adjoint-frame selection. The generator is the actual near-identity
matrix used by the commuting extraction. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem trace_lower_of_small_word_radius {A : Set G} {α : ℝ} {n : ℕ}
    (hα : 0 < α) (hαone : α ≤ 1) (hA : A ⊆ mobiusIdentityBall α)
    (hsmall : 2 * (5 : ℝ) ^ n * α ≤ 1) {x : G} (hx : x ∈ A ^ n) :
    1 ≤ Matrix.trace (x : RMat) := by
  have hn := set_pow_dist_from_one_le hα hαone hA n x hx
  have h00 := (entry_error_le_frobenius_dist (x : RMat) 1 0 0).trans hn
  have h11 := (entry_error_le_frobenius_dist (x : RMat) 1 1 1).trans hn
  change |x 0 0 - 1| ≤ (5 : ℝ) ^ n * α at h00
  change |x 1 1 - 1| ≤ (5 : ℝ) ^ n * α at h11
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  linarith [(abs_le.mp h00).1, (abs_le.mp h11).1]

theorem centered_generator_coordinates (z : RMat) :
    Matrix.trace (z - (Matrix.trace z / 2) • (1 : RMat)) = 0 ∧
      noncentralCoordinates (z - (Matrix.trace z / 2) • (1 : RMat)) = noncentralCoordinates z := by
  constructor
  · simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  · ext i
    fin_cases i <;> simp [noncentralCoordinates]

theorem exists_adjoint_frame_from_actual_spanning {A : Set G} {α d r : ℝ}
    (hA1 : 1 ∈ A) (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α) (hsmall : 2 * (5 : ℝ) ^ 34 * α ≤ 1)
    {p q z : G} (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hd : 0 < d)
    (hdet : d ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|)
    (hz : z ∈ mobiusIdentityBall (1 / 2)) (hr : 0 < r) (hfar : r ≤ dist (z : RMat) 1) :
    let b : RMat := (z : RMat) - (Matrix.trace (z : RMat) / 2) • (1 : RMat)
    ∃ u ∈ A ^ 34, ∃ v ∈ A ^ 68,
      (r / 8) ^ 3 / (3456 * (96 * ((4 : ℝ) ^ 34) ^ 4 / d) ^ 3) ≤
        |(directionFrame b (matrixConjugationLinear u b)
          (matrixConjugationLinear v b)).det| := by
  let b : RMat := (z : RMat) - (Matrix.trace (z : RMat) / 2) • (1 : RMat)
  let g : Fin 4 → G := ![1, p, q, p * q]
  have hgm (i : Fin 4) : g i ∈ A ^ 34 := by
    fin_cases i
    · exact Set.one_mem_pow hA1
    · exact hp
    · exact hq
    · exact hpq
  have hg : ∀ i j k, |g i j k| ≤ (4 : ℝ) ^ 34 := by
    intro i j k
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using set_pow_subset_matrixEntryBox
      (hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)) 34 (hgm i) j k
  have hframe : d ≤ |(Matrix.of fun i j => matrixCoordinates (g j : RMat) i).det| := by
    have he : (Matrix.of fun i j => matrixCoordinates (g j : RMat) i) =
        SL2Escape.pairSpanMatrix (p : RMat) (q : RMat) := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rwa [he]
  have ht (i : Fin 4) : (1 : ℝ) ≤ |Matrix.trace (g i : RMat)| :=
    (trace_lower_of_small_word_radius hα hαone hA hsmall (hgm i)).trans (le_abs_self _)
  have hb : Matrix.trace b = 0 := (centered_generator_coordinates (z : RMat)).1
  have hpivot : ∃ i, r / 8 ≤ |noncentralCoordinates b i| := by
    rw [show noncentralCoordinates b = noncentralCoordinates (z : RMat) from
      (centered_generator_coordinates (z : RMat)).2]
    exact exists_near_identity_noncentral_pivot z (by norm_num) (by norm_num) hz hfar
  have hh := exists_quantitative_adjoint_frame g b hAi hgm (by norm_num) hd
    (by norm_num : (0 : ℝ) < 1) (by positivity : 0 < r / 8) hg hframe ht hb hpivot
  simpa only [mul_one, show 2 * 34 = 68 by norm_num] using hh

end TransposeFollowup.SL2Projection
