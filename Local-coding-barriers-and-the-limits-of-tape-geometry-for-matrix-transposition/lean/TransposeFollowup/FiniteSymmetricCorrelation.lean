import TransposeFollowup.SymmetricOffsetSum

/-! A reusable finite quadratic-correlation estimate from near-offset
and distant-offset bounds. It applies to retained or shifted sequences. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

theorem symmetric_finite_correlation_le_of_offset_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (u : ℕ → E)
    (hsym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (D N : ℕ) (A B : ℝ)
    (hnear : ∀ d, (∑ j ∈ Finset.range N, |inner ℝ (T (u j)) (u (j + d))|) ≤ A)
    (hfar : (∑ d ∈ Finset.range N, ∑ j ∈ Finset.range N,
      |inner ℝ (T (u j)) (u (j + (D + d)))|) ≤ B) :
    inner ℝ (T (∑ j ∈ Finset.range N, u j)) (∑ j ∈ Finset.range N, u j) ≤
      2 * ((D : ℝ) * A + B) := by
  let a := fun j k => |inner ℝ (T (u j)) (u k)|
  let F := fun d => ∑ j ∈ Finset.range N, a j (j + d)
  have ha : ∀ j k, 0 ≤ a j k := fun _ _ => abs_nonneg _
  have hasym : ∀ j k, a j k = a k j := fun j k =>
    congrArg abs ((hsym (u j) (u k)).trans (real_inner_comm _ _))
  have hn : (∑ d ∈ Finset.range D, F d) ≤ (D : ℝ) * A := by
    calc
      _ ≤ ∑ _d ∈ Finset.range D, A := Finset.sum_le_sum (fun d _ => hnear d)
      _ = _ := by simp
  have htotal : (∑ d ∈ Finset.range N, F d) ≤ (D : ℝ) * A + B := by
    calc
      _ ≤ ∑ d ∈ Finset.range (D + N), F d :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun d _ _ => Finset.sum_nonneg (fun j _ => ha j (j + d)))
      _ = (∑ d ∈ Finset.range D, F d) + ∑ d ∈ Finset.range N, F (D + d) :=
        Finset.sum_range_add F D N
      _ ≤ _ := add_le_add hn hfar
  calc
    _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, inner ℝ (T (u j)) (u k) := by
      rw [map_sum, sum_inner]
      simp_rw [inner_sum]
    _ ≤ ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j k :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => le_abs_self _))
    _ ≤ 2 * (∑ d ∈ Finset.range N, F d) := finite_symmetric_sum_le_offset_sum N a ha hasym
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (by norm_num)

end TransposeFollowup
