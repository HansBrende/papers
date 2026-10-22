import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A nonnegative symmetric finite matrix is bounded by twice an
overcount of its upper diagonals. Extra indices contribute nonnegative terms. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

theorem finite_upper_row_le_offset_sum (N j : ℕ) (a : ℕ → ℕ → ℝ)
    (ha : ∀ j k, 0 ≤ a j k) :
    (∑ k ∈ Finset.range N, if j ≤ k then a j k else 0) ≤
      ∑ r ∈ Finset.range N, a j (j + r) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_injOn (fun k => k - j)
  · intro k hk l hl he
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk hl
    change k - j = l - j at he
    omega
  · intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_range.mpr (by omega)
  · intro k hk
    have hjk := (Finset.mem_filter.mp hk).2
    simp only [Nat.add_sub_of_le hjk, le_refl]
  · intro r _ _
    exact ha j (j + r)

theorem finite_symmetric_sum_le_offset_sum (N : ℕ) (a : ℕ → ℕ → ℝ)
    (ha : ∀ j k, 0 ≤ a j k) (hsym : ∀ j k, a j k = a k j) :
    (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j k) ≤
      2 * (∑ r ∈ Finset.range N, ∑ j ∈ Finset.range N, a j (j + r)) := by
  have hpoint (j k : ℕ) : a j k ≤
      (if j ≤ k then a j k else 0) + (if k ≤ j then a k j else 0) := by
    by_cases hjk : j ≤ k
    · rw [ite_eq_left hjk]
      split_ifs
      · linarith [ha k j]
      · simp only [add_zero, le_refl]
    · have hkj : k ≤ j := by omega
      simp only [ite_eq_right hjk, ite_eq_left hkj, zero_add, hsym j k, le_refl]
  calc
    _ ≤ ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ((if j ≤ k then a j k else 0) + (if k ≤ j then a k j else 0)) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hpoint j k))
    _ = 2 * (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        if j ≤ k then a j k else 0) := by
      simp_rw [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun j k => if k ≤ j then a k j else 0)]
      ring
    _ ≤ 2 * (∑ j ∈ Finset.range N, ∑ r ∈ Finset.range N, a j (j + r)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
        finite_upper_row_le_offset_sum N j a ha)) (by norm_num)
    _ = _ := by rw [Finset.sum_comm]

end TransposeFollowup
