import TransposeFollowup.DyadicSchwartzDilation
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Order.Interval.Finset.Nat

/-! Closed dyadic annuli [2^j,2^(j+2)] have overlap at most three.
This includes the boundary points needed for derivative supports. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

theorem dyadic_annulus_card_le_three (s : Finset ℕ) (x : ℝ) :
    (s.filter (fun j => (2 : ℝ) ^ j ≤ |x| ∧ |x| ≤ (2 : ℝ) ^ (j + 2))).card ≤ 3 := by
  classical
  let t := s.filter (fun j => (2 : ℝ) ^ j ≤ |x| ∧ |x| ≤ (2 : ℝ) ^ (j + 2))
  change t.card ≤ 3
  by_cases ht : t.Nonempty
  · let m := t.min' ht
    have hm : |x| ≤ (2 : ℝ) ^ (m + 2) := (Finset.mem_filter.mp (t.min'_mem ht)).2.2
    have hsub : t ⊆ Finset.Icc m (m + 2) := by
      intro j hj
      apply Finset.mem_Icc.mpr
      refine ⟨t.min'_le j hj, ?_⟩
      exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
        ((Finset.mem_filter.mp hj).2.1.trans hm)
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp ht, Finset.card_empty, Nat.zero_le]

theorem dyadic_annulus_sum_le_three (s : Finset ℕ) (x : ℝ) (a : ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ j ∈ s, a j ≤ M)
    (hsupport : ∀ j ∈ s, a j ≠ 0 → (2 : ℝ) ^ j ≤ |x| ∧ |x| ≤ (2 : ℝ) ^ (j + 2)) :
    (∑ j ∈ s, a j) ≤ 3 * M := by
  classical
  let t := s.filter (fun j => (2 : ℝ) ^ j ≤ |x| ∧ |x| ≤ (2 : ℝ) ^ (j + 2))
  have he : (∑ j ∈ s, a j) = ∑ j ∈ t, a j := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro j hj hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hj, hsupport j hj hne⟩)
  rw [he]
  calc
    _ ≤ ∑ _j ∈ t, M := Finset.sum_le_sum (fun j hj => hbound j (Finset.mem_filter.mp hj).1)
    _ = (t.card : ℝ) * M := by simp
    _ ≤ 3 * M := by
      have hcard : t.card ≤ 3 := dyadic_annulus_card_le_three s x
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM

theorem iteratedDeriv_tsupport_subset (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, subset_refl]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem schwartz_annular_derivative_support (u : 𝓢(ℝ, ℂ))
    (hu : tsupport (⇑u) ⊆ {x : ℝ | 1 ≤ |x| ∧ |x| ≤ 4}) (j n : ℕ) {x : ℝ}
    (hx : iteratedDeriv n (schwartzDyadicDilate u j) x ≠ 0) :
    (2 : ℝ) ^ j ≤ |x| ∧ |x| ≤ (2 : ℝ) ^ (j + 2) := by
  have hn : iteratedDeriv n u (((2 : ℝ) ^ j)⁻¹ * x) ≠ 0 := by
    intro hzero
    apply hx
    rw [schwartzDyadicDilate_iteratedDeriv, hzero, smul_zero]
  have hs := hu ((iteratedDeriv_tsupport_subset u n) (subset_tsupport _ (by exact hn)))
  change 1 ≤ |((2 : ℝ) ^ j)⁻¹ * x| ∧ |((2 : ℝ) ^ j)⁻¹ * x| ≤ 4 at hs
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  rw [abs_mul, abs_inv, abs_of_pos hp] at hs
  have h1 := mul_le_mul_of_nonneg_left hs.1 hp.le
  have h2 := mul_le_mul_of_nonneg_left hs.2 hp.le
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul, mul_one] at h1
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] at h2
  refine ⟨h1, ?_⟩
  simpa only [pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num] using h2

end TransposeFollowup
