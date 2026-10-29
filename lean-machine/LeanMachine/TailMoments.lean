import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Tail floors obstruct finite moments

A summable majorant controls every scaled tail. Applied to polynomial
weights, this shows that a positive eventual floor on the scaled tail
forces divergence of the corresponding moment, including moment zero.
-/

namespace LeanMachine.TailMoments

open Filter
open scoped BigOperators Topology

/-- A nonnegative decreasing summable sequence is little-o of reciprocal
rank. Compare a late coordinate with any fixed sufficiently small tail. -/
theorem rank_mul_tendsto_zero {h : ℕ → ℝ}
    (h0 : ∀ i, 0 ≤ h i) (hanti : Antitone h) (hs : Summable h) :
    Tendsto (fun J : ℕ => (J + 1 : ℝ) * h J) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun J => ha.trans_le (mul_nonneg (by positivity) (h0 J))
  · intro ε hε
    obtain ⟨R, hR⟩ := ((tendsto_sum_nat_add h).eventually
      (Iio_mem_nhds (half_pos hε))).exists
    apply eventually_atTop.2 ⟨2 * R, fun J hJ => ?_⟩
    have hsum : ((J + 1 - R : ℕ) : ℝ) * h J ≤ ∑' i, h (i + R) := by
      calc
        _ = ∑ i ∈ Finset.range (J + 1 - R), h J := by simp
        _ ≤ ∑ i ∈ Finset.range (J + 1 - R), h (i + R) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hanti (by have := Finset.mem_range.mp hi; omega)
        _ ≤ _ := ((summable_nat_add_iff R).mpr hs).sum_le_tsum _ (fun i _ => h0 (i + R))
    have hrank : (J + 1 : ℝ) ≤ 2 * ((J + 1 - R : ℕ) : ℝ) := by
      exact_mod_cast (show J + 1 ≤ 2 * (J + 1 - R) by omega)
    have := mul_le_mul_of_nonneg_right hrank (h0 J)
    linarith

/-- Compare each scaled tail term with the corresponding term of one
summable sequence. No monotonicity of either sequence is needed. -/
theorem scaled_tail_tendsto_zero {h g a : ℕ → ℝ}
    (h0 : ∀ i, 0 ≤ h i) (ha0 : ∀ R, 0 ≤ a R) (hg : Summable g)
    (hbound : ∀ R i, a R * h (i + R) ≤ g (i + R)) :
    Tendsto (fun R => a R * ∑' i, h (i + R)) atTop (𝓝 0) := by
  refine squeeze_zero
    (fun R => mul_nonneg (ha0 R) (tsum_nonneg fun i => h0 (i + R)))
    (fun R => ?_) (tendsto_sum_nat_add g)
  rw [← tsum_mul_left]
  have hgR := (summable_nat_add_iff R).mpr hg
  exact (Summable.of_nonneg_of_le
    (fun i => mul_nonneg (ha0 R) (h0 (i + R))) (hbound R) hgR).tsum_le_tsum
    (hbound R) hgR

/-- A finite `p`-th moment makes every fixed nonnegative polynomial shift
of the tail tend to zero. Summability of `h` need not be assumed separately. -/
theorem polynomial_tail_tendsto_zero {h : ℕ → ℝ} (p : ℕ) (shift : ℝ)
    (hshift : 0 ≤ shift) (h0 : ∀ i, 0 ≤ h i)
    (hm : Summable (fun i : ℕ => (i + 1 : ℝ) ^ p * h i)) :
    Tendsto (fun R : ℕ => (R + shift : ℝ) ^ p * ∑' i, h (i + R))
      atTop (𝓝 0) := by
  apply scaled_tail_tendsto_zero h0
    (fun R => pow_nonneg (add_nonneg (Nat.cast_nonneg R) hshift) p)
    (hm.mul_left ((shift + 1) ^ p))
  intro R i
  calc
    (R + shift : ℝ) ^ p * h (i + R) ≤
        ((shift + 1) * ((i + R : ℕ) + 1 : ℝ)) ^ p * h (i + R) := by
      apply mul_le_mul_of_nonneg_right _ (h0 (i + R))
      apply pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg R) hshift)
      simp only [Nat.cast_add]
      nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i),
        mul_nonneg hshift (add_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg R))]
    _ = (shift + 1) ^ p * (((i + R : ℕ) + 1 : ℝ) ^ p * h (i + R)) := by
      rw [mul_pow, mul_assoc]

/-- An eventual positive floor on a polynomially scaled tail rules out
summability of the matching moment. This includes `p = 0`. -/
theorem not_summable_moment_of_tail_floor {h : ℕ → ℝ} (p : ℕ) (shift : ℝ)
    (hshift : 0 ≤ shift) (h0 : ∀ i, 0 ≤ h i) {A : ℝ} (hA : 0 < A)
    (hfloor : ∀ᶠ R : ℕ in atTop,
      A ≤ (R + shift : ℝ) ^ p * ∑' i, h (i + R)) :
    ¬ Summable (fun i : ℕ => (i + 1 : ℝ) ^ p * h i) := by
  intro hm
  exact (not_le_of_gt hA)
    (ge_of_tendsto (polynomial_tail_tendsto_zero p shift hshift h0 hm) hfloor)

end LeanMachine.TailMoments
