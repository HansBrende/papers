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
