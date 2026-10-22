import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-! A finite coefficient bound for selecting a pair from one and two
applications of a linear combination of operators. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

theorem bilinear_iterated_sum_bound {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (U : ι → V →ₗ[ℝ] V) (a : ι → ℝ) (L : V → V) (b : V) {C D : ℝ}
    (hC : 0 ≤ C) (ha : ∀ i, |a i| ≤ C)
    (hL : ∀ x, L x = ∑ i, a i • U i x)
    (hB : ∀ i j k, |B (U i b) (U j (U k b))| ≤ D) :
    |B (L b) (L (L b))| ≤ (Fintype.card ι : ℝ) ^ 3 * C ^ 3 * D := by
  have he : B (L b) (L (L b)) =
      ∑ i, ∑ j, ∑ k, a i * a j * a k * B (U k b) (U i (U j b)) := by
    rw [hL (L b), hL b]
    simp only [map_sum, map_smul, LinearMap.smul_apply,
      LinearMap.sum_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  calc
    _ ≤ ∑ _i : ι, ∑ _j : ι, ∑ _k : ι, C ^ 3 * D := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      simp only [abs_mul]
      have hh : |a i| * |a j| * |a k| ≤ C ^ 3 := by
        calc
          _ ≤ C * C * C := by gcongr <;> apply ha
          _ = _ := by ring
      exact mul_le_mul hh (hB k i j) (abs_nonneg _) (by positivity)
    _ = _ := by simp; ring

end TransposeFollowup
