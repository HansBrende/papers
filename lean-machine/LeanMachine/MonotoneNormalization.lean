import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! # Parametrizing a coordinatewise monotone curve by its coordinate sum

Surjectivity of the sum suffices: flat segments cause no ambiguity in the
coordinate values. The normalized coordinates are automatically 1-Lipschitz.
-/

namespace LeanMachine.MonotoneNormalization

variable {I : Type*} [Fintype I] (G : I → ℝ → ℝ)

/-- On a coordinatewise monotone curve, ordering the sums orders every coordinate. -/
theorem coordinate_le_of_sum_le (hG : ∀ i, Monotone (G i)) {x y : ℝ}
    (h : (∑ i, G i x) ≤ ∑ i, G i y) (i : I) : G i x ≤ G i y := by
  classical
  by_cases hxy : x ≤ y
  · exact hG i hxy
  · have hyx : y ≤ x := (lt_of_not_ge hxy).le
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => G j x - G j y) (fun j _ => sub_nonneg.mpr (hG j hyx))
      (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib] at hh
    linarith

noncomputable def normalize (h : Function.Surjective (fun t => ∑ i, G i t))
    (i : I) (z : ℝ) : ℝ := G i (Function.surjInv h z)

theorem sum_normalize (h : Function.Surjective (fun t => ∑ i, G i t)) (z : ℝ) :
    (∑ i, normalize G h i z) = z := Function.surjInv_eq h z

theorem monotone_normalize (hG : ∀ i, Monotone (G i))
    (h : Function.Surjective (fun t => ∑ i, G i t)) (i : I) :
    Monotone (normalize G h i) := by
  intro x y hxy
  apply coordinate_le_of_sum_le G hG
  calc
    (∑ j, G j (Function.surjInv h x)) = x := Function.surjInv_eq h x
    _ ≤ y := hxy
    _ = ∑ j, G j (Function.surjInv h y) := (Function.surjInv_eq h y).symm

/-- Normalization preserves every point on the original curve, even when the
parameter chosen for its sum lies elsewhere on a flat segment. -/
theorem normalize_sum (hG : ∀ i, Monotone (G i))
    (h : Function.Surjective (fun t => ∑ i, G i t)) (t : ℝ) (i : I) :
    normalize G h i (∑ j, G j t) = G i t := by
  apply le_antisymm
  · apply coordinate_le_of_sum_le G hG
    exact (Function.surjInv_eq h _).le
  · apply coordinate_le_of_sum_le G hG
    exact (Function.surjInv_eq h _).ge

/-- Normalized coordinate increments are bounded by the total increment. -/
theorem increment_le (hG : ∀ i, Monotone (G i))
    (h : Function.Surjective (fun t => ∑ i, G i t)) {x y : ℝ} (hxy : x ≤ y) (i : I) :
    normalize G h i y - normalize G h i x ≤ y - x := by
  classical
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => normalize G h j y - normalize G h j x)
    (fun j _ => sub_nonneg.mpr (monotone_normalize G hG h j hxy))
    (Finset.mem_univ i)
  simpa only [Finset.sum_sub_distrib, sum_normalize] using hh

theorem lipschitz_normalize (hG : ∀ i, Monotone (G i))
    (h : Function.Surjective (fun t => ∑ i, G i t)) (i : I) :
    LipschitzWith 1 (normalize G h i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (monotone_normalize G hG h i hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith [increment_le G hG h hxy i]
  · rw [abs_of_nonneg (sub_nonneg.mpr (monotone_normalize G hG h i hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact increment_le G hG h hyx i

theorem exists_normalized_curve (hG : ∀ i, Monotone (G i))
    (h : Function.Surjective (fun t => ∑ i, G i t)) :
    ∃ f : I → ℝ → ℝ, (∀ i, Monotone (f i)) ∧ (∀ i, LipschitzWith 1 (f i)) ∧
      (∀ z, (∑ i, f i z) = z) ∧ (∀ t i, f i (∑ j, G j t) = G i t) :=
  ⟨normalize G h, monotone_normalize G hG h, lipschitz_normalize G hG h,
    sum_normalize G h, normalize_sum G hG h⟩

end LeanMachine.MonotoneNormalization
