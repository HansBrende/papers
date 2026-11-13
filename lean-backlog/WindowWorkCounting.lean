import WindowCounting
import WindowConeWindows

/-!
# Actual work-window counts and guard invoices

The native work-predecessor windows are a subset of the encountered labels
already counted on each work tape. Summing over the fixed tape family gives
the bad-window threshold and the exact guard-count invoice.
-/

namespace LeanBacklog.WindowWorkCounting

open Finset BoundedNesting WindowCounting WindowGuards WindowConeWindows
open scoped BigOperators

variable {k : ℕ}

/-- Every actual cross-window work edge has a counted old window label. -/
theorem workWindows_subset_labels (xs : Fin k → ℕ → ℤ) (T h i : ℕ) :
    workWindows xs T h i ⊆
      univ.biUnion (fun j : Fin k => predecessorWindows (xs j) h T i) := by
  classical
  intro a ha
  obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
  obtain ⟨j, z, hz, hlabel⟩ := externalWork_label_witness hu
  exact mem_biUnion.mpr ⟨j, mem_univ _, mem_predecessorWindows.mpr ⟨z, hz, hlabel⟩⟩

/-- Sum of the actual work-predecessor-window counts, with overlap counted
only once in each window. No positivity assumption on the width is needed. -/
theorem sum_workWindows_le (xs : Fin k → ℕ → ℤ) (hx : ∀ j, IsWalk (xs j))
    (T h N : ℕ) :
    (∑ i ∈ range N, (workWindows xs T h i).card) ≤ 3 * k * N := by
  classical
  calc
    (∑ i ∈ range N, (workWindows xs T h i).card)
        ≤ ∑ i ∈ range N, ∑ j : Fin k, (predecessorWindows (xs j) h T i).card := by
      apply sum_le_sum
      intro i _
      exact (card_le_card (workWindows_subset_labels xs T h i)).trans card_biUnion_le
    _ = ∑ j : Fin k, ∑ i ∈ range N, (predecessorWindows (xs j) h T i).card :=
      sum_comm
    _ ≤ ∑ _j : Fin k, 3 * N :=
      sum_le_sum fun j _ => sum_predecessorWindows_le_three_mul (hx j) h T N
    _ = 3 * k * N := by simp; ring

/-- Every bad window contributes at least `M+1` to the actual count. -/
theorem mul_card_badWindows_le (xs : Fin k → ℕ → ℤ) (hx : ∀ j, IsWalk (xs j))
    (T h M : ℕ) :
    (M + 1) * (badWindows xs T h M).card ≤ 3 * k * ((T + h - 1) / h) := by
  classical
  calc
    (M + 1) * (badWindows xs T h M).card
        = ∑ _i ∈ badWindows xs T h M, (M + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ badWindows xs T h M, (workWindows xs T h i).card := by
      apply sum_le_sum
      intro i hi
      exact Nat.succ_le_of_lt (mem_filter.mp hi).2
    _ ≤ ∑ i ∈ range ((T + h - 1) / h), (workWindows xs T h i).card := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; exact Nat.zero_le _)
    _ ≤ 3 * k * ((T + h - 1) / h) := sum_workWindows_le xs hx T h _

/-- The guard invoice used by the real-valued budget estimate. It is valid
also for zero work tapes; positive window width is the only size premise. -/
theorem mul_card_guards_le (xs : Fin k → ℕ → ℤ) (hx : ∀ j, IsWalk (xs j))
    (T h M : ℕ) (hh : 0 < h) :
    (M + 1) * (guards xs T h (badWindows xs T h M)).card ≤
      3 * k * (k + 1) * (((T + h - 1) / h) * h) := by
  calc
    (M + 1) * (guards xs T h (badWindows xs T h M)).card
        ≤ (M + 1) * ((badWindows xs T h M).card * ((k + 1) * h)) :=
      Nat.mul_le_mul_left _ (card_guards_le xs T h _ hh)
    _ = ((M + 1) * (badWindows xs T h M).card) * ((k + 1) * h) := by ring
    _ ≤ (3 * k * ((T + h - 1) / h)) * ((k + 1) * h) :=
      Nat.mul_le_mul_right _ (mul_card_badWindows_le xs hx T h M)
    _ = 3 * k * (k + 1) * (((T + h - 1) / h) * h) := by ring

#print axioms sum_workWindows_le
#print axioms mul_card_badWindows_le
#print axioms mul_card_guards_le

end LeanBacklog.WindowWorkCounting
