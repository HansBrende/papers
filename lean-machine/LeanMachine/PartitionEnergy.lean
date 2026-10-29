import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Weighted partition energy

Energy is the sum of squared fibre masses, equivalently the mass of ordered
pairs with equal labels. Preserving equal labels outside a paid set limits
the energy loss by the mass of pairs touching that set. Weights may vanish.
-/

namespace LeanMachine.PartitionEnergy

open Finset
open scoped BigOperators
noncomputable section

variable {α β γ : Type*}

def energy (V : Finset α) (w : α → ℝ) (c : α → β) : ℝ := by
  classical
  exact ∑ x ∈ V, ∑ y ∈ V, if c x = c y then w x * w y else 0

theorem energy_eq_sum_fibers [DecidableEq β]
    (V : Finset α) (w : α → ℝ) (c : α → β) :
    energy V w c = ∑ b ∈ V.image c, (∑ x ∈ V.filter (fun x => c x = b), w x) ^ 2 := by
  classical
  unfold energy
  rw [← sum_fiberwise_of_maps_to (g := c) (t := V.image c)
    (fun x hx => mem_image_of_mem c hx)]
  apply sum_congr rfl
  intro b _
  calc
    _ = ∑ x ∈ V.filter (fun x => c x = b),
        ∑ y ∈ V.filter (fun y => c y = b), w x * w y := by
      apply sum_congr rfl
      intro x hx
      rw [sum_filter]
      apply sum_congr rfl
      intro y _
      simp only [(mem_filter.mp hx).2, eq_comm]
    _ = _ := by rw [← sum_mul_sum, sq]

theorem energy_nonneg (V : Finset α) (w : α → ℝ) (c : α → β) :
    0 ≤ energy V w c := by
  classical
  rw [energy_eq_sum_fibers]
  exact sum_nonneg fun _ _ => sq_nonneg _

/-- Coarsening the label partition can only increase energy. -/
theorem energy_mono (V : Finset α) (w : α → ℝ) (c₀ : α → β) (c₁ : α → γ)
    (hw : ∀ x ∈ V, 0 ≤ w x)
    (h : ∀ x ∈ V, ∀ y ∈ V, c₀ x = c₀ y → c₁ x = c₁ y) :
    energy V w c₀ ≤ energy V w c₁ := by
  classical
  apply sum_le_sum
  intro x hx
  apply sum_le_sum
  intro y hy
  by_cases h₀ : c₀ x = c₀ y
  · simp only [ite_eq_left h₀, ite_eq_left (h x hx y hy h₀), le_refl]
  · simp only [ite_eq_right h₀]
    split_ifs
    · exact mul_nonneg (hw x hx) (hw y hy)
    · rfl

/-- Restricting the weighted domain can only decrease energy. -/
theorem energy_mono_finset {V W : Finset α} (hVW : V ⊆ W)
    (w : α → ℝ) (c : α → β) (hw : ∀ x ∈ W, 0 ≤ w x) :
    energy V w c ≤ energy W w c := by
  classical
  have hn (x : α) (hx : x ∈ W) (y : α) (hy : y ∈ W) :
      0 ≤ if c x = c y then w x * w y else 0 := by
    split_ifs
    · exact mul_nonneg (hw x hx) (hw y hy)
    · rfl
  exact (sum_le_sum (fun x hx => sum_le_sum_of_subset_of_nonneg hVW
    (fun y hy _ => hn x (hVW hx) y hy))).trans
    (sum_le_sum_of_subset_of_nonneg hVW (fun x hx _ => sum_nonneg (hn x hx)))

/-- Retain the exact old energy on unpaid pairs before relaxing their loss
to the full mass of all pairs touching the paid set. -/
theorem energy_loss_le_retained [DecidableEq α] (V U : Finset α) (w : α → ℝ)
    (c₀ : α → β) (c₁ : α → γ) (hw : ∀ x ∈ V, 0 ≤ w x)
    (h : ∀ x ∈ V \ U, ∀ y ∈ V \ U, c₀ x = c₀ y → c₁ x = c₁ y) :
    energy V w c₀ - energy V w c₁ ≤ energy V w c₀ - energy (V \ U) w c₀ := by
  have hm := energy_mono (V \ U) w c₀ c₁ (fun x hx => hw x (mem_sdiff.mp hx).1) h
  have hs := energy_mono_finset (sdiff_subset : V \ U ⊆ V) w c₁ hw
  linarith

/-- If equal labels persist on every unpaid pair, only pairs touching the
paid set can contribute to an energy decrease. -/
theorem energy_loss_le [DecidableEq α] (V U : Finset α) (w : α → ℝ)
    (c₀ : α → β) (c₁ : α → γ) (hw : ∀ x ∈ V, 0 ≤ w x)
    (h : ∀ x ∈ V \ U, ∀ y ∈ V \ U, c₀ x = c₀ y → c₁ x = c₁ y) :
    energy V w c₀ - energy V w c₁ ≤
      (∑ x ∈ V, w x) ^ 2 - (∑ x ∈ V \ U, w x) ^ 2 := by
  classical
  have hp (x : α) (hx : x ∈ V) (y : α) (hy : y ∈ V) :
      (if c₀ x = c₀ y then w x * w y else 0) -
        (if c₁ x = c₁ y then w x * w y else 0) ≤
      w x * w y - (if x ∈ U then 0 else w x) * (if y ∈ U then 0 else w y) := by
    have hprod := mul_nonneg (hw x hx) (hw y hy)
    have hkeep : x ∉ U → y ∉ U → c₀ x = c₀ y → c₁ x = c₁ y :=
      fun hxU hyU => h x (mem_sdiff.mpr ⟨hx, hxU⟩) y (mem_sdiff.mpr ⟨hy, hyU⟩)
    by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U <;>
      by_cases h₀ : c₀ x = c₀ y <;> by_cases h₁ : c₁ x = c₁ y <;>
      simp only [hxU, hyU, h₀, h₁, ite_true, ite_false,
        zero_mul, mul_zero, sub_zero, sub_self] <;>
      first | exact (h₁ (hkeep hxU hyU h₀)).elim | linarith
  have hs := sum_le_sum fun x hx => sum_le_sum fun y hy => hp x hx y hy
  simp only [sum_sub_distrib] at hs
  rw [← sum_mul_sum, ← sum_mul_sum] at hs
  have hzero : (∑ x ∈ V, if x ∈ U then (0 : ℝ) else w x) = ∑ x ∈ V \ U, w x := by
    rw [show V \ U = V.filter (fun x => x ∉ U) by ext x; simp, sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases hx : x ∈ U <;> simp [hx]
  simpa only [← sq, hzero, energy] using hs

/-- The actual paid union mass is charged once, including its quadratic saving. -/
theorem energy_loss_le_paid_mass [DecidableEq α] (V U : Finset α) (w : α → ℝ)
    (c₀ : α → β) (c₁ : α → γ) (hw : ∀ x ∈ V, 0 ≤ w x)
    (h : ∀ x ∈ V \ U, ∀ y ∈ V \ U, c₀ x = c₀ y → c₁ x = c₁ y) :
    energy V w c₀ - energy V w c₁ ≤
      2 * (∑ x ∈ V, w x) * (∑ x ∈ V ∩ U, w x) - (∑ x ∈ V ∩ U, w x) ^ 2 := by
  have hp := sum_inter_add_sum_sdiff V U w
  calc
    _ ≤ (∑ x ∈ V, w x) ^ 2 - (∑ x ∈ V \ U, w x) ^ 2 :=
      energy_loss_le V U w c₀ c₁ hw h
    _ = _ := by rw [← hp]; ring

end
end LeanMachine.PartitionEnergy
