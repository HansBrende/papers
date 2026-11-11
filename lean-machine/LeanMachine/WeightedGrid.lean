import LeanMachine.ShiftedGrid
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! One shift pays all nonnegative interval charges simultaneously. The exact
capped separation count is retained, so long spans are never overcounted. -/

namespace LeanMachine.ShiftedGrid

open Finset
open scoped BigOperators

noncomputable def weightedCharge {I : Type*} (items : Finset I)
    (lo hi : I → ℕ) (cost : I → ℝ) (g θ : ℕ) : ℝ :=
  ∑ i ∈ items, if label g θ (lo i) ≠ label g θ (hi i) then cost i else 0

theorem sum_weightedCharge {I : Type*} (items : Finset I)
    (lo hi : I → ℕ) (cost : I → ℝ) (g : ℕ) (hg : 0 < g)
    (horder : ∀ i ∈ items, lo i ≤ hi i) :
    (∑ θ ∈ range g, weightedCharge items lo hi cost g θ) =
      ∑ i ∈ items, (min g (hi i - lo i) : ℕ) * cost i := by
  classical
  unfold weightedCharge
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi'
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  rw [show ((range g).filter (fun θ => label g θ (lo i) ≠ label g θ (hi i))).card =
      min g (hi i - lo i) from separatingShifts_card hg (horder i hi')]

/-- The same shift controls every included charge; there is no separate
choice for resident switches and exported versions. -/
theorem exists_weightedCharge_le {I : Type*} (items : Finset I)
    (lo hi : I → ℕ) (cost : I → ℝ) (g : ℕ) (hg : 0 < g)
    (horder : ∀ i ∈ items, lo i ≤ hi i) (hcost : ∀ i ∈ items, 0 ≤ cost i) :
    ∃ θ < g, weightedCharge items lo hi cost g θ ≤
      (∑ i ∈ items, (hi i - lo i : ℕ) * cost i) / g := by
  have hs : (∑ θ ∈ range g, weightedCharge items lo hi cost g θ) ≤
      ∑ i ∈ items, (hi i - lo i : ℕ) * cost i := by
    rw [sum_weightedCharge items lo hi cost g hg horder]
    apply sum_le_sum
    intro i hi'
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right g (hi i - lo i))
      (hcost i hi')
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  by_contra hn
  have hall : ∀ θ ∈ range g,
      (∑ i ∈ items, (hi i - lo i : ℕ) * cost i) / g <
        weightedCharge items lo hi cost g θ := by
    intro θ hθ
    exact lt_of_not_ge (fun h => hn ⟨θ, mem_range.mp hθ, h⟩)
  have hh := sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hg.ne') hall
  simp only [sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ hgr.ne'] at hh
  exact hh.not_ge hs

end LeanMachine.ShiftedGrid
