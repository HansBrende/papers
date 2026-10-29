import LeanMachine.FractionalCover

/-! Feasible fractional covers bound the minimum. An ordinary finite cover
is the special case of unit weights on its chosen sets. -/

namespace LeanMachine.FractionalCover

open Classical Finset
open scoped BigOperators ENNReal
noncomputable section

variable {α ι : Type*} [Fintype ι] {S : Finset α} {A : ι → Set α}

theorem value_le_cost {w : ι → ℝ} (hw : Covers S A w) : value S A ≤ cost w :=
  csInf_le ⟨0, by rintro _ ⟨v, hv, rfl⟩; exact cost_nonneg hv⟩ ⟨w, hw, rfl⟩

theorem number_toReal_le_cost {w : ι → ℝ} (hw : Covers S A w) :
    (number S A).toReal ≤ cost w := by
  rw [number_toReal ⟨w, hw⟩]
  exact value_le_cost hw

theorem unit_covers (R : Finset ι) (hcover : ∀ a ∈ S, ∃ i ∈ R, a ∈ A i) :
    Covers S A (fun i => if i ∈ R then 1 else 0) := by
  refine ⟨fun i => by dsimp only; split_ifs <;> norm_num, fun a ha => ?_⟩
  obtain ⟨i, hi, hai⟩ := hcover a ha
  have h := single_le_sum (s := univ) (a := i)
    (f := fun j => if a ∈ A j then (if j ∈ R then (1 : ℝ) else 0) else 0)
    (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
  simpa only [ite_eq_left hai, ite_eq_left hi] using h

/-- Covers may overlap and contain points outside the target; neither the
target nor the chosen covering family needs to be nonempty. -/
theorem number_le_card (R : Finset ι) (hcover : ∀ a ∈ S, ∃ i ∈ R, a ∈ A i) :
    number S A ≠ ⊤ ∧ (number S A).toReal ≤ R.card := by
  have hw := unit_covers R hcover
  refine ⟨(number_ne_top_iff S A).mpr ⟨_, hw⟩, ?_⟩
  simpa [cost] using number_toReal_le_cost hw

end
end LeanMachine.FractionalCover
