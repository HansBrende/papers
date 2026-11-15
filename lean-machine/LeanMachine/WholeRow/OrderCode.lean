import LeanMachine.WholeRow.OrderAverage
import LeanMachine.OrderedRecovery

/-!
# Cardinality bounds from row orders

No linearity, group structure, or common recovery rule is assumed. The
recovery premise is stated as equality of words so this shared module has
no dependency on any paper's storage-code definition.
-/

namespace LeanMachine.WholeRow.OrderCode

open Finset LiftOrder AcyclicOrder OrderAverage
open scoped BigOperators Classical
noncomputable section

variable {R J A : Type*} [Fintype R] [Fintype J] [Fintype A]
variable (ρ : J → Finset R) (C : Finset (R × J → A))

/-- Any row order gives a valid code-cardinality bound, for every finite alphabet. -/
theorem card_le_order
    (hC : ∀ x ∈ C, ∀ y ∈ C, ∀ j,
      (∀ i ∈ ρ j, ∀ k, x (i, k) = y (i, k)) → ∀ i, x (i, j) = y (i, j))
    (o : R ≃ Fin (Fintype.card R)) :
    C.card ≤ Fintype.card A ^ cost ρ o := by
  let S := rowSet ρ o
  let f : C → (↑(Sᶜ) → A) := fun x v => x.1 v
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply OrderedRecovery.eq_of_wellFounded (fun z : C => z.1) (fun _ : C => ())
      (↑S) (fun v => ↑(rowHelpers ρ v)) _ (measure (fun v : R × J => (o v.1).val)).wf
      (fun v hv u hu _ => ?_) (fun v _ x y _ heq => ?_) rfl
    · intro v hv
      exact congrFun hxy ⟨v, mem_compl.mpr hv⟩
    · have hv' := (mem_filter.mp hv).2
      have hu' := Finset.le_sup (f := fun i => (o i).val + 1)
        ((mem_rowHelpers ρ v u).mp hu)
      change (o u.1).val < (o v.1).val
      omega
    · exact hC x.1 x.2 y.1 y.2 v.2
        (fun i hi k => heq ((mem_rowHelpers ρ v (i, k)).mpr hi)) v.1
  have hsize : (Sᶜ).card = cost ρ o := by
    have hp := rowSet_card_add_cost ρ o
    simp only [card_compl, Fintype.card_prod]
    dsimp [S]
    omega
  simpa only [Fintype.card_coe, Fintype.card_fun, hsize] using Fintype.card_le_of_injective f hf

/-- The finite degree bound without division or logarithms. -/
theorem card_pow_le_degree [Nonempty A]
    (hC : ∀ x ∈ C, ∀ y ∈ C, ∀ j,
      (∀ i ∈ ρ j, ∀ k, x (i, k) = y (i, k)) → ∀ i, x (i, j) = y (i, j))
    (w : ℕ) (hw : ∀ j, (ρ j).card ≤ w) :
    C.card ^ (w + 1) ≤ Fintype.card A ^ (w * Fintype.card J * (Fintype.card R + 1)) := by
  obtain ⟨o, ho⟩ := exists_order_degree_bound ρ w hw
  calc
    _ ≤ (Fintype.card A ^ cost ρ o) ^ (w + 1) := Nat.pow_le_pow_left (card_le_order ρ C hC o) _
    _ = Fintype.card A ^ ((w + 1) * cost ρ o) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right Fintype.card_pos ho

end
end LeanMachine.WholeRow.OrderCode
