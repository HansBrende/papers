import Mathlib

/-! # Literal coordinate fibres of a finite product -/

namespace LeanMachine.FiniteCoordinateFibres

open Finset

theorem card_le_complement {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]
    (D : Finset (I → A)) (S : Finset I)
    (hagree : ∀ x ∈ D, ∀ y ∈ D, ∀ i ∈ S, x i = y i) :
    D.card ≤ Fintype.card A ^ (Fintype.card I - S.card) := by
  classical
  let encode : D → (↑(Sᶜ) → A) := fun x i => x.val i.val
  have hinj : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · exact hagree x x.property y y.property i hi
    · exact congr_fun he ⟨i, mem_compl.mpr hi⟩
  simpa only [Fintype.card_coe, Fintype.card_fun, card_compl] using
    Fintype.card_le_of_injective encode hinj

end LeanMachine.FiniteCoordinateFibres
