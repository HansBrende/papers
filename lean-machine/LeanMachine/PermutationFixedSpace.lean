import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Fixed coordinate functions and Burnside's formula

Invariants of a permutation action are functions on its orbits. Counting these
orbits uses Burnside's lemma and works in every characteristic, including when
the characteristic divides the group order.
-/

namespace LeanMachine.PermutationFixedSpace

open Module MulAction

variable {F A G Y : Type*} [Field F] [AddCommGroup A] [Module F A]
  [Group G] [MulAction G Y]

def invariants : Submodule F (Y → A) where
  carrier := {f | ∀ g : G, ∀ y, f (g • y) = f y}
  zero_mem' := fun _ _ => rfl
  add_mem' := by intro f h hf hh g y; exact congrArg₂ (· + ·) (hf g y) (hh g y)
  smul_mem' := by intro a f hf g y; exact congrArg (a • ·) (hf g y)

noncomputable def orbitEquiv : invariants (F := F) (A := A) (G := G) (Y := Y) ≃ₗ[F]
    (MulAction.orbitRel.Quotient G Y → A) where
  toFun f := Quotient.lift f.val (by
    intro x y hxy
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hxy
    exact f.property g y)
  invFun f := ⟨fun y => f ⟦y⟧, by
    intro g y
    exact congrArg f (Quotient.sound (MulAction.mem_orbit y g))⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by
    funext o
    induction o using Quotient.inductionOn
    rfl
  map_add' f h := by
    funext o
    induction o using Quotient.inductionOn
    rfl
  map_smul' a f := by
    funext o
    induction o using Quotient.inductionOn
    rfl

theorem finrank_invariants [Fintype Y] [FiniteDimensional F A] :
    finrank F (invariants (F := F) (A := A) (G := G) (Y := Y)) =
      Nat.card (MulAction.orbitRel.Quotient G Y) * finrank F A := by
  classical
  let _ : Fintype (MulAction.orbitRel.Quotient G Y) := Fintype.ofFinite _
  rw [orbitEquiv.finrank_eq]
  simp [Module.finrank_pi_fintype, Nat.card_eq_fintype_card]

/-- A characteristic-free dimension identity for permutation invariants. -/
theorem card_mul_finrank_invariants [Fintype G] [Fintype Y] [FiniteDimensional F A] :
    Fintype.card G * finrank F (invariants (F := F) (A := A) (G := G) (Y := Y)) =
      (∑ g : G, Nat.card (MulAction.fixedBy Y g)) * finrank F A := by
  classical
  let _ : Fintype (MulAction.orbitRel.Quotient G Y) := Fintype.ofFinite _
  let _ (g : G) : Fintype (MulAction.fixedBy Y g) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G Y
  rw [finrank_invariants]
  simp only [Nat.card_eq_fintype_card]
  rw [h]
  ac_rfl

end LeanMachine.PermutationFixedSpace
