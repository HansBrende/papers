import SharedDecoders.CapacityTP
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.Group.Nat.Even

/-! # Symmetric arrays with vector entries, in every characteristic

This is the unordered-pair parametrization of `SwapRigidity.Swap`, with an
arbitrary finite-dimensional entry module instead of one scalar entry.
-/

namespace SharedDecoders

open Module

variable {F A I : Type*} [Field F] [AddCommGroup A] [Module F A]

def symmetricSpace : Submodule F (I → I → A) where
  carrier := {X | ∀ i j, X i j = X j i}
  zero_mem' := by intro i j; rfl
  add_mem' := by
    intro X Y hX hY i j
    exact congrArg₂ (· + ·) (hX i j) (hY i j)
  smul_mem' := by
    intro a X hX i j
    exact congrArg (a • ·) (hX i j)

noncomputable def symmetricEquiv : symmetricSpace (F := F) (A := A) (I := I) ≃ₗ[F]
    (Sym2 I → A) where
  toFun X := Sym2.lift ⟨fun i j => (X : I → I → A) i j, X.2⟩
  invFun f := ⟨fun i j => f s(i, j), by intro i j; change f s(i, j) = f s(j, i); rw [Sym2.eq_swap]⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv f := by
    funext z
    induction z using Sym2.ind with
    | _ i j => rfl
  map_add' X Y := by
    funext z
    induction z using Sym2.ind with
    | _ i j => rfl
  map_smul' a X := by
    funext z
    induction z using Sym2.ind with
    | _ i j => rfl

variable [Fintype I] [FiniteDimensional F A]

theorem finrank_symmetricSpace :
    finrank F (symmetricSpace (F := F) (A := A) (I := I)) =
      Fintype.card (Sym2 I) * finrank F A := by
  rw [(symmetricEquiv (F := F) (A := A) (I := I)).finrank_eq]
  simp [Module.finrank_pi_fintype]

theorem two_mul_finrank_symmetricSpace :
    2 * finrank F (symmetricSpace (F := F) (A := A) (I := I)) =
      Fintype.card I * (Fintype.card I + 1) * finrank F A := by
  have hc : 2 * Fintype.card (Sym2 I) = Fintype.card I * (Fintype.card I + 1) := by
    rw [Sym2.card, Nat.choose_two_right,
      Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self _), Nat.add_sub_cancel, mul_comm]
  rw [finrank_symmetricSpace, ← mul_assoc, hc]

end SharedDecoders
