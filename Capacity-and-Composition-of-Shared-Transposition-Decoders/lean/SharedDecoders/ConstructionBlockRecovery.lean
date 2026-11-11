import SharedDecoders.ConstructionBlockDefects

/-! # Descending block recovery with actual diagonal-kernel costs

Every diagonal kernel is charged by its own dimension, not by the ambient
block dimension. The proof supplies all strict upper blocks and an extension
of an identity map on each diagonal kernel, and reconstructs rows backwards.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {m : ℕ}

def blockAgreement (S : V ≃ₗ[F] V) (L : Fin m → Fin m → Fin m → (V →ₗ[F] V)) :
    Submodule F (Fin m → Fin m → V) where
  carrier := {X | ∀ j i, S (X j i) = ∑ a, L j i a (X a j)}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY j i
    simpa only [Pi.add_apply, map_add, Finset.sum_add_distrib] using congrArg₂ (· + ·) (hX j i) (hY j i)
  smul_mem' := by
    intro k X hX j i
    simpa only [Pi.smul_apply, map_smul, ← Finset.smul_sum] using congrArg (k • ·) (hX j i)

def diagonalKernel (S : V ≃ₗ[F] V) (L : Fin m → Fin m → Fin m → (V →ₗ[F] V))
    (j : Fin m) : Submodule F V := LinearMap.ker (S.toLinearMap - L j j j)

variable [FiniteDimensional F V]

theorem finrank_blockAgreement_le (S : V ≃ₗ[F] V)
    (L : Fin m → Fin m → Fin m → (V →ₗ[F] V)) :
    finrank F (blockAgreement S L) ≤
      Fintype.card (UpperBlocks m) * finrank F V + ∑ j, finrank F (diagonalKernel S L j) := by
  classical
  let L' : ∀ j i a b : Fin m, V →ₗ[F] V :=
    fun j i a b => if b = j then L j i a else 0
  have h := finrank_upperBlockAgreement_le (fun _ _ => V) (fun _ _ => S) L'
    (by intro j i a b hb; simp [L', ne_of_lt hb])
  have hsum (X : Fin m → Fin m → V) (j i : Fin m) :
      (∑ a, ∑ b, L' j i a b (X a b)) = ∑ a, L j i a (X a j) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single j]
    · simp only [L', ite_eq_left rfl]
    · intro b _ hb
      simp only [L', ite_eq_right hb, LinearMap.zero_apply]
    · simp
  have heq : upperBlockAgreement (fun _ _ => V) (fun _ _ => S) L' =
      blockAgreement S L := by
    ext X
    change (∀ j i, S (X j i) = ∑ a, ∑ b, L' j i a b (X a b)) ↔ _
    simp_rw [hsum]
    rfl
  have hd (j : Fin m) : upperDiagonalKernel (fun _ _ => V) (fun _ _ => S) L' j =
      diagonalKernel S L j := by
    change LinearMap.ker (S.toLinearMap - L' j j j j) = _
    simp only [L', ite_eq_left rfl]
    rfl
  rw [heq] at h
  apply h.trans_eq
  apply congrArg₂ (· + ·)
  · simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  · apply Finset.sum_congr rfl
    intro j _
    exact (LinearEquiv.ofEq _ _ (hd j)).finrank_eq

theorem card_upperBlocks (m : ℕ) : Fintype.card (UpperBlocks m) = ∑ j : Fin m, j.val := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.card_filter]
  simpa [min_eq_right (Nat.le_of_lt j.isLt)] using Fin.card_filter_val_lt (n := m) (m := j.val)

theorem two_mul_card_upperBlocks (m : ℕ) :
    2 * Fintype.card (UpperBlocks m) + m = m * m := by
  rw [card_upperBlocks, Fin.sum_univ_eq_sum_range (fun i : ℕ => i) m]
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; nlinarith

end SharedDecoders
