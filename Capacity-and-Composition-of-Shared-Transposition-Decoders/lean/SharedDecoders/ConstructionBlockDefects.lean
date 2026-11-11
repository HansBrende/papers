import SharedDecoders.CapacityOptimization
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Unequal rectangular blocks with actual diagonal-kernel defects

The summands may have different dimensions. Coefficients may involve later
columns, so this also covers upper triangular, not just diagonal, block
actions. The restriction and its injectivity are constructed explicitly.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

abbrev UpperBlocks (m : ℕ) := {ij : Fin m × Fin m // ij.1 < ij.2}

variable {F : Type*} [Field F] {m : ℕ}
variable (V : Fin m → Fin m → Type*) [∀ i j, AddCommGroup (V i j)]
  [∀ i j, Module F (V i j)]
variable (S : ∀ i j, V i j ≃ₗ[F] V j i)
  (L : ∀ j i a b, V a b →ₗ[F] V i j)

def upperBlockAgreement : Submodule F (∀ i j, V i j) where
  carrier := {X | ∀ j i, S j i (X j i) = ∑ a, ∑ b, L j i a b (X a b)}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY j i
    simpa only [Pi.add_apply, map_add, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) (hX j i) (hY j i)
  smul_mem' := by
    intro c X hX j i
    simpa only [Pi.smul_apply, map_smul, ← Finset.smul_sum] using
      congrArg (c • ·) (hX j i)

def upperDiagonalKernel (j : Fin m) : Submodule F (V j j) :=
  LinearMap.ker ((S j j).toLinearMap - L j j j j)

noncomputable def upperBlockDescriptor : upperBlockAgreement V S L →ₗ[F]
    ((∀ ij : UpperBlocks m, V ij.1.1 ij.1.2) × (∀ j, upperDiagonalKernel V S L j)) where
  toFun X := (fun ij => X.1 ij.1.1 ij.1.2,
    fun j => (upperDiagonalKernel V S L j).subtype.leftInverse (X.1 j j))
  map_add' X Y := by
    apply Prod.ext
    · rfl
    · funext j; exact map_add _ _ _
  map_smul' c X := by
    apply Prod.ext
    · rfl
    · funext j; exact map_smul _ _ _

theorem upperBlockDescriptor_injective
    (hupper : ∀ j i a b, b < j → L j i a b = 0) :
    Function.Injective (upperBlockDescriptor V S L) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro X hX
  have hup (a b : Fin m) (hab : a < b) : X.1 a b = 0 :=
    congrFun (congrArg Prod.fst hX) ⟨(a,b), hab⟩
  have hdiag (j : Fin m) :
      (upperDiagonalKernel V S L j).subtype.leftInverse (X.1 j j) = 0 :=
    congrFun (congrArg Prod.snd hX) j
  have key : ∀ n : ℕ, ∀ j : Fin m, m ≤ j.val + n → ∀ i, X.1 j i = 0 := by
    intro n
    induction n with
    | zero => intro j hj; have := j.isLt; omega
    | succ n ih =>
      intro j hj
      have hterm (i a b : Fin m) (hne : a ≠ j ∨ b ≠ j) : L j i a b (X.1 a b) = 0 := by
        by_cases hbj : b < j
        · rw [hupper j i a b hbj, LinearMap.zero_apply]
        · by_cases hab : a < b
          · rw [hup a b hab, map_zero]
          · have hja : j.val < a.val := by
              have hneval : a.val ≠ j.val ∨ b.val ≠ j.val := by
                rcases hne with ha | hb
                · exact Or.inl (fun hh => ha (Fin.ext hh))
                · exact Or.inr (fun hh => hb (Fin.ext hh))
              omega
            rw [ih a (by omega) b, map_zero]
      have hsum (i : Fin m) : (∑ a, ∑ b, L j i a b (X.1 a b)) = L j i j j (X.1 j j) := by
        rw [Finset.sum_eq_single j]
        · apply Finset.sum_eq_single j
          · intro b _ hb
            exact hterm i j b (Or.inr hb)
          · simp
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro b _
          exact hterm i a b (Or.inl ha)
        · simp
      have hmem : X.1 j j ∈ upperDiagonalKernel V S L j := by
        apply LinearMap.mem_ker.mpr
        change S j j (X.1 j j) - L j j j j (X.1 j j) = 0
        rw [X.2 j j, hsum, sub_self]
      have hjj : X.1 j j = 0 := by
        have hid := LinearMap.leftInverse_apply_of_inj
          (upperDiagonalKernel V S L j).ker_subtype
          (⟨X.1 j j, hmem⟩ : upperDiagonalKernel V S L j)
        have hz : (⟨X.1 j j, hmem⟩ : upperDiagonalKernel V S L j) = 0 :=
          hid.symm.trans (hdiag j)
        exact congrArg Subtype.val hz
      intro i
      apply (S j i).injective
      rw [map_zero, X.2 j i, hsum, hjj, map_zero]
  apply Subtype.ext
  funext j i
  exact key m j (by omega) i

theorem finrank_upperBlockAgreement_le [∀ i j, FiniteDimensional F (V i j)]
    (hupper : ∀ j i a b, b < j → L j i a b = 0) :
    finrank F (upperBlockAgreement V S L) ≤
      (∑ ij : UpperBlocks m, finrank F (V ij.1.1 ij.1.2)) +
        ∑ j, finrank F (upperDiagonalKernel V S L j) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (upperBlockDescriptor_injective V S L hupper)
  simpa only [Module.finrank_prod, Module.finrank_pi_fintype] using h

end SharedDecoders
