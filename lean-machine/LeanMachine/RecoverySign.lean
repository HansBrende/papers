import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Half-dimension bounds from an injective anticommuting map.

The diagonal sign-change criterion of backlog B3 is a special case. The
general result requires neither a diagonal map nor an involution.
-/

namespace LeanMachine.RecoverySign

open Module
open scoped Matrix

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- An injective anticommuting map embeds each eigenspace into the eigenspace
with opposite eigenvalue. -/
theorem finrank_eigenspace_le_neg (f g : Module.End F V)
    (hg : Function.Injective g) (hfg : ∀ x, f (g x) = -g (f x)) (μ : F) :
    finrank F (f.eigenspace μ) ≤ finrank F (f.eigenspace (-μ)) := by
  let e : f.eigenspace μ →ₗ[F] f.eigenspace (-μ) :=
    (g.comp (f.eigenspace μ).subtype).codRestrict _ fun x => by
      rw [Module.End.mem_eigenspace_iff]
      change f (g x) = (-μ) • g x
      rw [hfg, Module.End.mem_eigenspace_iff.mp x.property, map_smul, neg_smul]
  exact LinearMap.finrank_le_finrank_of_injective (f := e) fun x y h =>
    Subtype.ext (hg (congrArg Subtype.val h))

/-- Opposite eigenspaces have equal dimension under an injective
anticommuting map, even without an involution hypothesis. -/
theorem finrank_eigenspace_eq_neg (f g : Module.End F V)
    (hg : Function.Injective g) (hfg : ∀ x, f (g x) = -g (f x)) (μ : F) :
    finrank F (f.eigenspace μ) = finrank F (f.eigenspace (-μ)) := by
  apply le_antisymm (finrank_eigenspace_le_neg f g hg hfg μ)
  have h := finrank_eigenspace_le_neg f g hg hfg (-μ)
  rwa [neg_neg] at h

/-- If an eigenvalue differs from its negative, an injective anticommuting
map forces its eigenspace to occupy at most half the ambient space. -/
theorem two_mul_finrank_eigenspace_le (f g : Module.End F V)
    (hg : Function.Injective g) (hfg : ∀ x, f (g x) = -g (f x))
    (μ : F) (hμ : μ ≠ -μ) :
    2 * finrank F (f.eigenspace μ) ≤ finrank F V := by
  have hi := finrank_eigenspace_eq_neg f g hg hfg μ
  have hd := Submodule.finrank_add_finrank_le_of_disjoint
    (f.eigenspaces_iSupIndep.pairwiseDisjoint hμ)
  omega

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Backlog B3: a diagonal sign change conjugating `M` to `-M` bounds its
fixed space by half the number of coordinates, in characteristic not two. -/
theorem two_mul_finrank_fixed_le_of_sign (h2 : (2 : F) ≠ 0)
    (M : Matrix n n F) (ε : n → F) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hM : Matrix.diagonal ε * M * Matrix.diagonal ε = -M) :
    2 * finrank F (LinearMap.ker (Matrix.mulVecLin (1 - M))) ≤ Fintype.card n := by
  let D := Matrix.diagonal ε
  have hD : D * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      rcases hε i with h | h <;> simp [h]
    · simp [hij]
  have hinj : Function.Injective D.mulVecLin := by
    intro x y h
    have := congrArg (fun z => D *ᵥ z) h
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hD, Matrix.one_mulVec]
      using this
  have hanti : M * D = -(D * M) := by
    have h := congrArg (fun A => D * A) hM
    change D * (D * M * D) = D * (-M) at h
    simpa only [← Matrix.mul_assoc, hD, Matrix.one_mul, Matrix.mul_neg] using h
  have h := two_mul_finrank_eigenspace_le M.mulVecLin D.mulVecLin hinj
    (fun x => by
      change M *ᵥ (D *ᵥ x) = -(D *ᵥ (M *ᵥ x))
      rw [Matrix.mulVec_mulVec, hanti, Matrix.neg_mulVec, Matrix.mulVec_mulVec])
    (1 : F) (by
      intro he
      apply h2
      simpa only [one_add_one_eq_two] using add_eq_zero_iff_eq_neg.mpr he)
  have hk : LinearMap.ker (Matrix.mulVecLin (1 - M)) = Module.End.eigenspace M.mulVecLin 1 := by
    ext x
    simp [LinearMap.mem_ker, sub_eq_zero, eq_comm]
  rw [hk]
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one] using h

end LeanMachine.RecoverySign
