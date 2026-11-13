import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Choose

/-! A code dimension bound from the spaces available for successive coordinates.
The local constraints need hold only when all earlier coordinates vanish. -/

namespace LeanMachine.SequentialDimension

open Module

variable {F A ι : Type*} [Field F] [AddCommGroup A] [Module F A]
  [FiniteDimensional F A] [Fintype ι] [LinearOrder ι] [WellFoundedLT ι]

/-- Conditional coordinate spaces bound the total dimension. Linear projections
onto those spaces give a jointly injective record, proved by induction in the order. -/
theorem finrank_le_sum_of_prefix (C : Submodule F (ι → A)) (σ : Equiv.Perm ι)
    (S : ι → Submodule F A)
    (hS : ∀ t (x : ι → A), x ∈ C → (∀ u, u < t → x (σ u) = 0) → x (σ t) ∈ S t) :
    finrank F C ≤ ∑ t, finrank F (S t) := by
  classical
  have hi (t : ι) : ∃ g : A →ₗ[F] S t, g.comp (S t).subtype = LinearMap.id :=
    (S t).subtype.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))
  choose g hg using hi
  let f : C →ₗ[F] (∀ t, S t) :=
    { toFun := fun x t => g t (x.val (σ t))
      map_add' := by intro x y; funext t; exact map_add _ _ _
      map_smul' := by intro a x; funext t; exact map_smul _ _ _ }
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hz (t : ι) : x.val (σ t) = 0 := by
      induction t using WellFoundedLT.induction with
      | ind t ih =>
        have ht := hS t x.val x.property ih
        have he := LinearMap.congr_fun (hg t) ⟨x.val (σ t), ht⟩
        have hzero : g t (x.val (σ t)) = 0 := congrFun hx t
        change g t (x.val (σ t)) = ⟨x.val (σ t), ht⟩ at he
        exact (congrArg Subtype.val he).symm.trans (congrArg Subtype.val hzero)
    apply Subtype.ext
    funext i
    simpa using hz (σ.symm i)
  simpa only [Module.finrank_pi_fintype] using
    LinearMap.finrank_le_finrank_of_injective (f := f) hinj

end LeanMachine.SequentialDimension
