import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic

/-! A basis change that fixes one free generator and left-divides all
others by it. Any injectively indexed subfamily avoiding the base remains free. -/
namespace TransposeFollowup.FreeBasisRebase
open Classical
set_option autoImplicit false

variable {ι : Type*} [DecidableEq ι]

def subtractBase (o : ι) : FreeGroup ι →* FreeGroup ι :=
  FreeGroup.lift (fun i => if i = o then FreeGroup.of i else (FreeGroup.of o)⁻¹ * FreeGroup.of i)

def addBase (o : ι) : FreeGroup ι →* FreeGroup ι :=
  FreeGroup.lift (fun i => if i = o then FreeGroup.of i else FreeGroup.of o * FreeGroup.of i)

theorem addBase_comp_subtractBase (o : ι) :
    (addBase o).comp (subtractBase o) = MonoidHom.id (FreeGroup ι) := by
  ext i
  by_cases hi : i = o
  · subst i
    simp [subtractBase, addBase]
  · simp [subtractBase, addBase, hi]

theorem subtractBase_comp_addBase (o : ι) :
    (subtractBase o).comp (addBase o) = MonoidHom.id (FreeGroup ι) := by
  ext i
  by_cases hi : i = o
  · subst i
    simp [subtractBase, addBase]
  · simp [subtractBase, addBase, hi]

def basisChange (o : ι) : FreeGroup ι ≃* FreeGroup ι where
  toFun := subtractBase o
  invFun := addBase o
  left_inv x := DFunLike.congr_fun (addBase_comp_subtractBase o) x
  right_inv x := DFunLike.congr_fun (subtractBase_comp_addBase o) x
  map_mul' := (subtractBase o).map_mul

theorem subtractBase_injective (o : ι) : Function.Injective (subtractBase o) :=
  (basisChange o).injective

theorem translated_subfamily_free {κ G : Type*} [Group G] (a : ι → G)
    (ha : Function.Injective (FreeGroup.lift a)) (o : ι)
    (j : κ → ι) (hj : Function.Injective j) (hjo : ∀ k, j k ≠ o) :
    Function.Injective (FreeGroup.lift (fun k => (a o)⁻¹ * a (j k))) := by
  have he : FreeGroup.lift (fun k => (a o)⁻¹ * a (j k)) =
      (FreeGroup.lift a).comp ((subtractBase o).comp (FreeGroup.map j)) := by
    ext k
    simp [subtractBase, hjo]
  rw [he]
  exact ha.comp ((subtractBase_injective o).comp (FreeGroup.map_injective hj))

end TransposeFollowup.FreeBasisRebase
