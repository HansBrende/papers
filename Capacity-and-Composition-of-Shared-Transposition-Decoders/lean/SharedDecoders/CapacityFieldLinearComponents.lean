import SharedDecoders.CapacityIntervalsField
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Frobenius components of an actual binary-linear decoder

The scalar test `a ↦ f (a • x)` is expanded in the basis of field
automorphisms.  Untwisting each coefficient gives an extension-linear
functional of `x`.  No extension-linearity of `f` is assumed.
-/

namespace SharedDecoders.CapacityFieldLinear

open Module CapacityIntervals
open scoped BigOperators

variable (d : ℕ) [NeZero d]

noncomputable def phaseBasis : Basis (ZMod d) (Extension d)
    (Extension d →ₗ[Bit] Extension d) :=
  basisOfLinearIndependentOfCardEqFinrank
    ((linearIndependent_algHom_toLinearMap Bit (Extension d) (Extension d)).comp
      (fun s => (phase d s).toAlgHom) (by
        intro s t h
        apply phase_injective d
        exact AlgEquiv.coe_toAlgHom_injective h))
    (by rw [ZMod.card, Module.finrank_linearMap_self, extension_finrank])

@[simp] theorem phaseBasis_apply (s : ZMod d) :
    phaseBasis d s = (phase d s).toLinearMap := by
  simp only [phaseBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

variable {V : Type*} [AddCommGroup V] [Module (Extension d) V]
  [Module Bit V] [IsScalarTower Bit (Extension d) V]

noncomputable def scalarTest (f : V →ₗ[Bit] Extension d) (x : V) :
    Extension d →ₗ[Bit] Extension d where
  toFun a := f (a • x)
  map_add' a b := by rw [add_smul, map_add]
  map_smul' a b := by rw [smul_assoc, map_smul]; rfl

omit [NeZero d] in
@[simp] theorem scalarTest_apply (f : V →ₗ[Bit] Extension d) (x : V)
    (a : Extension d) : scalarTest d f x a = f (a • x) := rfl

omit [NeZero d] in
theorem scalarTest_add (f : V →ₗ[Bit] Extension d) (x y : V) :
    scalarTest d f (x+y) = scalarTest d f x + scalarTest d f y := by
  ext a
  simp [scalarTest, smul_add]

theorem scalarTest_smul_repr (f : V →ₗ[Bit] Extension d) (x : V)
    (a : Extension d) (s : ZMod d) :
    (phaseBasis d).repr (scalarTest d f (a • x)) s =
      (phaseBasis d).repr (scalarTest d f x) s * phase d s a := by
  have hex : scalarTest d f (a • x) =
      ∑ t : ZMod d,
        ((phaseBasis d).repr (scalarTest d f x) t * phase d t a) • phaseBasis d t := by
    ext z
    have h := congrArg (fun g : Extension d →ₗ[Bit] Extension d => g (z*a))
      ((phaseBasis d).sum_repr (scalarTest d f x))
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, phaseBasis_apply,
      AlgEquiv.toLinearMap_apply, smul_eq_mul, map_mul, scalarTest_apply] at h ⊢
    rw [smul_smul]
    rw [← h]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hex, Basis.repr_sum_self]

/-- The Frobenius coefficient, untwisted into an extension-linear functional. -/
noncomputable def component (f : V →ₗ[Bit] Extension d) (s : ZMod d) :
    V →ₗ[Extension d] Extension d where
  toFun x := (phase d s).symm ((phaseBasis d).repr (scalarTest d f x) s)
  map_add' x y := by
    rw [scalarTest_add, map_add]
    simp only [Finsupp.add_apply, map_add]
  map_smul' a x := by
    rw [scalarTest_smul_repr]
    simp only [map_mul, AlgEquiv.symm_apply_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_comm]

theorem component_of_scalarTest (f : V →ₗ[Bit] Extension d) (x : V)
    (t : ZMod d) (z : Extension d)
    (h : ∀ a, f (a • x) = phase d t a * z) (s : ZMod d) :
    component d f s x = if s=t then (phase d s).symm z else 0 := by
  classical
  have he : scalarTest d f x = z • phaseBasis d t := by
    ext a
    simp only [scalarTest_apply, phaseBasis_apply, LinearMap.smul_apply,
      AlgEquiv.toLinearMap_apply, smul_eq_mul, h]
    rw [mul_comm]
  change (phase d s).symm ((phaseBasis d).repr (scalarTest d f x) s) = _
  rw [he, map_smul, Basis.repr_self]
  by_cases hs : s=t
  · subst t
    simp
  · simp [hs]

theorem component_zero_of_scalarTest_zero (f : V →ₗ[Bit] Extension d) (x : V)
    (h : ∀ a : Extension d, f (a • x) = 0) (s : ZMod d) : component d f s x = 0 := by
  have he : scalarTest d f x = 0 := by ext a; exact h a
  simp [component, he]

theorem sum_components (f : V →ₗ[Bit] Extension d) (x : V) :
    f x = ∑ s : ZMod d, phase d s (component d f s x) := by
  have hh := congrArg (fun g : Extension d →ₗ[Bit] Extension d => g 1)
    ((phaseBasis d).sum_repr (scalarTest d f x))
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, phaseBasis_apply,
    AlgEquiv.toLinearMap_apply, map_one, smul_eq_mul, mul_one,
    scalarTest_apply, one_smul] at hh
  change f x = ∑ s : ZMod d, phase d s ((phase d s).symm
    ((phaseBasis d).repr (scalarTest d f x) s))
  simpa only [AlgEquiv.apply_symm_apply] using hh.symm

theorem components_unique (f : V →ₗ[Bit] Extension d)
    (g : ZMod d → V →ₗ[Extension d] Extension d)
    (hg : ∀ x, f x = ∑ s : ZMod d, phase d s (g s x)) (s : ZMod d) :
    component d f s = g s := by
  ext x
  have he : scalarTest d f x = ∑ t : ZMod d, phase d t (g t x) • phaseBasis d t := by
    ext a
    simp only [scalarTest_apply, hg, map_smul, smul_eq_mul, map_mul,
      LinearMap.sum_apply, LinearMap.smul_apply, phaseBasis_apply,
      AlgEquiv.toLinearMap_apply]
    apply Finset.sum_congr rfl
    intro t _
    ring
  change (phase d s).symm ((phaseBasis d).repr (scalarTest d f x) s)=g s x
  rw [he, Basis.repr_sum_self, AlgEquiv.symm_apply_apply]

end SharedDecoders.CapacityFieldLinear
