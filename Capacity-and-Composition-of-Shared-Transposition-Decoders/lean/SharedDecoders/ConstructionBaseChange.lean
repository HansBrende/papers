import SharedDecoders.CapacityOptimization
import SharedDecoders.CompositionScalarExtension
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-! # Scalar extension of an actual linear shared code

The source is extended by taking the span of its embedded basis. The class
rules are extended from their literal coordinate coefficients. This proves
capacity monotonicity without assuming a scalar-extension simulation.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F E κ : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} [NeZero d]

def scalarFlattenState (F : Type*) [Field F] (d : ℕ) :
    State d F ≃ₗ[F] (ZMod d × ZMod d → F) where
  toFun X ij := X ij.1 ij.2
  invFun X i j := X (i,j)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def embedState (X : State d F) : State d E := fun i j => algebraMap F E (X i j)

noncomputable def extendDecoder (f : State d F →ₗ[F] (ZMod d → F)) :
    State d E →ₗ[E] (ZMod d → E) :=
  (coordinateExtension E (f.comp (scalarFlattenState F d).symm.toLinearMap)).comp
    (scalarFlattenState E d).toLinearMap

theorem extendDecoder_embed (f : State d F →ₗ[F] (ZMod d → F)) (X : State d F) :
    extendDecoder (E := E) f (embedState (E := E) X) = fun r => algebraMap F E (f X r) := by
  change coordinateExtension E _
    (fun ij => algebraMap F E (scalarFlattenState F d X ij)) = _
  rw [coordinateExtension_base]
  rfl

omit [NeZero d] in
theorem embedState_rot (X : State d F) (c : ZMod d) :
    embedState (E := E) (rot c X) = rot c (embedState (E := E) X) := rfl

noncomputable def baseChangedCode (C : Submodule F (State d F)) : Submodule E (State d E) :=
  Submodule.span E (Set.range (fun i => embedState (E := E) ((Module.finBasis F C) i : State d F)))

theorem baseChangedBasis_independent (C : Submodule F (State d F)) :
    LinearIndependent E (fun i => embedState (E := E) ((Module.finBasis F C) i : State d F)) := by
  let v := fun i => scalarFlattenState F d ((Module.finBasis F C) i : State d F)
  have hinj : Function.Injective ((scalarFlattenState F d).toLinearMap.comp C.subtype) :=
    (scalarFlattenState F d).injective.comp Subtype.coe_injective
  have hv : LinearIndependent F v :=
    (Module.finBasis F C).linearIndependent.map'
      ((scalarFlattenState F d).toLinearMap.comp C.subtype) (LinearMap.ker_eq_bot.mpr hinj)
  have he : LinearIndependent E (fun i => algebraMap F E ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  apply LinearIndependent.of_comp (scalarFlattenState E d).toLinearMap
  exact he

theorem finrank_baseChangedCode (C : Submodule F (State d F)) :
    finrank E (baseChangedCode (E := E) C) = finrank F C := by
  rw [baseChangedCode, finrank_span_eq_card (baseChangedBasis_independent C), Fintype.card_fin]

theorem IsLinearSharedCode.baseChangedCode {p : ZMod d → κ}
    {C : Submodule F (State d F)} (hC : IsLinearSharedCode p C) :
    IsLinearSharedCode p (baseChangedCode (E := E) C) := by
  obtain ⟨f, hf⟩ := hC
  refine ⟨fun J => extendDecoder (E := E) (f J), ?_⟩
  intro X hX c
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨i, rfl⟩ := hX
    rw [← embedState_rot, extendDecoder_embed]
    funext r
    exact congrArg (algebraMap F E) (congrFun (hf _ ((Module.finBasis F C) i).property c) r)
  | zero => rw [show rot c (0 : State d E) = 0 from rfl, map_zero]; rfl
  | add X Y _ _ hX hY =>
    change X c + Y c = extendDecoder (E := E) (f (p c)) (rot c X + rot c Y)
    rw [map_add, hX, hY]
  | smul k X _ hX =>
    change k • X c = extendDecoder (E := E) (f (p c)) (k • rot c X)
    rw [map_smul, hX]

theorem linear_capacity_le_scalarExtension (p : ZMod d → κ) :
    dimensionCapacity (IsLinearSharedCode (F := F) (A := F) p) ≤
      dimensionCapacity (IsLinearSharedCode (F := E) (A := E) p) := by
  obtain ⟨C, hC, hdim⟩ := dimensionCapacity_attained
    (IsLinearSharedCode (F := F) (A := F) p) (isLinearSharedCode_bot p)
  have hh := le_dimensionCapacity (hC.baseChangedCode (E := E))
  rwa [finrank_baseChangedCode, hdim] at hh

end SharedDecoders
