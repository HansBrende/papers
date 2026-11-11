import SharedDecoders.CapacityReflectionRecovery
import SharedDecoders.ConstructionBaseChange

/-! # Scalar extension of the actual reflection source, with arbitrary lanes

The extended code is the span of the embedded original basis.  Its dimension,
source equations and actual decoder equations are proved here, not supplied
as hypotheses of the reflection endpoint.
-/

namespace SharedDecoders.CapacityReflection

open Module

variable {F E κ : Type*} [Field F] [Field E] [Algebra F E]
  {d b : ℕ} [NeZero d]

def flattenWord (F : Type*) [Field F] (d b : ℕ) :
    (ZMod d → Fin b → F) ≃ₗ[F] (ZMod d × Fin b → F) where
  toFun x z := x z.1 z.2
  invFun x i l := x (i,l)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def extendLaneDecoder
    (f : State d (Fin b → F) →ₗ[F] (ZMod d → Fin b → F)) :
    State d (Fin b → E) →ₗ[E] (ZMod d → Fin b → E) :=
  (flattenWord E d b).symm.toLinearMap.comp
    ((coordinateExtension E ((flattenWord F d b).toLinearMap.comp
      (f.comp (flattenState F d b).symm.toLinearMap))).comp
        (flattenState E d b).toLinearMap)

theorem extendLaneDecoder_base
    (f : State d (Fin b → F) →ₗ[F] (ZMod d → Fin b → F))
    (X : State d (Fin b → F)) :
    extendLaneDecoder (E := E) f (stateScalarMap X) =
      fun j l => algebraMap F E (f X j l) := by
  change (flattenWord E d b).symm (coordinateExtension E _
    (fun z => algebraMap F E (flattenState F d b X z))) = _
  rw [coordinateExtension_base]
  rfl

noncomputable def extendedCode (C : Submodule F (State d (Fin b → F))) :
    Submodule E (State d (Fin b → E)) :=
  Submodule.span E (Set.range fun i => stateScalarMap (E := E)
    ((Module.finBasis F C) i : State d (Fin b → F)))

theorem extendedBasis_independent (C : Submodule F (State d (Fin b → F))) :
    LinearIndependent E (fun i => stateScalarMap (E := E)
      ((Module.finBasis F C) i : State d (Fin b → F))) := by
  let v := fun i => flattenState F d b ((Module.finBasis F C) i : State d (Fin b → F))
  have hinj : Function.Injective ((flattenState F d b).toLinearMap.comp C.subtype) :=
    (flattenState F d b).injective.comp Subtype.coe_injective
  have hv : LinearIndependent F v := (Module.finBasis F C).linearIndependent.map'
    ((flattenState F d b).toLinearMap.comp C.subtype) (LinearMap.ker_eq_bot.mpr hinj)
  have he : LinearIndependent E (fun i => algebraMap F E ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  exact LinearIndependent.of_comp (flattenState E d b).toLinearMap he

theorem finrank_extendedCode (C : Submodule F (State d (Fin b → F))) :
    finrank E (extendedCode (E := E) C) = finrank F C := by
  rw [extendedCode, finrank_span_eq_card (extendedBasis_independent C), Fintype.card_fin]

theorem extendedCode_shared {p : ZMod d → κ}
    {C : Submodule F (State d (Fin b → F))} (hC : IsLinearSharedCode p C) :
    IsLinearSharedCode p (extendedCode (E := E) C) := by
  obtain ⟨f,hf⟩ := hC
  refine ⟨fun J => extendLaneDecoder (E := E) (f J), ?_⟩
  intro X hX c
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨i,rfl⟩ := hX
    rw [← stateScalarMap_rot, extendLaneDecoder_base]
    funext j l
    exact congrArg (algebraMap F E)
      (congrFun (congrFun (hf _ ((Module.finBasis F C) i).property c) j) l)
  | zero => rw [show rot c (0 : State d (Fin b → E)) = 0 from rfl, map_zero]; rfl
  | add X Y _ _ hX hY =>
    change X c + Y c = extendLaneDecoder (E := E) (f (p c)) (rot c X + rot c Y)
    rw [map_add,hX,hY]
  | smul k X _ hX =>
    change k • X c = extendLaneDecoder (E := E) (f (p c)) (k • rot c X)
    rw [map_smul,hX]

theorem extendedCode_le_source {C : Submodule F (State d (Fin b → F))}
    (hC : C ≤ source (F := F) d) :
    extendedCode (E := E) C ≤ source (F := E) d := by
  apply Submodule.span_le.mpr
  rintro X ⟨i,rfl⟩ c
  have hi := hC ((Module.finBasis F C) i).property c
  constructor
  · funext l
    change algebraMap F E (((Module.finBasis F C) i : State d (Fin b → F)) c 0 l) = 0
    rw [congrFun hi.1 l]
    exact map_zero _
  · intro j
    funext l
    exact congrArg (algebraMap F E) (congrFun (hi.2 j) l)

end SharedDecoders.CapacityReflection
