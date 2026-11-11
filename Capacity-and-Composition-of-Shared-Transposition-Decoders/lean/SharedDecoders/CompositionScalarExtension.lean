import SharedDecoders.CompositionRank
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Extending the literal complete maps to a larger coefficient field

Only a rank upper bound after extension is needed. It is obtained by factoring
through the scalar extension of the original range, so no hidden semisimplicity
or field-invariance hypothesis enters the composition theorem.
-/

namespace SharedDecoders

open Module TensorProduct

variable {F E I J K : Type*} [Field F] [Field E] [Algebra F E]
  [Fintype I] [Fintype J] [Fintype K]

noncomputable def coordinateExtension (E : Type*) [Field E] [Algebra F E]
    (f : (I → F) →ₗ[F] (J → F)) : (I → E) →ₗ[E] (J → E) := by
  classical
  exact (TensorProduct.piScalarRight F E E J).toLinearMap.comp
    ((f.baseChange E).comp (TensorProduct.piScalarRight F E E I).symm.toLinearMap)

lemma coordinateExtension_base (f : (I → F) →ₗ[F] (J → F)) (x : I → F) :
    coordinateExtension E f (fun i => algebraMap F E (x i)) =
      fun j => algebraMap F E (f x j) := by
  classical
  have he : (TensorProduct.piScalarRight F E E I) (1 ⊗ₜ[F] x) =
      fun i => algebraMap F E (x i) := by
    simp [Algebra.smul_def]
  change (TensorProduct.piScalarRight F E E J)
    ((f.baseChange E) ((TensorProduct.piScalarRight F E E I).symm _)) = _
  rw [← he, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
  simp [Algebra.smul_def]

/-- Agreement on the original coordinate vectors determines an extended linear map. -/
lemma coordinate_linear_ext {Z : Type*} [AddCommGroup Z] [Module E Z]
    (f g : (I → E) →ₗ[E] Z)
    (h : ∀ x : I → F, f (fun i => algebraMap F E (x i)) =
      g (fun i => algebraMap F E (x i))) : f = g := by
  classical
  apply LinearMap.pi_ext
  intro i a
  have hbase := h (Pi.single i 1)
  have hscalar : (fun j => algebraMap F E ((Pi.single i (1 : F) : I → F) j)) =
      Pi.single i (1 : E) := by
    funext j
    simp [Pi.single_apply]
  rw [hscalar] at hbase
  have ha : Pi.single i a = a • Pi.single i (1 : E) := by
    funext j
    simp [Pi.single_apply]
  rw [ha, map_smul, map_smul, hbase]

lemma coordinateExtension_comp (f : (I → F) →ₗ[F] (J → F))
    (g : (J → F) →ₗ[F] (K → F)) :
    coordinateExtension E (g.comp f) =
      (coordinateExtension E g).comp (coordinateExtension E f) := by
  apply coordinate_linear_ext (F := F)
  intro x
  simp [coordinateExtension_base]

lemma coordinateExtension_sub (f g : (I → F) →ₗ[F] (J → F)) :
    coordinateExtension E (f - g) = coordinateExtension E f - coordinateExtension E g := by
  apply coordinate_linear_ext (F := F)
  intro x
  simp only [coordinateExtension_base, LinearMap.sub_apply]
  funext j
  simp

lemma coordinateExtension_rank_le (f : (I → F) →ₗ[F] (J → F)) :
    finrank E (LinearMap.range (coordinateExtension E f)) ≤
      finrank F (LinearMap.range f) := by
  classical
  let out := (TensorProduct.piScalarRight F E E J).toLinearMap.comp
    ((LinearMap.range f).subtype.baseChange E)
  let inp := (f.rangeRestrict.baseChange E).comp
    (TensorProduct.piScalarRight F E E I).symm.toLinearMap
  have he : coordinateExtension E f = out.comp inp := by
    have hf : f.baseChange E = ((LinearMap.range f).subtype.baseChange E).comp
        (f.rangeRestrict.baseChange E) := by
      rw [← LinearMap.baseChange_comp, LinearMap.subtype_comp_rangeRestrict]
    simp only [coordinateExtension, out, inp, hf, LinearMap.comp_assoc]
  have h := Submodule.finrank_mono (show LinearMap.range (out.comp inp) ≤
      LinearMap.range out from LinearMap.range_comp_le_range inp out)
  rw [he]
  exact h.trans (out.finrank_range_le.trans_eq (Module.finrank_baseChange (R := E) (S := F)))

abbrev StateIndex (d b : ℕ) := ZMod d × ZMod d × Fin b

def flattenState (F : Type*) [Field F] (d b : ℕ) :
    State d (Fin b → F) ≃ₗ[F] (StateIndex d b → F) where
  toFun X z := X z.1 z.2.1 z.2.2
  invFun x i c l := x (i, c, l)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {d b : ℕ} [NeZero d]

def stateScalarMap (X : State d (Fin b → F)) : State d (Fin b → E) :=
  fun i c l => algebraMap F E (X i c l)

noncomputable def stateExtension (E : Type*) [Field E] [Algebra F E]
    (f : State d (Fin b → F) →ₗ[F] State d (Fin b → F)) :
    State d (Fin b → E) →ₗ[E] State d (Fin b → E) :=
  (flattenState E d b).symm.toLinearMap.comp
    ((coordinateExtension E ((flattenState F d b).toLinearMap.comp
      (f.comp (flattenState F d b).symm.toLinearMap))).comp
        (flattenState E d b).toLinearMap)

lemma stateExtension_base (f : State d (Fin b → F) →ₗ[F] State d (Fin b → F))
    (X : State d (Fin b → F)) : stateExtension E f (stateScalarMap X) =
      stateScalarMap (f X) := by
  change (flattenState E d b).symm (coordinateExtension E _
    (fun z => algebraMap F E (flattenState F d b X z))) = _
  rw [coordinateExtension_base]
  rfl

lemma state_linear_ext {Z : Type*} [AddCommGroup Z] [Module E Z]
    (f g : State d (Fin b → E) →ₗ[E] Z)
    (h : ∀ X : State d (Fin b → F), f (stateScalarMap X) = g (stateScalarMap X)) : f = g := by
  have he : f.comp (flattenState E d b).symm.toLinearMap =
      g.comp (flattenState E d b).symm.toLinearMap := by
    apply coordinate_linear_ext (F := F)
    intro x
    exact h ((flattenState F d b).symm x)
  apply LinearMap.ext
  intro X
  exact LinearMap.congr_fun he (flattenState E d b X)

lemma stateExtension_comp
    (f g : State d (Fin b → F) →ₗ[F] State d (Fin b → F)) :
    stateExtension E (g.comp f) = (stateExtension E g).comp (stateExtension E f) := by
  apply state_linear_ext (F := F)
  intro X
  simp [stateExtension_base]

lemma stateExtension_sub
    (f g : State d (Fin b → F) →ₗ[F] State d (Fin b → F)) :
    stateExtension E (f - g) = stateExtension E f - stateExtension E g := by
  apply state_linear_ext (F := F)
  intro X
  simp only [stateExtension_base, LinearMap.sub_apply]
  funext i c l
  simp [stateScalarMap]

lemma stateExtension_swap :
    stateExtension E (swapLinear F : State d (Fin b → F) →ₗ[F] _) = swapLinear E := by
  apply state_linear_ext (F := F)
  intro X
  rw [stateExtension_base]
  rfl


lemma conjugate_rank_eq {R V V' : Type*} [Field R]
    [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']
    (e : V ≃ₗ[R] V') (f : V →ₗ[R] V) :
    finrank R (LinearMap.range (e.toLinearMap.comp (f.comp e.symm.toLinearMap))) =
      finrank R (LinearMap.range f) := by
  rw [LinearMap.range_comp, e.finrank_map_eq, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top]

lemma stateExtension_rank_le
    (f : State d (Fin b → F) →ₗ[F] State d (Fin b → F)) :
    finrank E (LinearMap.range (stateExtension E f)) ≤ finrank F (LinearMap.range f) := by
  unfold stateExtension
  have he := conjugate_rank_eq (flattenState E d b).symm
    (coordinateExtension E ((flattenState F d b).toLinearMap.comp
      (f.comp (flattenState F d b).symm.toLinearMap)))
  simp only [LinearEquiv.symm_symm] at he
  rw [he]
  exact (coordinateExtension_rank_le _).trans_eq (conjugate_rank_eq (flattenState F d b) f)

omit [NeZero d] in
lemma stateScalarMap_rot (s : ZMod d) (X : State d (Fin b → F)) :
    stateScalarMap (E := E) (rot s X) = rot s (stateScalarMap X) := rfl

/-- Extending coefficients preserves the actual receiver classes and getters.
The argument uses the full linear maps, not a correctness fibre. -/
lemma stateExtension_classUniform {κ : Type*} (p : ZMod d → κ)
    (K : State d (Fin b → F) →ₗ[F] State d (Fin b → F)) (hK : ClassUniform p K) :
    ClassUniform p (stateExtension E K) := by
  classical
  let K' := stateExtension E K
  let col (c : ZMod d) : State d (Fin b → E) →ₗ[E] (ZMod d → Fin b → E) := {
    toFun := fun X i => X i c
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  refine ⟨fun J X => col (classRepresentative p J)
    (K' (rot (-classRepresentative p J) X)), ?_⟩
  intro X c i
  let e := classRepresentative p (p c)
  have he : p e = p c := classRepresentative_spec p c
  have hl : (col c).comp K' = (col e).comp (K'.comp (rotLinear E (c - e))) := by
    apply state_linear_ext (F := F)
    intro Y
    change col c (stateExtension E K (stateScalarMap Y)) =
      col e (stateExtension E K (rot (c - e) (stateScalarMap Y)))
    rw [← stateScalarMap_rot, stateExtension_base, stateExtension_base]
    funext j l
    change algebraMap F E (K Y j c l) = algebraMap F E (K (rot (c - e) Y) j e l)
    exact congrArg (algebraMap F E) (congrFun (hK.columns_of_same_class he Y j) l)
  have hh := congrFun (LinearMap.congr_fun hl X) i
  change K' X i c = K' (rot (-e) (rot c X)) i e
  rw [rot_rot]
  change K' X i c = K' (rot (c - e) X) i e at hh
  simpa only [neg_add_eq_sub] using hh

end SharedDecoders
