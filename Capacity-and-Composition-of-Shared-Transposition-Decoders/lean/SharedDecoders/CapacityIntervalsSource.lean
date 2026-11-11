import SharedDecoders.CapacityIntervalsField

/-! Paired actual rows, disjoint rotated views, and completion by class representatives. -/

namespace SharedDecoders.CapacityIntervals

open Module LinearMap

variable {d b : ℕ} [NeZero d] {κ I : Type*}

/-- `layout` places class representatives first and pairs all remaining rows. -/
noncomputable def pairedFieldMap (layout : κ ⊕ (I × Bool) ≃ ZMod d) :
    (I → Fin b → Extension d) →ₗ[Bit] (ZMod d → Fin b → Extension d) where
  toFun x c l := match layout.symm c with
    | Sum.inl _ => 0
    | Sum.inr (i, false) => x i l
    | Sum.inr (i, true) => normalElement d * x i l
  map_add' x y := by
    funext c l
    rcases h : layout.symm c with a | ⟨i, z⟩
    · simp [h]
    · cases z <;> simp [h, mul_add]
  map_smul' a x := by
    funext c l
    rcases h : layout.symm c with z | ⟨i, z⟩
    · simp [h]
    · cases z <;> simp [h, Algebra.smul_def, mul_left_comm]

noncomputable def pairedSourceMap (layout : κ ⊕ (I × Bool) ≃ ZMod d) :
    (I → Fin b → Extension d) →ₗ[Bit] State d (Fin b → Bit) :=
  (fieldEncode d).symm.toLinearMap.comp (pairedFieldMap layout)

noncomputable def pairedSource (layout : κ ⊕ (I × Bool) ≃ ZMod d) :
    Submodule Bit (State d (Fin b → Bit)) := (pairedSourceMap layout).range

@[simp] theorem fieldEncode_pairedSourceMap (layout : κ ⊕ (I × Bool) ≃ ZMod d)
    (x : I → Fin b → Extension d) :
    fieldEncode d (pairedSourceMap layout x) = pairedFieldMap layout x :=
  (fieldEncode d).apply_symm_apply _

omit [NeZero d] in
@[simp] theorem pairedFieldMap_representative (layout : κ ⊕ (I × Bool) ≃ ZMod d)
    (x : I → Fin b → Extension d) (a : κ) (l : Fin b) :
    pairedFieldMap layout x (layout (Sum.inl a)) l = 0 := by
  simp [pairedFieldMap]

omit [NeZero d] in
@[simp] theorem pairedFieldMap_first (layout : κ ⊕ (I × Bool) ≃ ZMod d)
    (x : I → Fin b → Extension d) (i : I) (l : Fin b) :
    pairedFieldMap layout x (layout (Sum.inr (i, false))) l = x i l := by
  simp [pairedFieldMap]

omit [NeZero d] in
@[simp] theorem pairedFieldMap_second (layout : κ ⊕ (I × Bool) ≃ ZMod d)
    (x : I → Fin b → Extension d) (i : I) (l : Fin b) :
    pairedFieldMap layout x (layout (Sum.inr (i, true))) l = normalElement d * x i l := by
  simp [pairedFieldMap]

theorem pairedSourceMap_injective (layout : κ ⊕ (I × Bool) ≃ ZMod d) :
    Function.Injective (pairedSourceMap layout (b := b)) := by
  intro x y h
  funext i l
  have hh := congrArg (fun X => fieldEncode d X (layout (Sum.inr (i, false))) l) h
  simpa only [fieldEncode_pairedSourceMap, pairedFieldMap_first] using hh

theorem finrank_pairedSource [Fintype I] (layout : κ ⊕ (I × Bool) ≃ ZMod d) :
    finrank Bit (pairedSource layout (b := b)) = Fintype.card I * b * d := by
  rw [pairedSource, LinearMap.finrank_range_of_inj (pairedSourceMap_injective layout)]
  simp [Module.finrank_pi_fintype, extension_finrank, mul_assoc]

theorem pairedSource_representative_zero (layout : κ ⊕ (I × Bool) ≃ ZMod d)
    {X : State d (Fin b → Bit)} (hX : X ∈ pairedSource layout) (a : κ) :
    X (layout (Sum.inl a)) = 0 := by
  obtain ⟨x, rfl⟩ := hX
  funext j l
  have hh : rowEncode d (fun j => pairedSourceMap layout x (layout (Sum.inl a)) j l) = 0 := by
    change fieldEncode d (pairedSourceMap layout x) (layout (Sum.inl a)) l = 0
    simp only [fieldEncode_pairedSourceMap, pairedFieldMap_representative]
  have hz := (rowEncode d).injective (hh.trans (map_zero (rowEncode d)).symm)
  exact congrFun hz j

/-- Distinct receiver phases have disjoint nonzero full residual views.
All lanes may be compared simultaneously; no scalar extension of a binary source is used. -/
theorem pairedSource_disjoint_views (layout : κ ⊕ (I × Bool) ≃ ZMod d)
    {c e : ZMod d} (hce : c ≠ e) :
    Disjoint ((pairedSource layout (b := b)).map (rotLinear Bit c))
      ((pairedSource layout (b := b)).map (rotLinear Bit e)) := by
  rw [Submodule.disjoint_def]
  rintro Z ⟨X, ⟨x, rfl⟩, hX⟩ ⟨Y, ⟨y, rfl⟩, hY⟩
  have hview : rot c (pairedSourceMap layout x) = rot e (pairedSourceMap layout y) :=
    hX.trans hY.symm
  have hx0 : x = 0 := by
    funext i l
    have hfirst := congrArg (fun Z => fieldEncode d Z (layout (Sum.inr (i, false))) l) hview
    simp only [fieldEncode_rot, fieldEncode_pairedSourceMap, pairedFieldMap_first] at hfirst
    have hsecond := congrArg (fun Z => fieldEncode d Z (layout (Sum.inr (i, true))) l) hview
    simp only [fieldEncode_rot, fieldEncode_pairedSourceMap, pairedFieldMap_second,
      map_mul] at hsecond
    rw [hfirst] at hsecond
    have hcoeff : phase d c (normalElement d) - phase d e (normalElement d) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hce (phase_normal_injective d h))
    have hprod : (phase d c (normalElement d) - phase d e (normalElement d)) *
        phase d e (y i l) = 0 := by
      rw [sub_mul]
      exact sub_eq_zero.mpr hsecond
    have hy0 := (mul_eq_zero.mp hprod).resolve_left hcoeff
    exact (phase d c).injective (hfirst.trans (hy0.trans (map_zero (phase d c)).symm))
  rw [hx0, map_zero] at hX
  exact hX.symm

theorem pairedSource_isSharedCode (p : ZMod d → κ)
    (layout : κ ⊕ (I × Bool) ≃ ZMod d) :
    IsSharedCode Bit p (pairedSource layout (b := b)) :=
  IsSharedCode.of_disjoint_views (fun _ _ h => pairedSource_disjoint_views layout h)

theorem pairedSource_le_projection_ker (p : ZMod d → κ)
    (layout : κ ⊕ (I × Bool) ≃ ZMod d)
    (hr : ∀ a, p (layout (Sum.inl a)) = a) :
    pairedSource layout (b := b) ≤
      LinearMap.ker (classProjection p (fun a => layout (Sum.inl a))) := by
  intro X hX
  exact (mem_classProjection_ker hr).mpr (pairedSource_representative_zero layout hX)

/-- Complete the paired source using its actual class representatives. -/
theorem paired_completion [Fintype κ] [Fintype I]
    (p : ZMod d → κ) (layout : κ ⊕ (I × Bool) ≃ ZMod d)
    (hr : ∀ a, p (layout (Sum.inl a)) = a) :
    ∃ C : Submodule Bit (State d (Fin b → Bit)), IsSharedCode Bit p C ∧
      finrank Bit C = (Fintype.card I + Fintype.card κ) * b * d := by
  let r := fun a => layout (Sum.inl a)
  let C := completedCode p r (pairedSource layout (b := b))
  refine ⟨C, (pairedSource_isSharedCode p layout).completedCode hr, ?_⟩
  change finrank Bit (completedCode p r (pairedSource layout (b := b))) = _
  rw [finrank_completedCode hr,
    inf_eq_left.mpr (pairedSource_le_projection_ker p layout hr), finrank_pairedSource]
  simp
  ring

end SharedDecoders.CapacityIntervals
