import SharedDecoders.CapacityFieldLinearBound
import SharedDecoders.CapacityCompletion
import SharedDecoders.CapacityLinearization

/-! # The actual scalar residual and its active support

The extension-linearity hypothesis applies to the actual intersection with
the class projection kernel, in the fixed reversed normal basis.
-/

namespace SharedDecoders.CapacityFieldLinear

open Module CapacityIntervals

variable {d : ℕ} [NeZero d]

noncomputable def scalarEncode : State d Bit ≃ₗ[Bit] (ZMod d → Extension d) :=
  LinearEquiv.piCongrRight fun _ => rowEncode d

@[simp] theorem scalarEncode_apply (X : State d Bit) (c : ZMod d) :
    scalarEncode X c = rowEncode d (X c) := rfl

theorem scalarEncode_rot (X : State d Bit) (s : ZMod d) :
    scalarEncode (rot s X) = twist s (scalarEncode X) := by
  funext c
  exact rowEncode_shift d (X c) s

theorem scalarEncode_symm_twist (Y : ZMod d → Extension d) (s : ZMod d) :
    scalarEncode.symm (twist s Y) = rot s (scalarEncode.symm Y) := by
  apply scalarEncode.injective
  rw [LinearEquiv.apply_symm_apply, scalarEncode_rot, LinearEquiv.apply_symm_apply]

def ScalarResidual (H : Submodule Bit (State d Bit)) : Prop :=
  ∀ (a : Extension d) X, X ∈ H → scalarEncode.symm (a • scalarEncode X) ∈ H

noncomputable def encodedResidual (H : Submodule Bit (State d Bit))
    (hH : ScalarResidual H) : Submodule (Extension d) (ZMod d → Extension d) where
  carrier := {Y | scalarEncode.symm Y ∈ H}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY; simpa using H.add_mem hX hY
  smul_mem' := by
    intro a Y hY
    change scalarEncode.symm (a • Y) ∈ H
    simpa only [LinearEquiv.apply_symm_apply] using hH a (scalarEncode.symm Y) hY

noncomputable def encodedResidualEquiv (H : Submodule Bit (State d Bit))
    (hH : ScalarResidual H) : H ≃ₗ[Bit] (encodedResidual H hH).restrictScalars Bit where
  toFun X := ⟨scalarEncode X.1, by change scalarEncode.symm (scalarEncode X.1) ∈ H; simp⟩
  invFun Y := ⟨scalarEncode.symm Y.1, Y.2⟩
  left_inv X := by apply Subtype.ext; exact scalarEncode.symm_apply_apply X.1
  right_inv Y := by apply Subtype.ext; exact scalarEncode.apply_symm_apply Y.1
  map_add' X Y := by apply Subtype.ext; exact map_add scalarEncode X.1 Y.1
  map_smul' a X := by apply Subtype.ext; exact map_smul scalarEncode a X.1

theorem finrank_encodedResidual (H : Submodule Bit (State d Bit)) (hH : ScalarResidual H) :
    finrank Bit H = d * finrank (Extension d) (encodedResidual H hH) := by
  rw [(encodedResidualEquiv H hH).finrank_eq]
  have ht := Module.finrank_mul_finrank Bit (Extension d) (encodedResidual H hH)
  rw [extension_finrank] at ht
  exact ht.symm

noncomputable def activeRows (K : Submodule (Extension d) (ZMod d → Extension d)) :
    Finset (ZMod d) := by
  classical
  exact Finset.univ.filter fun c => ∃ X ∈ K, X c ≠ 0

@[simp] theorem mem_activeRows (K : Submodule (Extension d) (ZMod d → Extension d))
    (c : ZMod d) : c ∈ activeRows K ↔ ∃ X ∈ K, X c ≠ 0 := by
  classical
  simp [activeRows]

theorem zero_outside_activeRows (K : Submodule (Extension d) (ZMod d → Extension d))
    {X : ZMod d → Extension d} (hX : X ∈ K) {c : ZMod d} (hc : c ∉ activeRows K) : X c = 0 := by
  by_contra hn
  exact hc ((mem_activeRows K c).mpr ⟨X,hX,hn⟩)

noncomputable def extendSupport (S : Finset (ZMod d)) :
    (S → Extension d) →ₗ[Extension d] (ZMod d → Extension d) where
  toFun X c := if h : c ∈ S then X ⟨c,h⟩ else 0
  map_add' X Y := by
    classical
    funext c
    by_cases hc : c∈S <;> simp [hc]
  map_smul' a X := by
    classical
    funext c
    by_cases hc : c∈S <;> simp [hc]

omit [NeZero d] in
@[simp] theorem extendSupport_apply (S : Finset (ZMod d)) (X : S → Extension d) (c : S) :
    extendSupport S X c = X c := by
  classical
  simp [extendSupport, c.2]

theorem extendSupport_twist (S : Finset (ZMod d)) (X : S → Extension d) (s : ZMod d) :
    extendSupport S (twist s X) = twist s (extendSupport S X) := by
  classical
  funext c
  by_cases hc : c∈S <;> simp [extendSupport, twist, hc]

noncomputable def supportedResidual (K : Submodule (Extension d) (ZMod d → Extension d)) :
    Submodule (Extension d) (activeRows K → Extension d) := K.comap (extendSupport (activeRows K))

noncomputable def supportedResidualEquiv (K : Submodule (Extension d) (ZMod d → Extension d)) :
    K ≃ₗ[Extension d] supportedResidual K where
  toFun X := ⟨fun c => X.1 c.1, by
    change extendSupport (activeRows K) (fun c => X.1 c.1) ∈ K
    have he : extendSupport (activeRows K) (fun c => X.1 c.1) = X.1 := by
      classical
      funext c
      by_cases hc : c∈activeRows K
      · exact dite_eq_left hc
      · exact (dite_eq_right hc).trans (zero_outside_activeRows K X.2 hc).symm
    rw [he]; exact X.2⟩
  invFun Y := ⟨extendSupport (activeRows K) Y.1, Y.2⟩
  left_inv X := by
    apply Subtype.ext
    funext c
    classical
    by_cases hc : c∈activeRows K
    · exact dite_eq_left hc
    · exact (dite_eq_right hc).trans (zero_outside_activeRows K X.2 hc).symm
  right_inv Y := by apply Subtype.ext; funext c; exact extendSupport_apply _ _ c
  map_add' X Y := rfl
  map_smul' a X := rfl

theorem active_class_residual_bound {κ : Type*} [DecidableEq κ]
    (p : ZMod d → κ) (r : κ → ZMod d) (hr : ∀ j, p (r j)=j)
    (H : Submodule Bit (State d Bit)) (hH : ScalarResidual H)
    (hker : H ≤ LinearMap.ker (classProjection (F := Bit) p r))
    (hdec : IsLinearSharedCode p H) (j : κ) :
    ((activeRows (encodedResidual H hH)).filter (fun c => p c=j)).card +
      finrank (Extension d) (encodedResidual H hH) ≤
        (activeRows (encodedResidual H hH)).card := by
  classical
  obtain ⟨f,hf⟩ := hdec
  let K := encodedResidual H hH
  let S := activeRows K
  let g : (S → Extension d) →ₗ[Bit] Extension d := (rowEncode d).toLinearMap.comp
    ((f j).comp (scalarEncode.symm.toLinearMap.comp ((extendSupport S).restrictScalars Bit)))
  let J : Finset S := Finset.univ.filter fun c => p c.1=j
  have hzero : ∀ x ∈ supportedResidual K, g (twist (r j) x)=0 := by
    intro x hx
    let X := scalarEncode.symm (extendSupport S x)
    have hX : X∈H := hx
    have hrX : X (r j)=0 := (mem_classProjection_ker hr).mp (hker hX) j
    change rowEncode d (f j (scalarEncode.symm (extendSupport S (twist (r j) x)))) = 0
    rw [extendSupport_twist, scalarEncode_symm_twist]
    change rowEncode d (f j (rot (r j) X))=0
    have he := hf X hX (r j)
    rw [hr j] at he
    rw [← he, hrX, map_zero]
  have hcorrect : ∀ c∈J, ∀ x∈supportedResidual K, g (twist c.1 x)=x c := by
    intro c hc x hx
    have hp : p c.1=j := (Finset.mem_filter.mp hc).2
    let X := scalarEncode.symm (extendSupport S x)
    have hX : X∈H := hx
    change rowEncode d (f j (scalarEncode.symm (extendSupport S (twist c.1 x))))=x c
    rw [extendSupport_twist, scalarEncode_symm_twist]
    change rowEncode d (f j (rot c.1 X))=x c
    rw [← hp, ← hf X hX c.1]
    change scalarEncode X c.1=x c
    rw [show scalarEncode X=extendSupport S x from scalarEncode.apply_symm_apply _]
    exact extendSupport_apply S x c
  have hactive : ∀ c∈J, ∃ x∈supportedResidual K, x c≠0 := by
    intro c _
    obtain ⟨X,hX,hc⟩ := (mem_activeRows K c.1).mp c.2
    exact ⟨(supportedResidualEquiv K ⟨X,hX⟩).1,
      (supportedResidualEquiv K ⟨X,hX⟩).2, hc⟩
  have hb := active_class_finrank_bound (supportedResidual K) g (r j)
    Subtype.val Subtype.val_injective J hzero hcorrect hactive
  have hcard : J.card=(S.filter (fun c => p c=j)).card := by
    simp only [J, Finset.card_filter]
    exact Finset.sum_coe_sort S (fun c => if p c=j then 1 else 0)
  rw [hcard, ← (supportedResidualEquiv K).finrank_eq] at hb
  simpa only [Fintype.card_coe] using hb

/-- The class-sensitive bound for the original source, without assuming that
the covariant baseline is contained in it. -/
theorem original_source_class_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : ZMod d → κ) (r : κ → ZMod d) (hr : ∀ j, p (r j)=j)
    (C : Submodule Bit (State d Bit)) (hC : IsLinearSharedCode p C)
    (hH : ScalarResidual (C ⊓ LinearMap.ker (classProjection (F := Bit) p r))) (j : κ) :
    finrank Bit C + d * ((activeRows (encodedResidual _ hH)).filter (fun c => p c=j)).card ≤
      Fintype.card κ * d + d * (activeRows (encodedResidual _ hH)).card := by
  let H := C ⊓ LinearMap.ker (classProjection (F := Bit) p r)
  have hdec : IsLinearSharedCode p H := by
    obtain ⟨f,hf⟩ := hC
    exact ⟨f, fun X hX c => hf X hX.1 c⟩
  have hactive := active_class_residual_bound p r hr H hH inf_le_right hdec j
  have hsource := finrank_le_completedCode hr C
  rw [finrank_completedCode hr] at hsource
  rw [finrank_encodedResidual H hH] at hsource
  simp only [Module.finrank_self, mul_one] at hsource
  have hmul := Nat.mul_le_mul_left d hactive
  dsimp [H] at hmul hsource
  nlinarith only [hmul, hsource]

end SharedDecoders.CapacityFieldLinear
