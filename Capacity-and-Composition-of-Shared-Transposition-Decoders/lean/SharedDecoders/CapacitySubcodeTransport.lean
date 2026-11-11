import SharedDecoders.CapacityLinearization

/-! # Entry-coordinate transport and coupled direct sums -/

namespace SharedDecoders.CapacitySubcode

open Module

variable {F A B κ : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] {d : ℕ}

noncomputable def entryEquiv (e : A ≃ₗ[F] B) : State d A ≃ₗ[F] State d B where
  toFun := entryLinear e.toLinearMap
  invFun := entryLinear e.symm.toLinearMap
  left_inv X := by ext i j; exact e.symm_apply_apply _
  right_inv X := by ext i j; exact e.apply_symm_apply _
  map_add' := (entryLinear e.toLinearMap).map_add
  map_smul' := (entryLinear e.toLinearMap).map_smul

@[simp] theorem entryEquiv_apply (e : A ≃ₗ[F] B) (X : State d A) (i j) :
    entryEquiv e X i j = e (X i j) := rfl

@[simp] theorem entryEquiv_rot (e : A ≃ₗ[F] B) (c : ZMod d) (X : State d A) :
    entryEquiv e (rot c X) = rot c (entryEquiv e X) := rfl

theorem shared_map {p : ZMod d → κ} {C : Submodule F (State d A)}
    (h : IsSharedCode F p C) (e : A ≃ₗ[F] B) :
    IsSharedCode F p (C.map (entryEquiv e).toLinearMap) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun j Y c => e (f j ((entryEquiv e).symm Y) c), ?_⟩
  rintro X ⟨Y, hY, rfl⟩ c
  have hh := hf Y hY c
  funext i
  change e (Y c i) = e (f (p c) ((entryEquiv e).symm (rot c (entryEquiv e Y))) i)
  rw [← entryEquiv_rot, LinearEquiv.symm_apply_apply, ← hh]

theorem linear_comap {p : ZMod d → κ} {C : Submodule F (State d B)}
    (h : IsLinearSharedCode p C) (e : A ≃ₗ[F] B) :
    IsLinearSharedCode p (C.comap (entryEquiv e).toLinearMap) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun j => (wordLinear e.symm.toLinearMap).comp
    ((f j).comp (entryEquiv e).toLinearMap), ?_⟩
  intro X hX c
  have hh := hf (entryEquiv e X) hX c
  funext i
  have hhi := congrFun hh i
  exact (e.symm_apply_apply (X c i)).symm.trans (congrArg e.symm hhi)

theorem subcode_bound_map [NeZero d] [FiniteDimensional F A] [FiniteDimensional F B]
    {p : ZMod d → κ} (C : Submodule F (State d A)) (L : ℕ)
    (h : ∀ D ≤ C, IsLinearSharedCode p D → finrank F D ≤ L)
    (e : A ≃ₗ[F] B) :
    ∀ D ≤ C.map (entryEquiv e).toLinearMap,
      IsLinearSharedCode p D → finrank F D ≤ L := by
  intro D hD hlin
  have hle : D.comap (entryEquiv e).toLinearMap ≤ C := by
    intro X hX
    obtain ⟨Y, hY, heq⟩ := hD hX
    exact (entryEquiv e).injective heq ▸ hY
  have hh := h _ hle (linear_comap hlin e)
  have he := (LinearEquiv.ofSubmodule' (entryEquiv e) D).finrank_eq
  rwa [he] at hh

noncomputable def productCode (G : Submodule F (State d A))
    (H : Submodule F (State d B)) : Submodule F (State d (A × B)) :=
  (G.comap (entryLinear (LinearMap.fst F A B))) ⊓
    (H.comap (entryLinear (LinearMap.snd F A B)))

noncomputable def productCodeEquiv (G : Submodule F (State d A))
    (H : Submodule F (State d B)) : productCode G H ≃ₗ[F] (G × H) where
  toFun X := (⟨entryLinear (LinearMap.fst F A B) X, X.property.1⟩,
    ⟨entryLinear (LinearMap.snd F A B) X, X.property.2⟩)
  invFun X := ⟨fun i j => (X.1.val i j, X.2.val i j), X.1.property, X.2.property⟩
  left_inv X := by ext i j <;> rfl
  right_inv X := rfl
  map_add' X Y := rfl
  map_smul' r X := rfl

theorem finrank_productCode [NeZero d] [FiniteDimensional F A] [FiniteDimensional F B]
    (G : Submodule F (State d A)) (H : Submodule F (State d B)) :
    finrank F (productCode G H) = finrank F G + finrank F H := by
  rw [(productCodeEquiv G H).finrank_eq, Module.finrank_prod]

theorem shared_product {p : ZMod d → κ} {G : Submodule F (State d A)}
    {H : Submodule F (State d B)} (hG : IsSharedCode F p G) (hH : IsSharedCode F p H) :
    IsSharedCode F p (productCode G H) := by
  obtain ⟨f, hf⟩ := hG
  obtain ⟨g, hg⟩ := hH
  refine ⟨fun j X t => (f j (entryLinear (LinearMap.fst F A B) X) t,
    g j (entryLinear (LinearMap.snd F A B) X) t), ?_⟩
  intro X hX c
  funext t
  apply Prod.ext
  · exact congrFun (hf _ hX.1 c) t
  · exact congrFun (hg _ hX.2 c) t

theorem product_linear_subcode_bound [NeZero d]
    [FiniteDimensional F A] [FiniteDimensional F B]
    {p : ZMod d → κ} (G : Submodule F (State d A)) (H : Submodule F (State d B))
    (L : ℕ) (hL : ∀ D ≤ H, IsLinearSharedCode p D → finrank F D ≤ L)
    (C : Submodule F (State d (A × B))) (hC : C ≤ productCode G H)
    (hlin : IsLinearSharedCode p C) : finrank F C ≤ finrank F G + L :=
  linear_subcode_lane_bound G H C hlin
    (fun _ h => (hC h).1) (fun _ h => (hC h).2) L hL

end SharedDecoders.CapacitySubcode
