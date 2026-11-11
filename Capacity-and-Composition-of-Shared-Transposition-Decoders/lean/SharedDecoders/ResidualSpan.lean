import SharedDecoders.ResidualReplay

/-! # Joint propagated-output corrections, counted without duplicate charges -/

namespace SharedDecoders

open Module

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

noncomputable def residualSpanDescriptor (A : V →ₗ[F] W) (U : Submodule F W) :
    U.comap A →ₗ[F] (A.ker × ↥(U ⊓ A.range : Submodule F W)) where
  toFun x := (A.ker.subtype.leftInverse x.1, ⟨A x.1, x.2, ⟨x.1, rfl⟩⟩)
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Subtype.ext
      exact map_add A _ _
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · apply Subtype.ext
      exact map_smul A _ _

theorem residualSpanDescriptor_injective (A : V →ₗ[F] W) (U : Submodule F W) :
    Function.Injective (residualSpanDescriptor A U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hAx : A x.1 = 0 := congrArg Subtype.val (congrArg Prod.snd hx)
  have hk : x.1 ∈ A.ker := LinearMap.mem_ker.mpr hAx
  have hp : A.ker.subtype.leftInverse x.1 = 0 := congrArg Prod.fst hx
  have hid := LinearMap.leftInverse_apply_of_inj A.ker.ker_subtype (⟨x.1, hk⟩ : A.ker)
  have hz : (⟨x.1, hk⟩ : A.ker) = 0 := hid.symm.trans hp
  have hzero : x.1 = 0 := congrArg (fun v : A.ker => v.1) hz
  exact Subtype.ext hzero

/-- Only the intersection of the joint correction span with the actual image is charged. -/
theorem finrank_preimage_le_kernel_add_intersection [FiniteDimensional F V]
    [FiniteDimensional F W] (A : V →ₗ[F] W) (U : Submodule F W) :
    finrank F (U.comap A) ≤ finrank F A.ker + finrank F (U ⊓ A.range : Submodule F W) := by
  have h := LinearMap.finrank_le_finrank_of_injective (residualSpanDescriptor_injective A U)
  simpa only [Module.finrank_prod] using h

theorem affine_preimage_card_le [Finite F] [Finite V] [FiniteDimensional F V]
    (S : Set V) (A : V →ₗ[F] W) (U : Submodule F W) (c : W)
    (h : ∀ x ∈ S, A x - c ∈ U) :
    Nat.card S ≤ Nat.card F ^ finrank F (U.comap A) := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hS
    have hi : Nat.card S ≤ Nat.card (U.comap A) := by
      refine Nat.card_le_card_of_injective
        (fun x : S => (⟨x.1 - x₀, ?_⟩ : U.comap A)) ?_
      · change A (x.1 - x₀) ∈ U
        have hh := U.sub_mem (h x.1 x.2) (h x₀ hx₀)
        rwa [sub_sub_sub_cancel_right, ← map_sub] at hh
      · intro x y heq
        exact Subtype.ext (sub_left_injective (congrArg Subtype.val heq))
    rwa [Module.natCard_eq_pow_finrank (K := F) (V := U.comap A)] at hi
  · have : IsEmpty S := ⟨fun x => hS ⟨x.1, x.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- The output-span invoice for arbitrary correctness sets and nonlinear corrections. -/
theorem residual_span_card_le [Finite F] [Finite V] [FiniteDimensional F V]
    [FiniteDimensional F W] (S : Set V) (A : V →ₗ[F] W) (U : Submodule F W) (c : W)
    (h : ∀ x ∈ S, A x - c ∈ U) :
    Nat.card S ≤ Nat.card F ^
      (finrank F A.ker + finrank F (U ⊓ A.range : Submodule F W)) := by
  apply (affine_preimage_card_le S A U c h).trans
  exact Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')
    (finrank_preimage_le_kernel_add_intersection A U)

end SharedDecoders
