import SharedDecoders.CapacityRetentionFinite

/-! # Paired-lane streaming control

Swapping the two lanes of every entry is transpose-correct on pairs (X, Xᵀ).
The source has rate one half but loses an extensive fraction of symmetric
directions. The algebraic statements hold over every field and for vector lanes.
-/

namespace SharedDecoders.RetentionControl

open Module

variable {F A I : Type*} [Field F] [AddCommGroup A] [Module F A]

/-- The entrywise interchange of the two lane groups. -/
def laneSwap : (I → I → A × A) →ₗ[F] (I → I → A × A) where
  toFun X i j := (X i j).swap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pairedSource : Submodule F (I → I → A × A) where
  carrier := {X | ∀ i j, (X i j).2 = (X j i).1}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro X Y hX hY i j
    exact congrArg₂ (· + ·) (hX i j) (hY i j)
  smul_mem' := by
    intro a X hX i j
    exact congrArg (a • ·) (hX i j)

theorem laneSwap_eq_transpose_iff (X : I → I → A × A) :
    laneSwap (F := F) X = (fun i j => X j i) ↔ X ∈ pairedSource (F := F) := by
  constructor
  · intro h i j
    exact congrArg Prod.fst (congrFun (congrFun h i) j)
  · intro h
    ext i j
    · exact h i j
    · exact (h j i).symm

noncomputable def pairedEquiv : pairedSource (F := F) (A := A) (I := I) ≃ₗ[F]
    (I → I → A) where
  toFun X i j := (X.val i j).1
  invFun Y := ⟨fun i j => (Y i j, Y j i), fun _ _ => rfl⟩
  left_inv X := by
    apply Subtype.ext
    funext i j
    exact Prod.ext rfl (X.property i j).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def symmetricPairedEquiv :
    (pairedSource ⊓ symmetricSpace : Submodule F (I → I → A × A)) ≃ₗ[F]
      symmetricSpace (F := F) (A := A) (I := I) where
  toFun X := ⟨fun i j => (X.val i j).1, fun i j => congrArg Prod.fst (X.property.2 i j)⟩
  invFun Y := ⟨fun i j => (Y.val i j, Y.val i j),
    ⟨fun i j => Y.property i j, fun i j => congrArg (fun a => (a, a)) (Y.property i j)⟩⟩
  left_inv X := by
    apply Subtype.ext
    funext i j
    apply Prod.ext
    · rfl
    · exact (congrArg Prod.fst (X.property.2 i j)).trans (X.property.1 i j).symm
  right_inv _ := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

variable [Fintype I] [FiniteDimensional F A]

theorem finrank_pairedSource :
    finrank F (pairedSource (F := F) (A := A) (I := I)) =
      Fintype.card I * Fintype.card I * finrank F A := by
  rw [pairedEquiv.finrank_eq]
  simp [Module.finrank_pi_fintype, mul_assoc]

theorem twice_finrank_symmetric_intersection :
    2 * finrank F (pairedSource ⊓ symmetricSpace : Submodule F (I → I → A × A)) =
      Fintype.card I * (Fintype.card I + 1) * finrank F A := by
  rw [symmetricPairedEquiv.finrank_eq]
  exact two_mul_finrank_symmetricSpace

/-- Half the ambient dimension is correct, while the symmetry loss is
one full scalar symmetric space. No small-loss inference from a streaming
implementation is possible without an additional hypothesis. -/
theorem paired_source_rate_and_loss :
    let C := pairedSource (F := F) (A := A) (I := I)
    let S : Submodule F (I → I → A × A) := symmetricSpace
    let η := finrank F S - finrank F (C ⊓ S : Submodule F (I → I → A × A))
    2 * finrank F C = finrank F (I → I → A × A) ∧
      2 * η = Fintype.card I * (Fintype.card I + 1) * finrank F A := by
  dsimp only
  have hS := two_mul_finrank_symmetricSpace (F := F) (A := A × A) (I := I)
  have h₀ := twice_finrank_symmetric_intersection (F := F) (A := A) (I := I)
  have hle : finrank F (pairedSource ⊓ symmetricSpace : Submodule F (I → I → A × A)) ≤
      finrank F (symmetricSpace (F := F) (A := A × A) (I := I)) :=
    Submodule.finrank_mono inf_le_right
  have hsub := Nat.sub_add_cancel hle
  simp only [Module.finrank_prod] at hS
  constructor
  · rw [finrank_pairedSource]
    simp [Module.finrank_pi_fintype, Module.finrank_prod, mul_add, mul_assoc, two_mul]
  · nlinarith

end SharedDecoders.RetentionControl
