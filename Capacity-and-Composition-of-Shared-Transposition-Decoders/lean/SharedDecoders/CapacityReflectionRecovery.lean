import SharedDecoders.ConstructionBlockRecovery
import SharedDecoders.CapacityReflectionSource
import SharedDecoders.CapacityLinearization

/-! # The all-width descending recovery count for reflected Fourier blocks

This module proves the recovery bound for its precise block equations and
the actual original-coordinate cut from two decoders to one. The actual
Fourier/scalar-extension adapter and complete endpoints are supplied by
`CapacityReflectionBaseChange`, `CapacityReflectionFourier`,
`CapacityReflectionBlocks`, and `CapacityReflectionBarrier`.
-/

namespace SharedDecoders.CapacityReflection

open Module
open scoped BigOperators

variable {F : Type*} [Field F] {m b : ℕ}

theorem reflected_block_finrank_bound
    (L : Fin m → Fin m → Fin m → ((Fin 2 → Fin b → F) →ₗ[F] (Fin 2 → Fin b → F))) :
    finrank F (blockAgreement (LinearEquiv.refl F _) L) ≤ b*m*(m+1) := by
  have hh := finrank_blockAgreement_le (LinearEquiv.refl F _) L
  have hdiag : (∑ j : Fin m, finrank F (diagonalKernel (LinearEquiv.refl F _) L j)) ≤
      m*(2*b) := by
    calc
      _ ≤ ∑ _j : Fin m, finrank F (Fin 2 → Fin b → F) :=
        Finset.sum_le_sum fun j _ => Submodule.finrank_le _
      _ = _ := by simp [Module.finrank_pi_fintype]
  have hc := two_mul_card_upperBlocks m
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hh
  have hcb := congrArg (fun n => b*n) hc
  nlinarith only [hh,hdiag,hcb]

variable {A : Type*} [AddCommGroup A] [Module F A] {d : ℕ}

def singletonPartition (c : ZMod d) : Bool := if c=0 then false else true

def bulkError (f : State d A →ₗ[F] (ZMod d → A)) :
    State d A →ₗ[F] (ZMod d → A) where
  toFun X := f X-X 0
  map_add' X Y := by ext j; simp; abel
  map_smul' a X := by ext j; simp [smul_sub]

theorem bulk_cut_one_class (C : Submodule F (State d A))
    (hC : IsLinearSharedCode singletonPartition C) :
    ∃ H : Submodule F (State d A), H≤C ∧ IsLinearSharedCode (fun _ => ()) H ∧
      ∃ f : State d A →ₗ[F] (ZMod d → A), H=C ⊓ LinearMap.ker (bulkError f) := by
  obtain ⟨f,hf⟩ := hC
  let H := C ⊓ LinearMap.ker (bulkError (f true))
  refine ⟨H,inf_le_left,⟨fun _ => f true, ?_⟩,f true,rfl⟩
  intro X hX c
  by_cases hc : c=0
  · subst c
    have he : f true X-X 0=0 := hX.2
    simpa using (sub_eq_zero.mp he).symm
  · simpa only [singletonPartition, ite_eq_right hc] using hf X hX.1 c

theorem bulk_cut_finrank [NeZero d] [FiniteDimensional F A]
    (C : Submodule F (State d A)) (f : State d A →ₗ[F] (ZMod d → A)) :
    finrank F C ≤ finrank F (C ⊓ LinearMap.ker (bulkError f) : Submodule F (State d A))+
      d*finrank F A := by
  let E := (bulkError f).comp C.subtype
  have hn := LinearMap.finrank_range_add_finrank_ker E
  have hr := Submodule.finrank_le (LinearMap.range E)
  have he : finrank F (LinearMap.ker E)=
      finrank F (C ⊓ LinearMap.ker (bulkError f) : Submodule F (State d A)) := by
    rw [show LinearMap.ker E=(LinearMap.ker (bulkError f)).comap C.subtype by
      ext X; rfl]
    have hco : (C ⊓ LinearMap.ker (bulkError f)).comap C.subtype =
        (LinearMap.ker (bulkError f)).comap C.subtype := by ext X; simp
    rw [← hco]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : C ⊓ LinearMap.ker (bulkError f)≤C)).finrank_eq
  rw [he] at hn
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    ZMod.card, smul_eq_mul] at hr
  omega

end SharedDecoders.CapacityReflection
