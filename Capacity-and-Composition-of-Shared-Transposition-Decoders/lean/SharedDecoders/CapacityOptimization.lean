import SharedDecoders.CapacityCompletion
import SharedDecoders.CapacityLinearization
import Mathlib.Order.Lattice.Nat

/-! # Attained capacities and the residual optimization identity -/

namespace SharedDecoders

open Module

section General

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

noncomputable def dimensionCapacity (P : Submodule F V → Prop) : ℕ :=
  sSup {n | ∃ C, P C ∧ finrank F C = n}

variable [FiniteDimensional F V]

theorem dimensionCapacity_bddAbove (P : Submodule F V → Prop) :
    BddAbove {n | ∃ C, P C ∧ finrank F C = n} := by
  refine ⟨finrank F V, ?_⟩
  rintro n ⟨C, _, rfl⟩
  exact Submodule.finrank_le C

theorem le_dimensionCapacity {P : Submodule F V → Prop} {C : Submodule F V}
    (hC : P C) : finrank F C ≤ dimensionCapacity P :=
  le_csSup (dimensionCapacity_bddAbove P) ⟨C, hC, rfl⟩

theorem dimensionCapacity_attained (P : Submodule F V → Prop) (hP : P ⊥) :
    ∃ C, P C ∧ finrank F C = dimensionCapacity P := by
  change sSup {n | ∃ C, P C ∧ finrank F C = n} ∈ {n | ∃ C, P C ∧ finrank F C = n}
  exact Nat.sSup_mem ⟨0, ⊥, hP, finrank_bot F V⟩ (dimensionCapacity_bddAbove P)

end General

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A] {d : ℕ}

theorem IsSharedCode.mono {p : ZMod d → κ} {C D : Submodule F (State d A)}
    (hC : IsSharedCode F p C) (hD : D ≤ C) : IsSharedCode F p D := by
  obtain ⟨f, hf⟩ := hC
  exact ⟨f, fun X hX c => hf X (hD hX) c⟩

theorem IsLinearSharedCode.mono {p : ZMod d → κ} {C D : Submodule F (State d A)}
    (hC : IsLinearSharedCode p C) (hD : D ≤ C) : IsLinearSharedCode p D := by
  obtain ⟨f, hf⟩ := hC
  exact ⟨f, fun X hX c => hf X (hD hX) c⟩

theorem isSharedCode_bot (p : ZMod d → κ) :
    IsSharedCode F p (⊥ : Submodule F (State d A)) := by
  refine ⟨fun _ _ => 0, ?_⟩
  intro X hX c
  have hX' : X = 0 := hX
  subst X
  rfl

theorem isLinearSharedCode_bot (p : ZMod d → κ) :
    IsLinearSharedCode p (⊥ : Submodule F (State d A)) := by
  refine ⟨fun _ => 0, ?_⟩
  intro X hX c
  have hX' : X = 0 := hX
  subst X
  rfl

def completedLinearDecoder (p : ZMod d → κ) (r : κ → ZMod d)
    (f : κ → State d A →ₗ[F] (ZMod d → A)) (a : κ) :
    State d A →ₗ[F] (ZMod d → A) where
  toFun := completedDecoder (F := F) p r (fun j => f j) a
  map_add' X Y := by
    funext j
    simp only [completedDecoder, map_add, Pi.add_apply]
    rw [add_sub_add_comm, map_add]
    simp only [Pi.add_apply]
    abel
  map_smul' k X := by
    funext j
    simp only [completedDecoder, map_smul, Pi.smul_apply, RingHom.id_apply]
    rw [← smul_sub, map_smul]
    simp only [Pi.smul_apply, smul_add]

theorem IsLinearSharedCode.completedCode {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) {C : Submodule F (State d A)}
    (hC : IsLinearSharedCode p C) : IsLinearSharedCode p (completedCode p r C) := by
  obtain ⟨f, hf⟩ := hC
  exact ⟨completedLinearDecoder p r f, completedDecoder_correct hr (fun j => f j) hf⟩

variable [NeZero d] [Fintype κ] [FiniteDimensional F A]

theorem capacity_eq_residual_add {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) (P : Submodule F (State d A) → Prop)
    (hbot : P ⊥) (hmono : ∀ C D, P C → D ≤ C → P D)
    (hcomplete : ∀ C, P C → P (completedCode p r C)) :
    dimensionCapacity P = Fintype.card κ * d * finrank F A +
      dimensionCapacity (fun C => P C ∧ C ≤ LinearMap.ker (classProjection (F := F) p r)) := by
  let W := LinearMap.ker (classProjection (F := F) (A := A) p r)
  obtain ⟨C, hC, hdimC⟩ := dimensionCapacity_attained P hbot
  obtain ⟨D, hD, hdimD⟩ := dimensionCapacity_attained (fun D => P D ∧ D ≤ W)
    ⟨hbot, bot_le⟩
  have hleft := le_dimensionCapacity (P := fun D => P D ∧ D ≤ W)
    (C := C ⊓ W) ⟨hmono C _ hC inf_le_left, inf_le_right⟩
  have hc := finrank_le_completedCode hr C
  rw [finrank_completedCode hr] at hc
  have hright := le_dimensionCapacity (hcomplete D hD.1)
  rw [finrank_completedCode hr, inf_eq_left.mpr hD.2] at hright
  change finrank F C ≤ finrank F (C ⊓ W : Submodule F (State d A)) +
    Fintype.card κ * d * finrank F A at hc
  dsimp only [W] at hdimD hleft hc
  omega

theorem shared_capacity_eq_residual {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) :
    dimensionCapacity (IsSharedCode F (A := A) p) = Fintype.card κ * d * finrank F A +
      dimensionCapacity (fun C => IsSharedCode F p C ∧
        C ≤ LinearMap.ker (classProjection (F := F) (A := A) p r)) :=
  capacity_eq_residual_add hr _ (isSharedCode_bot p)
    (fun _ _ hC hD => hC.mono hD) (fun _ hC => hC.completedCode hr)

theorem linear_capacity_eq_residual {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) :
    dimensionCapacity (IsLinearSharedCode (F := F) (A := A) p) =
      Fintype.card κ * d * finrank F A +
      dimensionCapacity (fun C => IsLinearSharedCode p C ∧
        C ≤ LinearMap.ker (classProjection (F := F) (A := A) p r)) :=
  capacity_eq_residual_add hr _ (isLinearSharedCode_bot p)
    (fun _ _ hC hD => hC.mono hD) (fun _ hC => hC.completedCode hr)

theorem capacity_transversal_deficiency {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) (P : Submodule F (State d A) → Prop)
    (hcomplete : ∀ C, P C → P (completedCode p r C))
    {C : Submodule F (State d A)} (hC : P C) :
    finrank F C + Fintype.card κ * d * finrank F A ≤ dimensionCapacity P +
      finrank F (LinearMap.range ((classProjection p r).comp C.subtype)) := by
  have hh := le_dimensionCapacity (hcomplete C hC)
  have heq := finrank_completedCode_add_rank hr C
  omega

theorem optimal_transversal_full_rank {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) (P : Submodule F (State d A) → Prop)
    (hcomplete : ∀ C, P C → P (completedCode p r C))
    {C : Submodule F (State d A)} (hC : P C) (hopt : finrank F C = dimensionCapacity P) :
    finrank F (LinearMap.range ((classProjection p r).comp C.subtype)) =
      Fintype.card κ * d * finrank F A := by
  have hlo := capacity_transversal_deficiency hr P hcomplete hC
  have hran : LinearMap.range ((classProjection (F := F) (A := A) p r).comp C.subtype) ≤
      LinearMap.range (classProjection (F := F) (A := A) p r) :=
    LinearMap.range_comp_le_range _ _
  have hhi := Submodule.finrank_mono hran
  rw [finrank_classProjection_range hr] at hhi
  omega

end SharedDecoders
