import SharedDecoders.CompositionScatteredCompletion
import SharedDecoders.CompositionRobustAgreement

/-! # The sparse first factor requires a fully separated remaining factor -/

namespace SharedDecoders

open CapacityIntervals

variable {d : ℕ} [NeZero d] {A : Type*} [Zero A] [Fintype A]

omit [NeZero d] in
theorem columnPatch_comp_disagreement (hd : 2 ≤ d) (H : Equiv.Perm (State d A)) :
    disagreementCount (columnPatch hd ∘ H) H = 2*(Fintype.card A ^ d-1) := by
  rw [disagreementCount]
  let E := H.subtypeEquiv
    (p := fun X => (columnPatch hd ∘ H) X ≠ H X)
    (q := fun Y => columnPatch hd Y ≠ Y) (fun _ => Iff.rfl)
  rw [Nat.card_congr E]
  exact columnPatch_support_card hd

theorem scatteredFirstFactor_disagreement {b : ℕ} (hd : 2 ≤ d) :
    disagreementCount (scatteredFirstFactor (b := b) hd)
      (scatteredEquivariantCompletion hd) = 2*(2^(b*d)-1) := by
  have h := columnPatch_comp_disagreement hd (scatteredEquivariantCompletion (b := b) hd)
  change disagreementCount (columnPatch hd ∘ scatteredEquivariantCompletion hd)
    (scatteredEquivariantCompletion hd) = _
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul] using h

/-- The exact remaining factor for this complete extension must distinguish
every receiver when `d ≥ 3`. -/
theorem scattered_remaining_factor_singletons {b : ℕ} [NeZero b] {κ : Type*}
    (hd : 3 ≤ d) (p : ZMod d → κ)
    (K : State d (Fin b → Bit) → State d (Fin b → Bit)) (hK : ClassUniform p K)
    (hexact : ∀ X, K (scatteredFirstFactor (by omega : 2 ≤ d) X) = swap X) :
    Function.Injective p := by
  classical
  intro c e hp
  by_contra hce
  let q := Fintype.card (Fin b → Bit) ^ d
  let S := Fintype.card (State d (Fin b → Bit))
  have hq2 : 2 ≤ Fintype.card (Fin b → Bit) := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (NeZero.pos b)
    simpa using h
  have hq8 : 8 ≤ q := by
    have h₁ := Nat.pow_le_pow_left hq2 3
    have h₂ := Nat.pow_le_pow_right (by omega : 0 < Fintype.card (Fin b → Bit)) hd
    exact h₁.trans h₂
  have hS : S = q^d := by simp [S, q, ZMod.card]
  have hq3 : q^3 ≤ S := by
    rw [hS]
    exact Nat.pow_le_pow_right (by omega : 0 < q) hd
  have hzero : disagreementCount (K ∘ scatteredFirstFactor (by omega : 2 ≤ d)) swap = 0 := by
    unfold disagreementCount
    have hempty : IsEmpty {X : State d (Fin b → Bit) //
        (K ∘ scatteredFirstFactor (by omega : 2 ≤ d)) X ≠ swap X} :=
      ⟨fun X => X.property (hexact X.val)⟩
    exact Nat.card_eq_zero.mpr (Or.inl hempty)
  have hdiff := columnPatch_comp_disagreement (A := Fin b → Bit) (by omega : 2 ≤ d)
    (scatteredEquivariantCompletion (b := b) (by omega : 2 ≤ d))
  have hr := robust_repeated_class_count p
    (scatteredFirstFactor (b := b) (by omega : 2 ≤ d)) K
    (scatteredEquivariantCompletion (by omega : 2 ≤ d)) hK
    (scatteredCompletion_equivariant (by omega : 2 ≤ d)) hce hp
  change disagreementCount (scatteredFirstFactor (b := b) (by omega : 2 ≤ d))
    (scatteredEquivariantCompletion (by omega : 2 ≤ d)) = 2*(q-1) at hdiff
  rw [hzero, hdiff] at hr
  change 2*q*S ≤ (q+1)*S + 2*q*(0+2*(q-1)) at hr
  have hqsub : q-1+1=q := Nat.sub_add_cancel (by omega)
  have hS4 : S ≤ 4*q := by nlinarith
  have hqpos : 0<q := by omega
  have hq_sq : 16<q*q := by nlinarith
  nlinarith [Nat.mul_le_mul_left q hq_sq.le]

end SharedDecoders
