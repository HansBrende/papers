import SubcodeSelection
import TransposeFollowup.FullFiberEntropy

/-!
# An exact subcode in one record fibre

Add one dependency saying that the record is determined by a constant helper,
then apply the generic selector to distinct joint word/record observations.
The selected record is constant, so projection to words preserves cardinality.
This yields the stronger price H(X | Z) minus the conditional recovery errors;
the previously stated H(X) - H(Z) target follows by entropy monotonicity.
-/

namespace LeanBacklog.ConditionalSubcode

open Finset MotionDepthCodes TransposeFollowup EntropyConsolidation SubcodeSelection
open scoped BigOperators
set_option autoImplicit false

/-- An exact storage code inside one positive-support record fibre. The record
may be correlated with the word without being a deterministic function of it. -/
theorem conditional_subcode_selection {V Ω α β : Type}
    [DecidableEq V] [Fintype V] [Fintype Ω] [Fintype α] [Fintype β]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → V → α) (Z : Ω → β) (H : V → Finset V) :
    ∃ (z : β) (D : Finset (V → α)), D.Nonempty ∧
      (∀ x ∈ D, ∃ ω, 0 < p ω ∧ Z ω = z ∧ X ω = x) ∧
      IsStorageCode H D ∧
      conditionalObservationEntropy p X Z -
        (∑ v, conditionalObservationEntropy p (fun ω => X ω v)
          (fun ω => (view (H v) (X ω), Z ω))) ≤ Real.log D.card := by
  classical
  obtain ⟨ω₀, _⟩ := exists_pos_mass p hp hp1
  let : Nonempty Ω := ⟨ω₀⟩
  let : Nonempty (V → α) := ⟨X ω₀⟩
  let : Nonempty β := ⟨Z ω₀⟩
  let C : Option V → Type _ := fun i => match i with
    | none => β
    | some _ => α
  let B : Option V → Type _ := fun i => match i with
    | none => Unit
    | some _ => (V → Option α) × β
  let : ∀ i, Fintype (C i) := fun i => by
    cases i <;> dsimp [C] <;> infer_instance
  let : ∀ i, Fintype (B i) := fun i => by
    cases i <;> dsimp [B] <;> infer_instance
  let f : ∀ i, ((V → α) × β) → C i
    | none, x => x.2
    | some v, x => x.1 v
  let g : ∀ i, ((V → α) × β) → B i
    | none, _ => ()
    | some v, x => (view (H v) x.1, x.2)
  let U : Ω → (V → α) × β := fun ω => (X ω, Z ω)
  obtain ⟨E, hE, hs, hd, he⟩ := exists_observed_dependency_subset p hp hp1 U f g
  obtain ⟨e₀, he₀⟩ := hE
  let z := e₀.2
  have hz : ∀ e ∈ E, e.2 = z := by
    intro e he'
    exact hd none e he' e₀ he₀ rfl
  let D := E.image Prod.fst
  have hD : D.Nonempty := ⟨e₀.1, mem_image.mpr ⟨e₀, he₀, rfl⟩⟩
  have hcard : D.card = E.card := by
    apply card_image_iff.mpr
    intro x hx y hy hxy
    exact Prod.ext hxy ((hz x hx).trans (hz y hy).symm)
  refine ⟨z, D, hD, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he', rfl⟩ := mem_image.mp hx
    obtain ⟨ω, hω, hU⟩ := hs e he'
    refine ⟨ω, hω, ?_, ?_⟩
    · exact (congrArg Prod.snd hU).trans (hz e he')
    · exact congrArg Prod.fst hU
  · intro x hx y hy v hxy
    obtain ⟨e, he', rfl⟩ := mem_image.mp hx
    obtain ⟨e', he'', rfl⟩ := mem_image.mp hy
    apply hd (some v) e he' e' he''
    change (view (H v) e.1, e.2) = (view (H v) e'.1, e'.2)
    exact Prod.ext ((view_eq_iff _ _ _).mpr hxy) ((hz e he').trans (hz e' he'').symm)
  · have hsum :
        (∑ i : Option V, conditionalObservationEntropy p (fun ω => f i (U ω))
          (fun ω => g i (U ω))) = observationEntropy p Z +
          ∑ v, conditionalObservationEntropy p (fun ω => X ω v)
            (fun ω => (view (H v) (X ω), Z ω)) := by
      rw [Fintype.sum_option]
      change conditionalObservationEntropy p Z (fun _ => ()) +
        (∑ v, conditionalObservationEntropy p (fun ω => X ω v)
          (fun ω => (view (H v) (X ω), Z ω))) = _
      rw [conditionalObservationEntropy_const_condition p hp hp1 Z ()]
    rw [hsum] at he
    have hswap : observationEntropy p U =
        observationEntropy p (fun ω => (Z ω, X ω)) :=
      observationEntropy_pair_swap p hp X Z
    rw [hcard, conditionalObservationEntropy, ← hswap]
    linarith only [he]

/-- The original record-fibre target, with precisely its original hypotheses. -/
theorem conditionalSubcodeSelectionTarget {V : Type} [DecidableEq V] [Fintype V] :
    ConditionalSubcodeSelectionTarget (V := V) := by
  intro Ω α β _ _ _ _ p hp hp1 X Z H
  obtain ⟨ω₀, _⟩ := exists_pos_mass p hp hp1
  let : Nonempty Ω := ⟨ω₀⟩
  obtain ⟨z, D, hD, hs, hc, he⟩ := conditional_subcode_selection p hp hp1 X Z H
  refine ⟨z, D, hD, hs, hc, ?_⟩
  have hX : observationEntropy p X ≤
      observationEntropy p (fun ω => (Z ω, X ω)) := by
    simpa only [Function.comp_def] using
      observationEntropy_comp_le p hp (fun ω => (Z ω, X ω)) Prod.snd
  rw [codeEntropy_univ_eq_observationEntropy p hp X]
  unfold conditionalObservationEntropy at he ⊢
  linarith only [hX, he]

end LeanBacklog.ConditionalSubcode

#print axioms LeanBacklog.ConditionalSubcode.conditional_subcode_selection
#print axioms LeanBacklog.ConditionalSubcode.conditionalSubcodeSelectionTarget
