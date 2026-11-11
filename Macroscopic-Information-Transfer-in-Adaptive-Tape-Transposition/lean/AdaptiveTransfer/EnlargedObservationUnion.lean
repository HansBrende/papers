import AdaptiveTransfer.EnlargedClasses
import AdaptiveTransfer.GetterMetadataRates

/-! A reusable union over bounded records of actual enlarged runs. Geometry
selection is deliberately separate: both the ordinary one-port constants and
the multiport radius constants supply their own proved selection witnesses.
-/

namespace AdaptiveTransfer.Enlarged
open Transpose MergeDepth NativeRelations Finset Getter
open scoped BigOperators

theorem actual_observation_union {Q Γ Λ : Type*} [Fintype Q] [Fintype Γ] [Fintype Λ]
    {p R d b T W N q z a : ℕ} (M : System Q Γ Λ 1 p R)
    (D : Finset (Fin (d * d * b) → Bool)) (labels : D → Λ) (finish : D → ℕ)
    (successful : ∀ X : D, ∀ t < finish X, M.instruction (labels X) (List.ofFn X.val) t ≠ none)
    (output : ∀ X : D, (M.run (labels X) (List.ofFn X.val) (finish X)).outRev.reverse =
      List.ofFn (fun j => X.val (tposOf d b j)))
    (obs : ∀ X : D, SlabObservation (M.motionTrace (labels X) (List.ofFn X.val)) T W N)
    (finish_le : ∀ X : D, (obs X).finish ≤ finish X)
    (hq : Fintype.card Q ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z) (hA : Fintype.card Γ ≤ 2 ^ a)
    (saving : ℝ)
    (margin : ∀ X : D, saving ≤
      ((omittedPortBits (d := d) (b := b) (M.portPaths (labels X) (List.ofFn X.val))
        (fun j => appendTime (M.motionTrace (labels X) (List.ofFn X.val)) (finish X) j.val)
        (obs X).times (obs X).finish R).card : ℝ) -
      (a : ℝ) * (if (obs X).start = 0 then 0 else (W : ℝ))) :
    (D.card : ℝ) ≤ (portMetadataSize 1 p T W N : ℝ) *
      (2 : ℝ) ^ ((d * d * b : ℕ) - saving + z + (N : ℝ) * q) := by
  classical
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, card_empty, Nat.cast_zero]; positivity
  let X₀ : D := ⟨hD.choose, hD.choose_spec⟩
  let encodeObs (X : D) := Observation.encode (obs X) (M.portPaths (labels X) (List.ofFn X.val))
    M.origins (M.portPaths_walk _ _) (M.portPaths_zero _ _)
  let encoding (X : Fin (d * d * b) → Bool) : PortMetadata 1 p T W N :=
    if hX : X ∈ D then encodeObs ⟨X, hX⟩ else encodeObs X₀
  have henc (X : D) : encoding X.val = encodeObs X := by simp only [encoding, dite_eq_left X.property]
  let cost : ℝ := (2 : ℝ) ^ ((d * d * b : ℕ) - saving + z + (N : ℝ) * q)
  have hfibre (σ : PortMetadata 1 p T W N) :
      ((D.filter fun X => encoding X = σ).card : ℝ) ≤ cost := by
    let F := D.filter fun X => encoding X = σ
    rcases F.eq_empty_or_nonempty with hF | hF
    · change (F.card : ℝ) ≤ cost
      rw [hF, card_empty, Nat.cast_zero]; dsimp [cost]; positivity
    let lift (X : F) : D := ⟨X.val, (mem_filter.mp X.property).1⟩
    let X₁ : F := ⟨hF.choose, hF.choose_spec⟩
    have hsame (X : F) : encodeObs (lift X) = encodeObs (lift X₁) := by
      rw [← henc (lift X), ← henc (lift X₁)]
      exact (mem_filter.mp X.property).2.trans (mem_filter.mp X₁.property).2.symm
    exact class_saving_bound M F (fun X => labels (lift X)) (fun X => finish (lift X))
      (fun X => successful (lift X)) (fun X => output (lift X)) (fun X => obs (lift X))
      (fun X => finish_le (lift X)) X₁ hsame q z a hq hz hA saving (margin (lift X₁))
  have hcard : D.card = ∑ σ : PortMetadata 1 p T W N, (D.filter fun X => encoding X = σ).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ _σ : PortMetadata 1 p T W N, cost := sum_le_sum (fun σ _ => hfibre σ)
    _ = _ := by simp only [sum_const, card_univ, portMetadata_card, nsmul_eq_mul]; rfl

end AdaptiveTransfer.Enlarged
