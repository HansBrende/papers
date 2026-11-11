import SharedDecoders.CompositionAgreement
import SharedDecoders.CompositionAnchoredEndpoint

/-! # Robust composition from complete-input disagreement counts -/

namespace SharedDecoders

variable {d : ℕ} [NeZero d] {A κ : Type*} [Fintype A]

noncomputable def disagreementCount (F G : State d A → State d A) : ℕ :=
  Nat.card {X : State d A // F X ≠ G X}

/-- The comparison map is arbitrary: no injectivity or surjectivity is used. -/
theorem agreement_error_cover (K₁ K₂ H : State d A → State d A) :
    Fintype.card (State d A) ≤ (correctInputs (K₂ ∘ H)).card +
      disagreementCount (K₂ ∘ K₁) swap + disagreementCount K₁ H := by
  classical
  let E := Finset.univ.filter (fun X : State d A => K₂ (K₁ X) ≠ swap X)
  let D := Finset.univ.filter (fun X : State d A => K₁ X ≠ H X)
  have he : Finset.univ = (correctInputs (K₂ ∘ H) ∪ E) ∪ D := by
    ext X
    simp only [Finset.mem_univ, Finset.mem_union, true_iff]
    by_cases hD : K₁ X = H X
    · by_cases hE : K₂ (K₁ X) = swap X
      · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa only [Function.comp_apply, ← hD] using hE⟩))
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩))
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩)
  have h := (Finset.card_union_le (correctInputs (K₂ ∘ H) ∪ E) D).trans
    (Nat.add_le_add_right (Finset.card_union_le (correctInputs (K₂ ∘ H)) E) D.card)
  rw [← he, Finset.card_univ] at h
  simpa [E, D, disagreementCount, Nat.card_eq_fintype_card, Fintype.card_subtype] using h

/-- Integer form of the robust arbitrary-class inequality. Dividing by
`2*d*q*|V|` gives `failure + disagreement ≥ 1 - B(p)`. -/
theorem robust_full_input_count [Fintype κ] (p : ZMod d → κ)
    (K₁ K₂ H : State d A → State d A) (hK : ClassUniform p K₂) (hH : Equivariant H) :
    2*d*(Fintype.card A ^ d)*Fintype.card (State d A) ≤
      (2*Fintype.card κ*(Fintype.card A ^ d) +
        ∑ J : κ, receiverClassSize p J * (receiverClassSize p J - 1)) *
          Fintype.card (State d A) +
      2*d*(Fintype.card A ^ d) *
        (disagreementCount (K₂ ∘ K₁) swap + disagreementCount K₁ H) := by
  have hc := full_input_agreement_count p (K₂ ∘ H) (hK.comp_equivariant hH)
  have hcover := Nat.mul_le_mul_left (2*d*(Fintype.card A ^ d))
    (agreement_error_cover K₁ K₂ H)
  nlinarith

/-- Integer form of `failure + disagreement ≥ (1 - 1/q)/2` for any
repeated receiver class. The equivariant comparison may be singular. -/
theorem robust_repeated_class_count (p : ZMod d → κ)
    (K₁ K₂ H : State d A → State d A) (hK : ClassUniform p K₂) (hH : Equivariant H)
    {c e : ZMod d} (hce : c ≠ e) (hp : p c = p e) :
    2*(Fintype.card A ^ d)*Fintype.card (State d A) ≤
      (Fintype.card A ^ d+1)*Fintype.card (State d A) +
      2*(Fintype.card A ^ d) *
        (disagreementCount (K₂ ∘ K₁) swap + disagreementCount K₁ H) := by
  have hc := repeated_class_agreement_count p (K₂ ∘ H) (hK.comp_equivariant hH) hce hp
  have hcover := Nat.mul_le_mul_left (2*(Fintype.card A ^ d))
    (agreement_error_cover K₁ K₂ H)
  nlinarith

end SharedDecoders
