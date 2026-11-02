import AboveHalfRate.Incidence

/-!
# Binary codes by blow-up

A storage code over an alphabet `A` becomes a binary storage code by writing each symbol in `b`
bits through an injection `ι : A → (Fin b → Bool)`. The coordinates become pairs `(p, i)` with
`i : Fin b`, and the bit `(p, i)` is recovered from all bits of the recovery set of `p`
(`blowUp N b`). Then:

* `isStorageCode_blowCode`: the encoded code is a binary storage code for the blow-up;
* `card_blowCode`: it has as many words as the original code;
* `degree_blowUp_le`: incidence degrees are multiplied by at most `b`;
* `edist_le_blowUp`: paired distances do not decrease, since forgetting the bit index is a
  homomorphism of paired incidence graphs; so short coordinates of the blow-up lie over short
  coordinates of the original relation (`shortPairedCoordinates_blowUp_subset`).
-/

namespace AboveHalf

open Finset DirectedRecovery MotionDepthCodes

set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Type*} {b : ℕ}

/-- The blow-up of a relation: the bit `(p, i)` is recovered from all bits of `N p`. -/
def blowUp (N : V → Finset V) (b : ℕ) (x : V × Fin b) : Finset (V × Fin b) :=
  N x.1 ×ˢ Finset.univ

/-- Bitwise encoding of a word through `ι`. -/
def encodeWord (ι : A → Fin b → Bool) (c : V → A) : V × Fin b → Bool := fun x => ι (c x.1) x.2

omit [Fintype V] [DecidableEq V] in
theorem encodeWord_injective {ι : A → Fin b → Bool} (hι : Function.Injective ι) :
    Function.Injective (encodeWord (V := V) ι) := by
  intro c₁ c₂ h
  funext p
  apply hι
  funext i
  exact congrFun h (p, i)

omit [DecidableEq V] in
/-- The binary code obtained by encoding every word. -/
def blowCode (ι : A → Fin b → Bool) (C : Finset (V → A)) : Finset (V × Fin b → Bool) :=
  C.image (encodeWord ι)

omit [DecidableEq V] in
/-- Encoding is injective on words, so the binary code has as many words as the original. -/
theorem card_blowCode {ι : A → Fin b → Bool} (hι : Function.Injective ι) (C : Finset (V → A)) :
    (blowCode ι C).card = C.card := by
  unfold blowCode
  exact Finset.card_image_of_injective _ (encodeWord_injective hι)

omit [DecidableEq V] in
/-- **The blow-up of a storage code is a binary storage code.** -/
theorem isStorageCode_blowCode {N : V → Finset V} {C : Finset (V → A)}
    (hC : IsStorageCode N C) {ι : A → Fin b → Bool} (hι : Function.Injective ι) :
    IsStorageCode (blowUp N b) (blowCode ι C) := by
  intro x₁ hx₁ x₂ hx₂ v hagree
  unfold blowCode at hx₁ hx₂
  obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_image.1 hx₁
  obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_image.1 hx₂
  have hrec : ∀ u ∈ N v.1, c₁ u = c₂ u := by
    intro u hu
    apply hι
    funext i
    exact hagree (u, i) (Finset.mem_product.2 ⟨hu, Finset.mem_univ _⟩)
  simp only [encodeWord]
  rw [hC c₁ hc₁ c₂ hc₂ v.1 hrec]

/-- **Degrees.** The incidence degrees of the blow-up are at most `b` times those of `N`. -/
theorem degree_blowUp_le (N : V → Finset V) {Δ : ℕ}
    (hout : ∀ q, (N q).card ≤ Δ) (hin : ∀ p, (Finset.univ.filter (fun q => p ∈ N q)).card ≤ Δ)
    (v : (V × Fin b) ⊕ (V × Fin b))
    [Fintype ((pairedIncidenceGraph (blowUp N b)).neighborSet v)] :
    (pairedIncidenceGraph (blowUp N b)).degree v ≤ b * Δ := by
  refine degree_le_of_bounds (blowUp N b) (fun q => ?_) (fun p => ?_) v
  · rw [blowUp, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
    exact Nat.mul_le_mul_left _ (hout q.1)
  · have : Finset.univ.filter (fun q : V × Fin b => p ∈ blowUp N b q) =
        (Finset.univ.filter (fun q => p.1 ∈ N q)) ×ˢ Finset.univ := by
      ext q; simp [blowUp]
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
    exact Nat.mul_le_mul_left _ (hin p.1)

/-- Forgetting the bit index maps the paired incidence graph of the blow-up to that of `N`. -/
def forgetBit (N : V → Finset V) :
    pairedIncidenceGraph (blowUp N b) →g pairedIncidenceGraph N where
  toFun := Sum.map Prod.fst Prod.fst
  map_rel' := by
    intro u v h
    rcases u with ⟨p, i⟩ | ⟨q, j⟩ <;> rcases v with ⟨p', i'⟩ | ⟨q', j'⟩ <;>
      simp_all [blowUp]

omit [Fintype V] [DecidableEq V] in
/-- **Paired distances do not decrease** under blow-up. -/
theorem edist_le_blowUp (N : V → Finset V) (x : V × Fin b) :
    (pairedIncidenceGraph N).edist (Sum.inl x.1) (Sum.inr x.1) ≤
      (pairedIncidenceGraph (blowUp N b)).edist (Sum.inl x) (Sum.inr x) :=
  edist_map_le (forgetBit N) (Sum.inl x) (Sum.inr x)

omit [DecidableEq V] in
/-- Short coordinates of the blow-up lie over short coordinates of `N`. -/
theorem shortPairedCoordinates_blowUp_subset (N : V → Finset V) (K : ℕ) :
    shortPairedCoordinates (blowUp N b) K ⊆ shortPairedCoordinates N K ×ˢ Finset.univ := by
  intro x hx
  simp only [shortPairedCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [Finset.mem_product, shortPairedCoordinates, Finset.mem_filter, Finset.mem_univ,
    true_and, and_true]
  exact (edist_le_blowUp N x).trans hx

end AboveHalf
