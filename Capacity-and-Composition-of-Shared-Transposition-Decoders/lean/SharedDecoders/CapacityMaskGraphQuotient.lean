import SharedDecoders.CapacityMaskFinite

/-! # Explicit classifiers of the actual translate-link quotient -/

namespace SharedDecoders.CapacityMaskGraph

variable {d : ℕ} [NeZero d] {κ ι : Type*}

omit [NeZero d] in
theorem label_of_connected {p : ZMod d → κ} {Δ : Finset (ZMod d)} {x y : ZMod d}
    (h : Relation.EqvGen (Link p Δ) x y) : p x=p y := by
  induction h with
  | rel _ _ h => exact h.1
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

omit [NeZero d] in
theorem connected_mono {p : ZMod d → κ} {Δ Γ : Finset (ZMod d)} (hΔ : Δ⊆Γ)
    {x y : ZMod d} (h : Relation.EqvGen (Link p Δ) x y) : Relation.EqvGen (Link p Γ) x y := by
  apply Relation.EqvGen.mono (fun _ _ hl => ?_) x y h
  obtain ⟨hp,u,hu,v,hv,he⟩ := hl
  exact ⟨hp,u,hΔ hu,v,hΔ hv,he⟩

/-- An explicitly proved component classifier computes the actual quotient.
The equivalence hypothesis here is discharged by paths and edge invariants
in the concrete mask modules. -/
theorem componentCount_eq_card [Fintype ι] (p : ZMod d → κ) (Δ : Finset (ZMod d))
    (f : ZMod d → ι) (hsurj : Function.Surjective f)
    (hrel : ∀ x y, Relation.EqvGen (Link p Δ) x y ↔ f x=f y) :
    componentCount p Δ=Fintype.card ι := by
  let q : LinkComponent p Δ → ι := Quotient.lift f (fun x y h => (hrel x y).mp h)
  have hq : Function.Bijective q := by
    constructor
    · intro x y h
      induction x using Quotient.inductionOn with
      | h x =>
        induction y using Quotient.inductionOn with
        | h y => exact Quotient.sound ((hrel x y).mpr h)
    · intro a
      obtain ⟨x,hx⟩ := hsurj a
      exact ⟨Quotient.mk _ x,hx⟩
  exact Fintype.card_congr (Equiv.ofBijective q hq)

end SharedDecoders.CapacityMaskGraph
