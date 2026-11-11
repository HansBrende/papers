import SharedDecoders.Model

/-! # Exact deterministic consistency on arbitrary correctness sets

This totalizes actual view requirements, without linearity or evaluation-cost
assumptions. The orbit counting application has a separate written proof.
-/

namespace SharedDecoders

theorem exists_decoder_iff_consistent {X I V Y : Type*} [Nonempty Y]
    (C : Set X) (view : I → X → V) (demand : I → X → Y) :
    (∃ f : V → Y, ∀ x ∈ C, ∀ i, f (view i x) = demand i x) ↔
      (∀ x ∈ C, ∀ y ∈ C, ∀ i j, view i x = view j y → demand i x = demand j y) := by
  classical
  constructor
  · rintro ⟨f, hf⟩ x hx y hy i j hij
    rw [← hf x hx i, ← hf y hy j, hij]
  · intro h
    let Q (v : V) := {p : X × I // p.1 ∈ C ∧ view p.2 p.1 = v}
    let f : V → Y := fun v => if hv : Nonempty (Q v) then
      demand (Classical.choice hv).1.2 (Classical.choice hv).1.1 else Classical.choice inferInstance
    refine ⟨f, ?_⟩
    intro x hx i
    have hv : Nonempty (Q (view i x)) := ⟨⟨(x,i), hx, rfl⟩⟩
    dsimp [f]
    rw [dite_eq_left hv]
    exact h _ (Classical.choice hv).2.1 x hx _ i (Classical.choice hv).2.2

/-- Every proposed cyclic set is checked against every actual equality of views. -/
theorem exists_cyclic_set_decoder_iff {d : ℕ} {A : Type*} [Nonempty A]
    (C : Set (State d A)) :
    (∃ f : State d A → (ZMod d → A), ∀ X ∈ C, ∀ c, f (rot c X) = X c) ↔
      (∀ X ∈ C, ∀ Y ∈ C, ∀ c e, rot c X = rot e Y → X c = Y e) :=
  exists_decoder_iff_consistent C rot (fun c X => X c)

end SharedDecoders
