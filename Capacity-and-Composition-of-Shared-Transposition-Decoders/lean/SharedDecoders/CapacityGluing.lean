import SharedDecoders.CapacityCompletion

/-! # Exact deterministic gluing of the demanded row maps -/

namespace SharedDecoders

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A] {d : ℕ}

/-- A total deterministic decoder exists exactly when identical same-class
views make identical row demands. No compatibility of sums of views is used. -/
theorem isSharedCode_iff_compatible {p : ZMod d → κ}
    {C : Submodule F (State d A)} : IsSharedCode F p C ↔
    ∀ X ∈ C, ∀ Y ∈ C, ∀ c e, p c = p e → rot c X = rot e Y → X c = Y e := by
  classical
  constructor
  · rintro ⟨f, hf⟩ X hX Y hY c e hp hview
    rw [hf X hX c, hf Y hY e, hp, hview]
  · intro h
    let P : κ → State d A → (State d A × ZMod d) → Prop :=
      fun a Y z => z.1 ∈ C ∧ p z.2 = a ∧ rot z.2 z.1 = Y
    let f : κ → State d A → (ZMod d → A) := fun a Y =>
      if hw : ∃ z, P a Y z then (Classical.choose hw).1 (Classical.choose hw).2 else 0
    refine ⟨f, ?_⟩
    intro X hX c
    have hw : ∃ z, P (p c) (rot c X) z := ⟨(X, c), hX, rfl, rfl⟩
    dsimp [f]
    rw [dite_eq_left hw]
    obtain ⟨hZ, hp, hview⟩ := Classical.choose_spec hw
    exact h X hX _ hZ c _ hp.symm hview.symm

theorem IsSharedCode.of_disjoint_views {p : ZMod d → κ}
    {C : Submodule F (State d A)}
    (hsep : ∀ c e : ZMod d, c ≠ e →
      Disjoint (C.map (rotLinear F c)) (C.map (rotLinear F e))) :
    IsSharedCode F p C := by
  apply isSharedCode_iff_compatible.mpr
  intro X hX Y hY c e _ hview
  by_cases hce : c = e
  · subst e
    have heq : X = Y := (rotEquiv c).injective hview
    rw [heq]
  · have hz : rot c X = 0 := (Submodule.disjoint_def.mp (hsep c e hce))
      (rot c X) ⟨X, hX, rfl⟩ ⟨Y, hY, hview.symm⟩
    have hX0 : X = 0 := by
      have hh := congrArg (rot (-c)) hz
      simpa only [rot_neg_rot, show rot (-c) (0 : State d A) = 0 from rfl] using hh
    have hY0 : Y = 0 := by
      have hh := congrArg (rot (-e)) (hview.symm.trans hz)
      simpa only [rot_neg_rot, show rot (-e) (0 : State d A) = 0 from rfl] using hh
    simp [hX0, hY0]

end SharedDecoders
