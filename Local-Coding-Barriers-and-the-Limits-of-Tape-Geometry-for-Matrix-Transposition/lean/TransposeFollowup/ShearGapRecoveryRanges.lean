import TransposeFollowup.ShearGapRecovery

/-! Reachable-state version of the shear recovery bound. Ambient state
spaces may be arbitrary; only the finite range on each helper branch is
charged. The capacity is real and no rounding is introduced. -/
namespace TransposeFollowup.ExpanderShear
open scoped BigOperators
open Classical
set_option autoImplicit false

theorem helper_recovery_gap_conditional_of_state_range_bits {Ω H : Type*} [Fintype Ω] [Fintype H] {m W : ℕ}
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → Bank m W) (L : Matrix (Fin m) (Fin m) Bit)
    (D : ℕ) (hrow : ∀ j, (Finset.univ.filter (fun i => L j i ≠ 0)).card ≤ D)
    (hcol : ∀ i, (Finset.univ.filter (fun j => L j i ≠ 0)).card ≤ D)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta2 : eta ≤ 2)
    (hexp : ∀ S : Finset (Row m), 2 * S.card ≤ 2 * m →
      eta * S.card ≤ (outsideNeighbors (coreGraph L) S).card)
    (z : Ω → H) (I J : H → Finset (Row m))
    (hI : ∀ a, (I a).card = m) (hJ : ∀ a, (J a).card = m)
    (R S : H → Row m → (Fin W → Bit) ≃ (Fin W → Bit))
    (State₁ State₂ : H → Type*)
    (s : H → ℝ) (state₁ : ∀ a, HelperFiber z a → State₁ a)
    (state₂ : ∀ a, HelperFiber z a → State₂ a)
    (hcap₁ : ∀ a, (Fintype.card (Set.range (state₁ a)) : ℝ) ≤ (2 : ℝ)^(s a))
    (hcap₂ : ∀ a, (Fintype.card (Set.range (state₂ a)) : ℝ) ≤ (2 : ℝ)^(s a))
    (decode₁ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a) (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a) (rowRecode (S a) (shear L (X ω))), state₁ a ω)))
    (decode₂ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a)ᶜ (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a)ᶜ (rowRecode (S a) (shear L (X ω))), state₂ a ω))) :
    eta / (4 * ((D : ℝ) + 1)^2) * (2 * m * W) -
      ((2 * m * W : ℝ) - conditionalObservationEntropy p X z / Real.log 2) ≤
        ∑ a, helperMass p z a * s a := by
  let r₁ (a : H) (ω : HelperFiber z a) : Set.range (state₁ a) := ⟨state₁ a ω,⟨ω,rfl⟩⟩
  let r₂ (a : H) (ω : HelperFiber z a) : Set.range (state₂ a) := ⟨state₂ a ω,⟨ω,rfl⟩⟩
  apply helper_recovery_gap_conditional_bits p hp hp1 X L D hrow hcol eta heta0 heta2 hexp
    z I J hI hJ R S (fun a => Set.range (state₁ a)) (fun a => Set.range (state₂ a))
    s r₁ r₂ hcap₁ hcap₂
  · intro a x y he
    have hh := congrArg (fun p => (p.1,p.2.val)) he
    exact decode₁ a hh
  · intro a x y he
    have hh := congrArg (fun p => (p.1,p.2.val)) he
    exact decode₂ a hh

theorem helper_recovery_gap_of_state_range_bits {Ω H : Type*} [Fintype Ω] [Fintype H] {m W : ℕ}
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → Bank m W) (L : Matrix (Fin m) (Fin m) Bit)
    (D : ℕ) (hrow : ∀ j, (Finset.univ.filter (fun i => L j i ≠ 0)).card ≤ D)
    (hcol : ∀ i, (Finset.univ.filter (fun j => L j i ≠ 0)).card ≤ D)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hexp : ∀ S : Finset (Row m), 2 * S.card ≤ 2 * m →
      eta * S.card ≤ (outsideNeighbors (coreGraph L) S).card)
    (z : Ω → H) (I J : H → Finset (Row m))
    (hI : ∀ a, (I a).card = m) (hJ : ∀ a, (J a).card = m)
    (R S : H → Row m → (Fin W → Bit) ≃ (Fin W → Bit))
    (State₁ State₂ : H → Type*)
    (s : ℝ) (state₁ : ∀ a, HelperFiber z a → State₁ a)
    (state₂ : ∀ a, HelperFiber z a → State₂ a)
    (hcap₁ : ∀ a, (Fintype.card (Set.range (state₁ a)) : ℝ) ≤ (2 : ℝ)^s)
    (hcap₂ : ∀ a, (Fintype.card (Set.range (state₂ a)) : ℝ) ≤ (2 : ℝ)^s)
    (decode₁ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a) (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a) (rowRecode (S a) (shear L (X ω))), state₁ a ω)))
    (decode₂ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a)ᶜ (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a)ᶜ (rowRecode (S a) (shear L (X ω))), state₂ a ω))) :
    eta / (8 * ((D : ℝ) + 1)^2) * (2 * m * W) -
      ((2 * m * W : ℝ) - observationEntropy p X / Real.log 2) -
        observationEntropy p z / Real.log 2 ≤ (s : ℝ) := by
  have h := helper_recovery_gap_conditional_of_state_range_bits p hp hp1 X L D hrow hcol
    eta heta0 (by linarith) hexp z I J hI hJ R S State₁ State₂ (fun _ => s)
    state₁ state₂ hcap₁ hcap₂ decode₁ decode₂
  rw [← Finset.sum_mul, sum_helperMass, hp1, one_mul] at h
  have hc := mul_le_mul_of_nonneg_right (recovery_coefficient_le_sharp D eta heta0)
    (show 0 ≤ (2 * m * W : ℝ) by positivity)
  exact (entropy_charge_le_conditional_budget p hp X z _ _ (2 * m * W) (Real.log 2)
    hc (Real.log_pos (by norm_num))).trans h

end TransposeFollowup.ExpanderShear
