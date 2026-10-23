import TransposeFollowup.ShearGap
import TransposeFollowup.ConditionalEntropyFibers
import TransposeFollowup.PacketInformation

/-! Nonlinear recovery states and helper-selected row orders. The helper
entropy is charged; row recodings are separately bijective within each row. -/
namespace TransposeFollowup.ExpanderShear
open scoped BigOperators
open Classical
set_option autoImplicit false

def rowRecode {α : Type*} {W : ℕ}
    (R : α → (Fin W → Bit) ≃ (Fin W → Bit))
    (x : α → Fin W → Bit) : α → Fin W → Bit := fun r => R r (x r)

theorem rowRecode_injective {α : Type*} {W : ℕ}
    (R : α → (Fin W → Bit) ≃ (Fin W → Bit)) : Function.Injective (rowRecode R) := by
  intro x y h
  funext r
  exact (R r).injective (congrFun h r)

theorem observationEntropy_rowRecode_eq {Ω α : Type*} [Fintype Ω] [Fintype α]
    {W : ℕ} (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (X : Ω → α → Fin W → Bit) (R : α → (Fin W → Bit) ≃ (Fin W → Bit)) :
    observationEntropy p (fun ω => rowRecode R (X ω)) = observationEntropy p X := by
  apply observationEntropy_eq_of_same_fibers p hp
  intro x y
  exact (rowRecode_injective R).eq_iff

theorem rowView_recode_same_fibers {α : Type*} [Fintype α] [DecidableEq α] {W : ℕ}
    (I : Finset α) (R : α → (Fin W → Bit) ≃ (Fin W → Bit))
    (x y : α → Fin W → Bit) :
    rowView I (rowRecode R x) = rowView I (rowRecode R y) ↔ rowView I x = rowView I y := by
  constructor
  · intro h
    funext i w
    have he := (R i).injective (congrFun h i)
    exact congrFun he w
  · intro h
    funext i
    exact congrArg (R i) (congrFun h i)

theorem conditional_rowView_recode_eq {Ω α : Type*} [Fintype Ω] [Fintype α]
    [DecidableEq α] {W : ℕ} (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (I J : Finset α) (X Y : Ω → α → Fin W → Bit)
    (R S : α → (Fin W → Bit) ≃ (Fin W → Bit)) :
    conditionalObservationEntropy p (fun ω => rowView I (rowRecode R (X ω)))
      (fun ω => rowView J (rowRecode S (Y ω))) =
    conditionalObservationEntropy p (fun ω => rowView I (X ω))
      (fun ω => rowView J (Y ω)) := by
  rw [conditionalObservationEntropy_eq_of_same_fibers p hp
    (fun ω => rowView I (rowRecode R (X ω))) (fun ω => rowView I (X ω))
    (fun ω => rowView J (rowRecode S (Y ω)))
    (fun x y _ => rowView_recode_same_fibers I R (X x) (X y))]
  exact conditionalObservationEntropy_condition_eq_of_same_fibers p hp _ _ _
    (fun x y => rowView_recode_same_fibers J S (Y x) (Y y))

/-- A finite-valued nonlinear state supplies no more information than its
logarithmic cardinality budget. The real budget incurs no integer rounding. -/
theorem conditional_entropy_le_state_budget {Ω A C S : Type*}
    [Fintype Ω] [Fintype A] [Fintype C] [Fintype S]
    [Nonempty A] [Nonempty C] [Nonempty S]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (f : Ω → A) (w : Ω → C) (s : ℝ) (state : Ω → S)
    (hcap : (Fintype.card S : ℝ) ≤ (2 : ℝ)^s)
    (hdecode : f.FactorsThrough (fun ω => (w ω, state ω))) :
    conditionalObservationEntropy p f w ≤ s * Real.log 2 := by
  have h₁ := conditionalObservationEntropy_le_of_factorsThrough p hp f state w hdecode
  have h₂ := conditionalObservationEntropy_le_observation p hp hp1 state w
  have h₃ := entropy_le_log_card (pushforward p state)
    (pushforward_nonneg p hp state) (by rw [sum_pushforward, hp1])
  have hpos : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hc := Real.log_le_log hpos hcap
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hc
  exact h₁.trans (h₂.trans (h₃.trans hc))

/-- Exact conditional-source bound for an arbitrary joint source/helper law.
The helper may choose both row sets and all within-row recodings; each branch has
its own common budget for the two recovery states. Only the average is charged. -/
theorem helper_recovery_gap_conditional {Ω H : Type*} [Fintype Ω] [Fintype H] {m W : ℕ}
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
    (State₁ State₂ : H → Type*) [∀ a, Fintype (State₁ a)] [∀ a, Fintype (State₂ a)]
    (s : H → ℝ) (state₁ : ∀ a, HelperFiber z a → State₁ a)
    (state₂ : ∀ a, HelperFiber z a → State₂ a)
    (hcap₁ : ∀ a, (Fintype.card (State₁ a) : ℝ) ≤ (2 : ℝ)^(s a))
    (hcap₂ : ∀ a, (Fintype.card (State₂ a) : ℝ) ≤ (2 : ℝ)^(s a))
    (decode₁ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a) (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a) (rowRecode (S a) (shear L (X ω))), state₁ a ω)))
    (decode₂ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a)ᶜ (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a)ᶜ (rowRecode (S a) (shear L (X ω))), state₂ a ω))) :
    eta / (4 * ((D : ℝ) + 1)^2) * (2 * m * W) * Real.log 2 -
      ((2 * m * W : ℝ) * Real.log 2 - conditionalObservationEntropy p X z) ≤
        (∑ a, helperMass p z a * s a) * Real.log 2 := by
  let C : ℝ := eta / (4 * ((D : ℝ) + 1)^2) * (2 * m * W) * Real.log 2
  let P : ℝ := (2 * m * W : ℝ) * Real.log 2
  have hbranch (a : H) (ha : 0 < helperMass p z a) :
      C - P + observationEntropy (helperConditionalWeight p z a)
        (fun ω : HelperFiber z a => X ω) ≤ s a * Real.log 2 := by
    let : Nonempty (HelperFiber z a) := helperFiber_nonempty_of_mass_pos p z a ha
    let : Nonempty (State₁ a) := Nonempty.map (state₁ a) inferInstance
    let : Nonempty (State₂ a) := Nonempty.map (state₂ a) inferInstance
    let q := helperConditionalWeight p z a
    have hq := helperConditionalWeight_nonneg p hp z a
    have hq1 := sum_helperConditionalWeight p z a ha.ne'
    have hg := balanced_conditional_gap_sharp q hq hq1
      (fun ω : HelperFiber z a => X ω) L D hrow hcol eta heta0 heta2 hexp
      (I a) (J a) (hI a) (hJ a)
    have hc₁ := conditional_entropy_le_state_budget q hq hq1 _ _ (s a)
      (state₁ a) (hcap₁ a) (decode₁ a)
    have hc₂ := conditional_entropy_le_state_budget q hq hq1 _ _ (s a)
      (state₂ a) (hcap₂ a) (decode₂ a)
    rw [conditional_rowView_recode_eq] at hc₁ hc₂
    · have hm := max_le hc₁ hc₂
      dsimp [C, P]
      linarith
    all_goals exact hq
  have hsum : (∑ a, helperMass p z a *
      (C - P + observationEntropy (helperConditionalWeight p z a)
        (fun ω : HelperFiber z a => X ω))) ≤
      ∑ a, helperMass p z a * (s a * Real.log 2) := by
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : helperMass p z a = 0
    · simp [ha]
    · exact mul_le_mul_of_nonneg_left (hbranch a
        (lt_of_le_of_ne (helperMass_nonneg p hp z a) (Ne.symm ha)))
        (helperMass_nonneg p hp z a)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_helperMass, hp1, one_mul, sum_helperMass_mul_observationEntropy p hp] at hsum
  change C - (P - conditionalObservationEntropy p X z) ≤ _
  calc
    _ = C - P + conditionalObservationEntropy p X z := by ring
    _ ≤ _ := hsum.trans_eq (by simp only [mul_assoc, Finset.sum_mul])

/-- In bits, the deficit is P - H(X | Z), equivalently the source deficit
plus I(X; Z). No determinism of the helper from X is assumed. -/
theorem helper_recovery_gap_conditional_bits {Ω H : Type*} [Fintype Ω] [Fintype H] {m W : ℕ}
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
    (State₁ State₂ : H → Type*) [∀ a, Fintype (State₁ a)] [∀ a, Fintype (State₂ a)]
    (s : H → ℝ) (state₁ : ∀ a, HelperFiber z a → State₁ a)
    (state₂ : ∀ a, HelperFiber z a → State₂ a)
    (hcap₁ : ∀ a, (Fintype.card (State₁ a) : ℝ) ≤ (2 : ℝ)^(s a))
    (hcap₂ : ∀ a, (Fintype.card (State₂ a) : ℝ) ≤ (2 : ℝ)^(s a))
    (decode₁ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a) (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a) (rowRecode (S a) (shear L (X ω))), state₁ a ω)))
    (decode₂ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a)ᶜ (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a)ᶜ (rowRecode (S a) (shear L (X ω))), state₂ a ω))) :
    eta / (4 * ((D : ℝ) + 1)^2) * (2 * m * W) -
      ((2 * m * W : ℝ) - conditionalObservationEntropy p X z / Real.log 2) ≤
        ∑ a, helperMass p z a * s a := by
  have h := helper_recovery_gap_conditional p hp hp1 X L D hrow hcol eta heta0 heta2
    hexp z I J hI hJ R S State₁ State₂ s state₁ state₂ hcap₁ hcap₂ decode₁ decode₂
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd := (div_le_iff₀ hlog).mpr h
  convert hd using 1
  field_simp

/-- Replacing the exact conditional deficit by source deficit plus helper
entropy only weakens a bound. The positive unit supports either nats or bits. -/
theorem entropy_charge_le_conditional_budget {Ω A H : Type*}
    [Fintype Ω] [Fintype A] [Fintype H] [Nonempty A]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → A) (z : Ω → H)
    (c C P unit : ℝ) (hc : c ≤ C) (hunit : 0 < unit) :
    c - (P - observationEntropy p X / unit) - observationEntropy p z / unit ≤
      C - (P - conditionalObservationEntropy p X z / unit) := by
  have hpair := observationEntropy_le_of_factorsThrough p hp
    (fun ω => (z ω, X ω)) X (fun _ _ he => congrArg Prod.snd he)
  have he := div_le_div_of_nonneg_right (sub_le_sub_right hpair (observationEntropy p z))
    hunit.le
  rw [sub_div] at he
  change _ ≤ conditionalObservationEntropy p X z / unit at he
  linarith

/-- The original common-budget statement is a corollary of the sharper
conditional-source bound. Charging H(Z) is valid without assuming Z is a function of X. -/
theorem helper_recovery_gap {Ω H : Type*} [Fintype Ω] [Fintype H] {m W : ℕ}
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
    (State₁ State₂ : H → Type*) [∀ a, Fintype (State₁ a)] [∀ a, Fintype (State₂ a)]
    (s : ℝ) (state₁ : ∀ a, HelperFiber z a → State₁ a)
    (state₂ : ∀ a, HelperFiber z a → State₂ a)
    (hcap₁ : ∀ a, (Fintype.card (State₁ a) : ℝ) ≤ (2 : ℝ)^s)
    (hcap₂ : ∀ a, (Fintype.card (State₂ a) : ℝ) ≤ (2 : ℝ)^s)
    (decode₁ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a) (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a) (rowRecode (S a) (shear L (X ω))), state₁ a ω)))
    (decode₂ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a)ᶜ (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a)ᶜ (rowRecode (S a) (shear L (X ω))), state₂ a ω))) :
    eta / (8 * ((D : ℝ) + 1)^2) * (2 * m * W) * Real.log 2 -
      ((2 * m * W : ℝ) * Real.log 2 - observationEntropy p X) -
        observationEntropy p z ≤ s * Real.log 2 := by
  have h := helper_recovery_gap_conditional p hp hp1 X L D hrow hcol eta heta0
    (by linarith) hexp z I J hI hJ R S State₁ State₂ (fun _ => s)
    state₁ state₂ hcap₁ hcap₂ decode₁ decode₂
  rw [← Finset.sum_mul, sum_helperMass, hp1, one_mul] at h
  have hc := mul_le_mul_of_nonneg_right (recovery_coefficient_le_sharp D eta heta0)
    (show 0 ≤ (2 * m * W : ℝ) * Real.log 2 by positivity)
  have hw := entropy_charge_le_conditional_budget p hp X z _ _
    ((2 * m * W : ℝ) * Real.log 2) 1 hc (by norm_num)
  simp only [div_one] at hw
  linarith

/-- The recovery obstruction in bits, with precisely the advertised coefficient. -/
theorem helper_recovery_gap_bits {Ω H : Type*} [Fintype Ω] [Fintype H] {m W : ℕ}
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
    (State₁ State₂ : H → Type*) [∀ a, Fintype (State₁ a)] [∀ a, Fintype (State₂ a)]
    (s : ℝ) (state₁ : ∀ a, HelperFiber z a → State₁ a)
    (state₂ : ∀ a, HelperFiber z a → State₂ a)
    (hcap₁ : ∀ a, (Fintype.card (State₁ a) : ℝ) ≤ (2 : ℝ)^s)
    (hcap₂ : ∀ a, (Fintype.card (State₂ a) : ℝ) ≤ (2 : ℝ)^s)
    (decode₁ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a) (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a) (rowRecode (S a) (shear L (X ω))), state₁ a ω)))
    (decode₂ : ∀ a,
      (fun ω : HelperFiber z a => rowView (I a)ᶜ (rowRecode (R a) (X ω))).FactorsThrough
      (fun ω => (rowView (J a)ᶜ (rowRecode (S a) (shear L (X ω))), state₂ a ω))) :
    eta / (8 * ((D : ℝ) + 1)^2) * (2 * m * W) -
      ((2 * m * W : ℝ) - observationEntropy p X / Real.log 2) -
        observationEntropy p z / Real.log 2 ≤ (s : ℝ) := by
  have h := helper_recovery_gap p hp hp1 X L D hrow hcol eta heta0 heta1 hexp
    z I J hI hJ R S State₁ State₂ s state₁ state₂ hcap₁ hcap₂ decode₁ decode₂
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd := (div_le_iff₀ hlog).mpr h
  convert hd using 1
  field_simp

end TransposeFollowup.ExpanderShear
