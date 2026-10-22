import TransposeFollowup.ConditionalObservation

/-! Exact finite helper-fiber averaging. Empty and zero-mass helper fibers
are retained, with zero normalized weights and zero contribution. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

variable {Ω H A : Type*} [Fintype Ω]

/-- The finite sample fiber belonging to a helper value. -/
abbrev HelperFiber (h : Ω → H) (a : H) := {x : Ω // h x = a}

/-- The mass of one helper value. -/
noncomputable def helperMass (p : Ω → ℝ) (h : Ω → H) (a : H) : ℝ :=
  pushforward p h a

/-- The conditional weights on a helper fiber. Division by zero is zero,
so no positive-mass or nonempty assumption is imposed on every helper value. -/
noncomputable def helperConditionalWeight (p : Ω → ℝ) (h : Ω → H) (a : H)
    (x : HelperFiber h a) : ℝ := p x / helperMass p h a

theorem sum_helperFiber (h : Ω → H) (a : H) (f : Ω → ℝ) :
    (∑ x : HelperFiber h a, f x) = ∑ x, if h x = a then f x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem sum_helperFiber_eq_mass (p : Ω → ℝ) (h : Ω → H) (a : H) :
    (∑ x : HelperFiber h a, p x) = helperMass p h a := by
  exact sum_helperFiber h a p

theorem sum_helperFibers [Fintype H] (h : Ω → H) (f : Ω → ℝ) :
    (∑ a, ∑ x : HelperFiber h a, f x) = ∑ x, f x := by
  simp_rw [sum_helperFiber]
  rw [Finset.sum_comm]
  simp

theorem helperMass_nonneg (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (h : Ω → H) (a : H) : 0 ≤ helperMass p h a :=
  pushforward_nonneg p hp h a

theorem sum_helperMass [Fintype H] (p : Ω → ℝ) (h : Ω → H) :
    ∑ a, helperMass p h a = ∑ x, p x := sum_pushforward p h

theorem helperConditionalWeight_nonneg (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (h : Ω → H) (a : H) (x : HelperFiber h a) :
    0 ≤ helperConditionalWeight p h a x :=
  div_nonneg (hp x) (helperMass_nonneg p hp h a)

theorem sum_helperConditionalWeight (p : Ω → ℝ) (h : Ω → H) (a : H)
    (ha : helperMass p h a ≠ 0) :
    ∑ x : HelperFiber h a, helperConditionalWeight p h a x = 1 := by
  simp only [helperConditionalWeight, ← Finset.sum_div, sum_helperFiber_eq_mass,
    div_self ha]

theorem helperConditionalWeight_of_mass_zero (p : Ω → ℝ) (h : Ω → H) (a : H)
    (ha : helperMass p h a = 0) (x : HelperFiber h a) :
    helperConditionalWeight p h a x = 0 := by
  simp [helperConditionalWeight, ha]

theorem helperFiber_weight_of_mass_zero (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (h : Ω → H) (a : H) (ha : helperMass p h a = 0) (x : HelperFiber h a) :
    p x = 0 := by
  have hle := le_pushforward p hp h x.val
  rw [x.property] at hle
  exact le_antisymm (ha ▸ hle) (hp x)

theorem helperMass_mul_conditionalWeight (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (h : Ω → H) (a : H) (x : HelperFiber h a) :
    helperMass p h a * helperConditionalWeight p h a x = p x := by
  by_cases ha : helperMass p h a = 0
  · simp [ha, helperFiber_weight_of_mass_zero p hp h a ha x]
  · exact mul_div_cancel₀ _ ha


/-- Positive helper mass supplies an inhabitant of the conditional sample type. -/
theorem helperFiber_nonempty_of_mass_pos (p : Ω → ℝ) (h : Ω → H) (a : H)
    (ha : 0 < helperMass p h a) : Nonempty (HelperFiber h a) := by
  by_contra hn
  have : IsEmpty (HelperFiber h a) := not_nonempty_iff.mp hn
  have hz : helperMass p h a = 0 := by
    rw [← sum_helperFiber_eq_mass]
    simp
  linarith

/-- The law of total expectation, including zero-mass helper fibers. -/
theorem sum_helperMass_mul_mean [Fintype H] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (h : Ω → H) (f : Ω → ℝ) :
    (∑ a, helperMass p h a *
      ∑ x : HelperFiber h a, helperConditionalWeight p h a x * f x) =
      ∑ x, p x * f x := by
  simp_rw [Finset.mul_sum, ← mul_assoc, helperMass_mul_conditionalWeight p hp]
  exact sum_helperFibers h (fun x => p x * f x)

/-- Entropy of a scaled finite weight function, with its exact mass correction. -/
theorem entropy_scale_weights {B : Type*} [Fintype B] (q : B → ℝ) (c : ℝ) :
    entropy (fun x => c * q x) =
      c * entropy q + Real.negMulLog c * ∑ x, q x := by
  simp only [entropy, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Normalizing nonnegative weights has the standard exact entropy correction,
including the zero-mass case. -/
theorem sum_weights_mul_entropy_normalize {B : Type*} [Fintype B]
    (q : B → ℝ) (hq : ∀ x, 0 ≤ q x) :
    (∑ x, q x) * entropy (fun x => q x / ∑ y, q y) =
      entropy q - Real.negMulLog (∑ x, q x) := by
  let s := ∑ x, q x
  by_cases hs : s = 0
  · have hz : ∀ x, q x = 0 := by
      intro x
      have hx : q x ≤ s := Finset.single_le_sum (fun y _ => hq y) (Finset.mem_univ x)
      exact le_antisymm (hs ▸ hx) (hq x)
    simp [hz, entropy]
  · have hsum : (∑ x, q x / s) = 1 := by rw [← Finset.sum_div, div_self hs]
    have heq : (fun x => s * (q x / s)) = q := by
      funext x
      exact mul_div_cancel₀ _ hs
    have he := entropy_scale_weights (fun x => q x / s) s
    rw [heq, hsum, mul_one] at he
    change s * entropy (fun x => q x / s) = entropy q - Real.negMulLog s
    linarith


/-- Joint observation mass at a fixed helper value, summed over the observation. -/
theorem sum_joint_observation_eq_helperMass [Fintype A] (p : Ω → ℝ) (h : Ω → H)
    (X : Ω → A) (a : H) :
    (∑ b, pushforward p (fun x => (h x, X x)) (a, b)) = helperMass p h a := by
  unfold pushforward helperMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hh : h x = a <;> simp [hh]

/-- The observation law in a normalized helper fiber. -/
theorem pushforward_helperConditionalWeight (p : Ω → ℝ) (h : Ω → H)
    (X : Ω → A) (a : H) (b : A) :
    pushforward (helperConditionalWeight p h a) (fun x : HelperFiber h a => X x) b =
      pushforward p (fun x => (h x, X x)) (a, b) / helperMass p h a := by
  unfold pushforward helperConditionalWeight
  have he (x : HelperFiber h a) :
      (if X x = b then p x / helperMass p h a else 0) =
        (if X x = b then p x else 0) / helperMass p h a := by
    split <;> simp
  simp_rw [he]
  rw [← Finset.sum_div, sum_helperFiber h a (fun x => if X x = b then p x else 0)]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hh : h x = a <;> simp [hh]

/-- A helper-weighted observation entropy has its exact unnormalized mass
correction. The statement holds on zero-mass and empty fibers as well. -/
theorem helperMass_mul_observationEntropy [Fintype A] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (h : Ω → H) (X : Ω → A) (a : H) :
    helperMass p h a *
      observationEntropy (helperConditionalWeight p h a) (fun x : HelperFiber h a => X x) =
      entropy (fun b => pushforward p (fun x => (h x, X x)) (a, b)) -
        Real.negMulLog (helperMass p h a) := by
  have hf : pushforward (helperConditionalWeight p h a)
      (fun x : HelperFiber h a => X x) =
        fun b => pushforward p (fun x => (h x, X x)) (a, b) / helperMass p h a := by
    funext b
    exact pushforward_helperConditionalWeight p h X a b
  rw [observationEntropy, hf]
  have he := sum_weights_mul_entropy_normalize
    (fun b => pushforward p (fun x => (h x, X x)) (a, b))
    (fun b => pushforward_nonneg p hp _ (a, b))
  rw [sum_joint_observation_eq_helperMass] at he
  exact he

/-- The law of total conditional observation entropy. No helper fiber is
assumed nonempty or of positive mass, and normalization of the original
nonnegative weights is unnecessary. -/
theorem sum_helperMass_mul_observationEntropy [Fintype H] [Fintype A] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (h : Ω → H) (X : Ω → A) :
    (∑ a, helperMass p h a *
      observationEntropy (helperConditionalWeight p h a) (fun x : HelperFiber h a => X x)) =
      conditionalObservationEntropy p X h := by
  simp_rw [helperMass_mul_observationEntropy p hp, Finset.sum_sub_distrib]
  simp only [conditionalObservationEntropy, observationEntropy, entropy,
    Fintype.sum_prod_type, helperMass]

/-- Input entropy is the helper entropy plus the averaged entropy inside its
normalized fibers, including zero-mass fibers. -/
theorem sum_helperMass_mul_entropy [Fintype H] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (h : Ω → H) :
    (∑ a, helperMass p h a * entropy (helperConditionalWeight p h a)) =
      entropy p - observationEntropy p h := by
  have he (a : H) : helperMass p h a * entropy (helperConditionalWeight p h a) =
      entropy (fun x : HelperFiber h a => p x) - Real.negMulLog (helperMass p h a) := by
    have hx := sum_weights_mul_entropy_normalize (fun x : HelperFiber h a => p x)
      (fun x => hp x)
    rw [sum_helperFiber_eq_mass] at hx
    exact hx
  simp_rw [he, Finset.sum_sub_distrib]
  rw [show (∑ a, entropy (fun x : HelperFiber h a => p x)) = entropy p by
    exact sum_helperFibers h (fun x => Real.negMulLog (p x))]
  rfl

/-- Exact deficit averaging for a normalized input law and a fixed entropy
budget. This is the branch-helper identity used in the coding bounds. -/
theorem sum_helperMass_mul_entropy_deficit [Fintype H] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (h : Ω → H) (C : ℝ) :
    (∑ a, helperMass p h a * (C - entropy (helperConditionalWeight p h a))) =
      C - entropy p + observationEntropy p h := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_helperMass, hp1, one_mul, sum_helperMass_mul_entropy p hp]
  ring

end TransposeFollowup
