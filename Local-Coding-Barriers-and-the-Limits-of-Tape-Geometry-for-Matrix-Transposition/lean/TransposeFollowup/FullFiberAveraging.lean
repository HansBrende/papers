import TransposeFollowup.FullFiberEntropy
import TransposeFollowup.RefinedPrefix

/-! Averaging actual full-fiber deficits and charging a prefix-free transcript.
The leaf estimate is an internal interface discharged by geometric recovery. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

theorem observationEntropy_le_expected_code_length
    {Ω A : Type*} [Fintype Ω] [Fintype A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : Ω → A) (code : A → List Bool) (hinj : Function.Injective code)
    (hprefix : InformationTheory.IsPrefixFree (Set.range code)) :
    observationEntropy p f ≤ (∑ x, p x * (code (f x)).length) * Real.log 2 := by
  let q : A → ℝ := fun a => (1 / 2 : ℝ) ^ (code a).length
  have hq : ∀ a, 0 < q a := fun a => pow_pos (by norm_num) _
  have hq1 : ∑ a, q a ≤ 1 := kraft_indexed code hinj hprefix
  have hlog : ∀ a, Real.log (q a) = -((code a).length * Real.log 2) := by
    intro a
    simp [q, Real.log_pow]
  have he := entropy_le_crossEntropy (pushforward p f) q (pushforward_nonneg p hp f)
    (fun a => (hq a).le) ((sum_pushforward p f).trans hp1) hq1 (fun a _ => hq a)
  calc
    observationEntropy p f ≤ -(∑ a, pushforward p f a * Real.log (q a)) := he
    _ = (∑ a, pushforward p f a * (code a).length) * Real.log 2 := by
      simp only [hlog, mul_neg, Finset.sum_neg_distrib, neg_neg, ← mul_assoc, ← Finset.sum_mul]
    _ = _ := by rw [sum_pushforward_mul]

/-- An arbitrary law's conditional deficit is measured relative to each full
reference fiber. The overhead may depend on the leaf and is charged in expectation;
the transcript cost is charged once, through its code. -/
theorem fullFiber_expected_cost_of_leaf_cost
    {Ω V A : Type*} [Fintype Ω] [Fintype V] [Nonempty V] [Fintype A] [Nonempty A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → V) (f : V → A) (code : A → List Bool) (hinj : Function.Injective code)
    (hprefix : InformationTheory.IsPrefixFree (Set.range code))
    (overhead : A → ℝ) (Q : ℝ) (hQ : 1 ≤ Q)
    (hleaf : ∀ a, 0 < helperMass p (f ∘ X) a →
      observationEntropy (helperConditionalWeight p (f ∘ X) a)
        (fun x : HelperFiber (f ∘ X) a => X x) ≤
      overhead a * Real.log 2 + (Q - 1) *
        (Real.log (fiberCard f a : ℝ) -
          observationEntropy (helperConditionalWeight p (f ∘ X) a)
            (fun x : HelperFiber (f ∘ X) a => X x))) :
    (∑ x, p x * (code (f (X x))).length) ≥
      Real.log (Fintype.card V : ℝ) / Real.log 2 - (∑ x, p x * overhead (f (X x))) -
        Q * ((Real.log (Fintype.card V : ℝ) - observationEntropy p X) / Real.log 2) := by
  let H := f ∘ X
  let E := fun a => observationEntropy (helperConditionalWeight p H a)
    (fun x : HelperFiber H a => X x)
  let D := fun a => Real.log (fiberCard f a : ℝ) - E a
  have hav : (∑ a, helperMass p H a * E a) ≤
      ∑ a, helperMass p H a * (overhead a * Real.log 2 + (Q - 1) * D a) := by
    apply Finset.sum_le_sum
    intro a _
    by_cases hz : helperMass p H a = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left
        (hleaf a (lt_of_le_of_ne (helperMass_nonneg p hp H a) (Ne.symm hz)))
        (helperMass_nonneg p hp H a)
  have hE : (∑ a, helperMass p H a * E a) = conditionalObservationEntropy p X H :=
    sum_helperMass_mul_observationEntropy p hp H X
  have hD : (∑ a, helperMass p H a * D a) =
      (∑ x, p x * Real.log (fiberCard f (H x) : ℝ)) - conditionalObservationEntropy p X H := by
    simp only [D, mul_sub, Finset.sum_sub_distrib, hE]
    congr 1
    exact sum_pushforward_mul p H (fun a => Real.log (fiberCard f a : ℝ))
  have hright : (∑ a, helperMass p H a * (overhead a * Real.log 2 + (Q - 1) * D a)) =
      (∑ x, p x * overhead (H x)) * Real.log 2 +
        (Q - 1) * (∑ a, helperMass p H a * D a) := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · simp only [← mul_assoc, ← Finset.sum_mul]
      exact congrArg (fun t => t * Real.log 2) (sum_pushforward_mul p H overhead)
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
  rw [hE, hright, hD] at hav
  have hdef := fullFiberReference_deficit p hp hp1 X f
  have hmul := mul_le_mul_of_nonneg_left hdef (by linarith : 0 ≤ Q - 1)
  have hcond : conditionalObservationEntropy p X H ≤
      (∑ x, p x * overhead (H x)) * Real.log 2 +
      (Q - 1) * (Real.log (Fintype.card V : ℝ) - observationEntropy p X) :=
    hav.trans (add_le_add_right hmul _)
  have hcode := observationEntropy_le_expected_code_length p hp hp1 H code hinj hprefix
  have hpair : observationEntropy p (fun x => (H x, X x)) = observationEntropy p X := by
    exact observationEntropy_pair_of_factorsThrough p hp X H (by
      intro x y hxy
      exact congrArg f hxy)
  have hchain : observationEntropy p X = observationEntropy p H + conditionalObservationEntropy p X H := by
    rw [conditionalObservationEntropy, hpair]
    ring
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfinal : Real.log (Fintype.card V : ℝ) -
      (∑ x, p x * overhead (H x)) * Real.log 2 -
      Q * (Real.log (Fintype.card V : ℝ) - observationEntropy p X) ≤
        (∑ x, p x * (code (f (X x))).length) * Real.log 2 := by
    change observationEntropy p H ≤ (∑ x, p x * (code (f (X x))).length) * Real.log 2 at hcode
    linarith
  have hh := (div_le_iff₀ hlog).mpr hfinal
  dsimp only [H, Function.comp_def] at hh
  convert hh using 1
  field_simp

/-- An arbitrary law's conditional deficit is measured relative to each full
reference fiber. The transcript cost is charged once, through its code. -/
theorem fullFiber_expected_cost
    {Ω V A : Type*} [Fintype Ω] [Fintype V] [Nonempty V] [Fintype A] [Nonempty A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → V) (f : V → A) (code : A → List Bool) (hinj : Function.Injective code)
    (hprefix : InformationTheory.IsPrefixFree (Set.range code))
    (overhead Q : ℝ) (hQ : 1 ≤ Q)
    (hleaf : ∀ a, 0 < helperMass p (f ∘ X) a →
      observationEntropy (helperConditionalWeight p (f ∘ X) a)
        (fun x : HelperFiber (f ∘ X) a => X x) ≤
      overhead * Real.log 2 + (Q - 1) *
        (Real.log (fiberCard f a : ℝ) -
          observationEntropy (helperConditionalWeight p (f ∘ X) a)
            (fun x : HelperFiber (f ∘ X) a => X x))) :
    (∑ x, p x * (code (f (X x))).length) ≥
      Real.log (Fintype.card V : ℝ) / Real.log 2 - overhead -
        Q * ((Real.log (Fintype.card V : ℝ) - observationEntropy p X) / Real.log 2) := by
  simpa only [← Finset.sum_mul, hp1, one_mul] using
    fullFiber_expected_cost_of_leaf_cost p hp hp1 X f code hinj hprefix
      (fun _ => overhead) Q hQ hleaf

end TransposeFollowup
