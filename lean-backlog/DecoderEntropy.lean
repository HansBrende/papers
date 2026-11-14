import TransposeFollowup.ConditionalEntropyFibers
import TransposeFollowup.UniformEntropy

/-!
# Conditional response distributions for deterministic decoder selection

Use the actual conditional output law on positive helper fibres and a uniform
output law on zero-mass fibres. Every response row is a probability vector,
including helper values that never occur. Its expected log success is exactly
the negative conditional observation entropy. Nonnegative source weights are
enough: their total mass need not be one.
-/

namespace LeanBacklog.DecoderEntropy

open Finset TransposeFollowup
open scoped BigOperators
open Classical
set_option autoImplicit false

variable {A B C : Type*} [Fintype A] [Fintype C]

/-- A normalized response at every helper value, including zero-mass fibres. -/
noncomputable def conditionalResponse (p : A → ℝ) (f : A → C) (g : A → B)
    (b : B) (c : C) : ℝ :=
  if helperMass p g b = 0 then uniformWeight C c
  else pushforward p (fun a => (g a, f a)) (b, c) / helperMass p g b

theorem conditionalResponse_nonneg (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : A → B) (b : B) (c : C) :
    0 ≤ conditionalResponse p f g b c := by
  unfold conditionalResponse
  split
  · exact uniformWeight_nonneg C c
  · exact div_nonneg (pushforward_nonneg p hp _ _) (helperMass_nonneg p hp g b)

theorem conditionalResponse_sum [Nonempty C] (p : A → ℝ)
    (f : A → C) (g : A → B) (b : B) :
    ∑ c, conditionalResponse p f g b c = 1 := by
  by_cases hb : helperMass p g b = 0
  · simp only [conditionalResponse, hb, ite_true]
    exact sum_uniformWeight C
  · simp only [conditionalResponse, hb, ite_false]
    rw [← sum_div, sum_joint_observation_eq_helperMass, div_self hb]

theorem conditionalResponse_pos (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : A → B) (a : A) (ha : 0 < p a) :
    0 < conditionalResponse p f g (g a) (f a) := by
  have hm : 0 < helperMass p g (g a) := lt_of_lt_of_le ha (le_pushforward p hp g a)
  have hj : 0 < pushforward p (fun a => (g a, f a)) (g a, f a) :=
    lt_of_lt_of_le ha (le_pushforward p hp (fun a => (g a, f a)) a)
  simp only [conditionalResponse, hm.ne', ite_false]
  exact div_pos hj hm

variable [Fintype B]

/-- Reindexing a log-likelihood expectation by its observed value. -/
theorem sum_log_observation (p : A → ℝ) (f : A → B) :
    ∑ a, p a * Real.log (pushforward p f (f a)) = -observationEntropy p f := by
  rw [← sum_pushforward_mul p f (fun b => Real.log (pushforward p f b))]
  simp only [observationEntropy, entropy, Real.negMulLog, neg_mul,
    sum_neg_distrib, neg_neg]

/-- The true conditional response achieves conditional entropy exactly.
Zero source weights make no positivity demand on their response probabilities. -/
theorem conditionalResponse_log (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : A → B) :
    ∑ a, p a * Real.log (conditionalResponse p f g (g a) (f a)) =
      -conditionalObservationEntropy p f g := by
  have he (a : A) : p a * Real.log (conditionalResponse p f g (g a) (f a)) =
      p a * Real.log (pushforward p (fun a => (g a, f a)) (g a, f a)) -
        p a * Real.log (pushforward p g (g a)) := by
    by_cases hz : p a = 0
    · simp only [hz, zero_mul, sub_self]
    · have ha : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm hz)
      have hm : 0 < helperMass p g (g a) :=
        lt_of_lt_of_le ha (le_pushforward p hp g a)
      have hj : 0 < pushforward p (fun a => (g a, f a)) (g a, f a) :=
        lt_of_lt_of_le ha (le_pushforward p hp (fun a => (g a, f a)) a)
      simp only [conditionalResponse, hm.ne', ite_false]
      rw [Real.log_div hj.ne' hm.ne', mul_sub]
      rfl
  simp_rw [he]
  rw [sum_sub_distrib, sum_log_observation p (fun a => (g a, f a)),
    sum_log_observation p g]
  unfold conditionalObservationEntropy
  ring

section Family

variable {I : Type*} [Fintype I]
  {B' C' : I → Type*} [∀ i, Fintype (C' i)]

/-- Probability that independent response tables succeed on a given input. -/
noncomputable def responseSuccess (p : A → ℝ)
    (f : ∀ i, A → C' i) (g : ∀ i, A → B' i) (a : A) : ℝ :=
  ∏ i, conditionalResponse p (f i) (g i) (g i a) (f i a)

theorem responseSuccess_nonneg (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : ∀ i, A → C' i) (g : ∀ i, A → B' i) (a : A) :
    0 ≤ responseSuccess p f g a :=
  prod_nonneg fun i _ => conditionalResponse_nonneg p hp (f i) (g i) _ _

theorem responseSuccess_pos (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : ∀ i, A → C' i) (g : ∀ i, A → B' i) (a : A) (ha : 0 < p a) :
    0 < responseSuccess p f g a :=
  prod_pos fun i _ => conditionalResponse_pos p hp (f i) (g i) a ha

variable [∀ i, Fintype (B' i)]

/-- The exact log-success identity for arbitrary dependent finite alphabets. -/
theorem responseSuccess_log (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : ∀ i, A → C' i) (g : ∀ i, A → B' i) :
    ∑ a, p a * Real.log (responseSuccess p f g a) =
      -∑ i, conditionalObservationEntropy p (f i) (g i) := by
  have he (a : A) : p a * Real.log (responseSuccess p f g a) =
      ∑ i, p a * Real.log (conditionalResponse p (f i) (g i) (g i a) (f i a)) := by
    by_cases hz : p a = 0
    · simp only [hz, zero_mul, sum_const_zero]
    · have ha : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm hz)
      unfold responseSuccess
      rw [Real.log_prod (fun i _ => (conditionalResponse_pos p hp (f i) (g i) a ha).ne')]
      rw [mul_sum]
  simp_rw [he]
  rw [sum_comm]
  simp_rw [conditionalResponse_log p hp]
  rw [sum_neg_distrib]

end Family

end LeanBacklog.DecoderEntropy

#print axioms LeanBacklog.DecoderEntropy.conditionalResponse_sum
#print axioms LeanBacklog.DecoderEntropy.conditionalResponse_log
#print axioms LeanBacklog.DecoderEntropy.responseSuccess_log
