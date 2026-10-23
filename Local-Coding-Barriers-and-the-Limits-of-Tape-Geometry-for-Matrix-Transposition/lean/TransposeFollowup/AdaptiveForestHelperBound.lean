import TransposeFollowup.AdaptiveBankHelper
import TransposeFollowup.AdaptiveForestBound

/-! Helper-selected adaptive nonlinear forest codes. The complete finite
bound applies to the actual selected executions and charges helper entropy. -/

namespace TransposeFollowup.HelperGapBankCode

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {d b sigma : ℕ} {H Ω : Type*} [Fintype H] [Fintype Ω]
    (C : HelperGapBankCode d b sigma H)

theorem forest_expected_length
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hc : C.CorrectOn (Set.range X))
    (R M D : ℕ) (hR : 0 < R) (hM : 0 < M) (hd : 0 < d) (hD : 2 ≤ D)
    (hforest : ∀ x, ((C.branch (C.helper (X x))).protocol.interactionGraph
      ((C.branch (C.helper (X x))).transcript (X x))).IsAcyclic)
    (hpair : ∀ x, (C.branch (C.helper (X x))).protocol.Along (fun S => S.card ≤ 2)
      ((C.branch (C.helper (X x))).transcript (X x)))
    (G : H → List Bool → SimpleGraph (Fin d))
    (hlocal : ∀ x, (C.branch (C.helper (X x))).LeafLocalTo
      ((C.branch (C.helper (X x))).transcript (X x))
      (G (C.helper (X x)) ((C.branch (C.helper (X x))).transcript (X x))))
    (hdegree : ∀ x i, (G (C.helper (X x))
      ((C.branch (C.helper (X x))).transcript (X x))).degree i ≤ D)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : ∀ a, (C.branch a).bank.StateBudget s) :
    (d*d*b : ℕ) -
      ((d*b*D^(2*R)*(d ⌈/⌉ M + 2*sigma) : ℕ) +
        ((D^R+1)*bucketPatternCount M (D^R) : ℕ)*s) -
      (bucketPatternCount M (D^R) : ℝ) *
        ((d*d*b : ℕ) - observationEntropy p X / Real.log 2 +
          observationEntropy p (fun x => C.helper (X x)) / Real.log 2) ≤
      (1 + 1 / (R : ℝ)) * ∑ x, p x * (C.length (X x) : ℝ) := by
  apply helper_length_bound_of_fiber_bounds p hp hp1 X (fun x => C.helper (X x))
    (fun _ _ he => congrArg C.helper he) (fun x => (C.length (X x) : ℝ))
    (1 + 1/(R:ℝ)) (d*d*b : ℕ)
    ((d*b*D^(2*R)*(d ⌈/⌉ M + 2*sigma) : ℕ) +
      ((D^R+1)*bucketPatternCount M (D^R) : ℕ)*s)
    (bucketPatternCount M (D^R)) (Real.log 2)
  intro a ha
  have hbranch := (C.branch a).forest_expected_length
    (helperConditionalWeight p (fun x => C.helper (X x)) a)
    (helperConditionalWeight_nonneg p hp _ a)
    (sum_helperConditionalWeight p _ a ha.ne')
    (fun x : HelperFiber (fun y => C.helper (X y)) a => X x)
    (C.correctOn_fiber X hc a) R M D hR hM hd hD
    (fun x => by simpa only [x.property] using hforest x)
    (fun x => by simpa only [x.property] using hpair x)
    (G a) (fun x => by
      have hx : C.helper (X x) = a := x.property
      intro v w hvw
      have hh := @hlocal x.val v w
      rw [hx] at hh
      exact hh hvw)
    (fun x i => by
      have hx : C.helper (X x) = a := x.property
      have hh := hdegree x.val i
      rw [hx] at hh
      exact hh) hs0 (hs a)
  convert hbranch using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp only [length, x.property]

end TransposeFollowup.HelperGapBankCode
