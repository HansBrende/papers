import TransposeFollowup.AdaptiveForestStrategyBound
import TransposeFollowup.GapBankStateRange

/-! The actual adaptive theorem with a budget on reachable gap states only.
Unused state labels are removed without changing any bank bit or execution. -/

namespace TransposeFollowup.HelperGapBankStrategy

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {d b sigma : ℕ} {H Ω : Type*} [Fintype H] [Fintype Ω]
    (C : HelperGapBankStrategy d b sigma H)

theorem forest_expected_length_of_state_range
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (message : FiniteMatrix d b → List Bool)
    (ht : C.TerminatesOn (Set.range X) message) (hc : C.CorrectOn (Set.range X) message)
    (R M D : ℕ) (hR : 0 < R) (hM : 0 < M) (hd : 0 < d) (hD : 2 ≤ D)
    (hforest : ∀ x, ((C.strategy (C.helper (X x))).bankInteractionGraph [] (message (X x))).IsAcyclic)
    (hpair : ∀ x, (C.strategy (C.helper (X x))).Along (fun S => S.card ≤ 2) [] (message (X x)))
    (G : H → List Bool → SimpleGraph (Fin d))
    (hlocal : ∀ x, ∀ v w : MatrixBit d b,
      ((C.strategy (C.helper (X x))).bankInteractionGraph [] (message (X x))).Adj v w →
        v.1 = w.1 ∨ (G (C.helper (X x)) (message (X x))).Adj v.1 w.1)
    (hdegree : ∀ x i, (G (C.helper (X x)) (message (X x))).degree i ≤ D)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : ∀ a, (C.bank a).StateRangeBudget s) :
    (d*d*b : ℕ) -
      ((d*b*D^(2*R)*(d ⌈/⌉ M + 2*sigma) : ℕ) +
        ((D^R+1)*bucketPatternCount M (D^R) : ℕ)*s) -
      (bucketPatternCount M (D^R) : ℝ) *
        ((d*d*b : ℕ) - observationEntropy p X / Real.log 2 +
          observationEntropy p (fun x => C.helper (X x)) / Real.log 2) ≤
      (1 + 1 / (R : ℝ)) * ∑ x, p x * ((message (X x)).length : ℝ) := by
  exact C.restrictStates.forest_expected_length p hp hp1 X message ht hc R M D
    hR hM hd hD hforest hpair G hlocal hdegree hs0 (C.restrictStates_budget s hs)

end TransposeFollowup.HelperGapBankStrategy
