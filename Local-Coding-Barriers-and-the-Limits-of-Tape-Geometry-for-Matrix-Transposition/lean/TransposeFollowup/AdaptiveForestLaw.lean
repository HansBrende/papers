import TransposeFollowup.AdaptiveForestRangeBound
import TransposeFollowup.AdaptiveBankRate
import TransposeFollowup.HelperPacketDegreeBound

/-! A semantic bundle for families of actual helper-selected forest strategies.
Every field describes inputs, executions, locality or correctness; the numerical
budget is a proved consequence, never a field of the bundle. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

structure AdaptiveForestLaw (d b sigma Delta : ℕ) where
  Helper : Type
  Sample : Type
  helperFinite : Fintype Helper
  sampleFinite : Fintype Sample
  code : HelperGapBankStrategy d b sigma Helper
  weight : Sample → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  weight_sum : @Finset.sum Sample ℝ _ (Finset.univ (α := Sample)) weight = 1
  input : Sample → FiniteMatrix d b
  message : FiniteMatrix d b → List Bool
  terminates : code.TerminatesOn (Set.range input) message
  correct : code.CorrectOn (Set.range input) message
  forest : ∀ x, ((code.strategy (code.helper (input x))).bankInteractionGraph [] (message (input x))).IsAcyclic
  pairwise : ∀ x, (code.strategy (code.helper (input x))).Along (fun S => S.card ≤ 2) [] (message (input x))
  rowGraph : Helper → List Bool → SimpleGraph (Fin d)
  locality : ∀ x, ∀ v w : MatrixBit d b,
    ((code.strategy (code.helper (input x))).bankInteractionGraph [] (message (input x))).Adj v w →
      v.1 = w.1 ∨ (rowGraph (code.helper (input x)) (message (input x))).Adj v.1 w.1
  degree : ∀ x i, (rowGraph (code.helper (input x)) (message (input x))).degree i ≤ Delta
  stateBits : ℝ
  state_nonneg : 0 ≤ stateBits
  state_budget : ∀ a, (code.bank a).StateRangeBudget stateBits

attribute [instance] AdaptiveForestLaw.helperFinite AdaptiveForestLaw.sampleFinite

namespace AdaptiveForestLaw

variable {d b sigma Delta : ℕ} (F : AdaptiveForestLaw d b sigma Delta)

noncomputable def expectedLength : ℝ :=
  ∑ x, F.weight x * ((F.message (F.input x)).length : ℝ)

noncomputable def deficit : ℝ :=
  (d*d*b : ℕ) - observationEntropy F.weight F.input / Real.log 2 +
    observationEntropy F.weight (fun x => F.code.helper (F.input x)) / Real.log 2

theorem deficit_nonneg : 0 ≤ F.deficit :=
  helper_matrix_deficit_nonneg F.weight F.weight_nonneg F.weight_sum F.input
    (fun x => F.code.helper (F.input x))

/-- Exact numerical budget instantiated by the actual public strategy theorem. -/
theorem budget (R M : ℕ) (hR : 0 < R) (hM : 0 < M) (hd : 0 < d) :
    (d:ℝ) * (d*b:ℕ) -
      (d*b:ℕ) * ((max 2 Delta:ℕ):ℝ)^(2*R) * ((d ⌈/⌉ M : ℕ) + 2*(sigma:ℝ)) -
      (bucketPatternCount M ((max 2 Delta)^R) : ℝ) *
        ((((max 2 Delta:ℕ):ℝ)^R+1)*F.stateBits+F.deficit) ≤
      (1+1/(R:ℝ))*F.expectedLength := by
  have h := F.code.forest_expected_length_of_state_range F.weight F.weight_nonneg F.weight_sum F.input F.message
    F.terminates F.correct R M (max 2 Delta) hR hM hd (le_max_left _ _)
    F.forest F.pairwise F.rowGraph F.locality
    (fun x i => (F.degree x i).trans (le_max_right _ _)) F.state_nonneg F.state_budget
  dsimp only [expectedLength, deficit]
  convert h using 1; push_cast; ring

/-- Explicit finite logarithmic-logarithmic loss, including the original
floor choices, coefficient eight and remainder. -/
theorem explicit_rate (hd : 1 ≤ d) (hb : 0 < b)
    (ht : ((max 2 Delta : ℕ) : ℝ)^8 ≤ Real.logb 2 (d:ℝ))
    (As Ad : ℝ) (hAs : 0 ≤ As) (hAd : 0 ≤ Ad)
    (hs : F.stateBits ≤ As*(d*b:ℕ)) (hdef : F.deficit ≤ Ad*(d*b:ℕ)) :
    1-F.expectedLength/(d*d*b:ℕ) ≤
      8*Real.log ((max 2 Delta:ℕ):ℝ)/Real.log (Real.logb 2 (d:ℝ)) +
        adaptiveRateError d (max 2 Delta) sigma As Ad := by
  have h := adaptive_forest_explicit_rate d (max 2 Delta) sigma hd (le_max_left _ _) ht
    (d*b:ℕ) F.expectedLength F.stateBits F.deficit As Ad
    (by positivity) hAs hAd hs hdef
    (fun R M hR hM _ => F.budget R M hR hM (by omega))
  convert h using 1; push_cast; ring

end AdaptiveForestLaw
end TransposeFollowup
