import SubcubicMemo.ConstrainedHalf

/-! Exact payment for restricting the full code kernel, followed by the
block-row support payment. The graph input is stated explicitly. -/

namespace SubcubicMemo

open Module Finset LeanMachine.SubspaceRecovery MotionDepthCodes
open scoped BigOperators Classical

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
  {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]
  (T : ∀ v u, A u →ₗ[K] A v) (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def constraintLoss : ℕ := finrank K (LinearMap.range
  ((separatedConstraint T G).domRestrict (LinearMap.ker (LinearMap.id - blockOperator T))))

theorem constraintLoss_identity : constraintLoss T G + finrank K (constrainedCode T G) =
    finrank K (LinearMap.ker (LinearMap.id - blockOperator T)) := by
  let C := LinearMap.ker (LinearMap.id - blockOperator T)
  let f := (separatedConstraint T G).domRestrict C
  have hker : LinearMap.ker f = (constrainedCode T G).comap C.subtype := by
    ext x
    change separatedConstraint T G x.val = 0 ↔
      x.val ∈ C ∧ separatedConstraint T G x.val = 0
    exact ⟨fun h => ⟨x.property, h⟩, fun h => h.2⟩
  have heq := (Submodule.comapSubtypeEquivOfLe
    (show constrainedCode T G ≤ C from inf_le_left)).finrank_eq
  rw [← hker] at heq
  have hn := LinearMap.finrank_range_add_finrank_ker f
  rw [heq] at hn
  exact hn

theorem constraintLoss_le : constraintLoss T G ≤
    finrank K (LinearMap.range (separatedConstraint T G)) := by
  exact Submodule.finrank_mono (LinearMap.range_domRestrict_le_range _ _)

theorem paid_rank_of_squareCore_good
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hgood : RateBound (nbhd (squareCore G)) (1 / 2)) :
    (∑ v, finrank K (A v)) ≤
      2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) +
        2 * constraintLoss T G := by
  have hh := (constrained_half_of_squareCore_good T G hs hgood).trans
    (sum_le_sum (fun v _ => Submodule.finrank_le _))
  have hc := constraintLoss_identity T G
  have hn := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - blockOperator T)
  rw [Module.finrank_pi_fintype] at hn
  omega

theorem defect_rank_of_squareCore_good
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hgood : RateBound (nbhd (squareCore G)) (1 / 2)) :
    (∑ v, finrank K (A v)) ≤
      2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) +
        12 * finrank K (LinearMap.range (twoStepDefect T)) := by
  have h := paid_rank_of_squareCore_good T G hs hgood
  have hq := (constraintLoss_le T G).trans (separatedConstraint_rank_le T G hs hdeg)
  omega

theorem zero_defect_half_of_squareCore_good
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hgood : RateBound (nbhd (squareCore G)) (1 / 2)) (hzero : twoStepDefect T = 0) :
    (∑ v, finrank K (A v)) ≤
      2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) := by
  have h := defect_rank_of_squareCore_good T G hs hdeg hgood
  rw [hzero, LinearMap.range_zero, finrank_bot, mul_zero, add_zero] at h
  exact h

end SubcubicMemo
