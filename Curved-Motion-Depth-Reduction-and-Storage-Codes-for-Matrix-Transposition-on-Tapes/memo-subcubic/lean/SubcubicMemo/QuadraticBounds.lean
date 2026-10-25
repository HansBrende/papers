import SubcubicMemo.SquareGood
import SubcubicMemo.QuadraticExact

/-! Unconditional triangle-free subcubic specializations: the graph premise
of the reusable algebraic lemmas is discharged by the proved square theorem. -/

namespace SubcubicMemo

open Module Finset LeanMachine.SubspaceRecovery MotionDepthCodes
open scoped BigOperators Classical

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
  {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]
  (T : ∀ v u, A u →ₗ[K] A v) (G : SimpleGraph V) [DecidableRel G.Adj]
  (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
  (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3)

include hs htri hdeg in
theorem subcubic_constrained_half :
    2 * finrank K (constrainedCode T G) ≤
      ∑ v, finrank K (LinearMap.range ((LinearMap.proj v).domRestrict (constrainedCode T G))) :=
  constrained_half_of_squareCore_good T G hs (squareCore_good G htri hdeg)

include hs htri hdeg in
theorem subcubic_paid_rank :
    (∑ v, finrank K (A v)) ≤
      2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) +
        2 * constraintLoss T G :=
  paid_rank_of_squareCore_good T G hs (squareCore_good G htri hdeg)

include hs htri hdeg in
theorem subcubic_twoStep_stability :
    (∑ v, finrank K (A v)) ≤
      2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) +
        12 * finrank K (LinearMap.range (twoStepDefect T)) ∧
    (∑ v, finrank K (A v)) ≤
      2 * finrank K (LinearMap.range (LinearMap.id + blockOperator T)) +
        12 * finrank K (LinearMap.range (twoStepDefect T)) :=
  ⟨defect_rank_of_squareCore_good T G hs hdeg (squareCore_good G htri hdeg),
    plus_defect_rank_of_squareCore_good T G hs hdeg (squareCore_good G htri hdeg)⟩

include hs htri hdeg in
theorem subcubic_quadratic_exact (hzero : twoStepDefect T = 0) :
    2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) =
      (∑ v, finrank K (A v)) +
        finrank K (LinearMap.range ((blockOperator T).comp (blockOperator T) - LinearMap.id)) ∧
    2 * finrank K (LinearMap.range (LinearMap.id + blockOperator T)) =
      (∑ v, finrank K (A v)) +
        finrank K (LinearMap.range ((blockOperator T).comp (blockOperator T) - LinearMap.id)) :=
  ⟨quadratic_exact_minus T G hs hdeg (squareCore_good G htri hdeg) hzero,
    quadratic_exact_plus T G hs hdeg (squareCore_good G htri hdeg) hzero⟩

include hs htri hdeg in
theorem subcubic_quadratic_injective (hzero : twoStepDefect T = 0)
    (S : Submodule K (∀ v, A v))
    (hS : Function.Injective (((blockOperator T).comp (blockOperator T) - LinearMap.id).domRestrict S)) :
    (∑ v, finrank K (A v)) + finrank K S ≤
      2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) ∧
    (∑ v, finrank K (A v)) + finrank K S ≤
      2 * finrank K (LinearMap.range (LinearMap.id + blockOperator T)) :=
  quadratic_rank_injective_subspace T G hs hdeg (squareCore_good G htri hdeg) hzero S hS

include hs htri hdeg in
theorem subcubic_involution_ranks (hi : (blockOperator T).comp (blockOperator T) = LinearMap.id) :
    2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) = ∑ v, finrank K (A v) ∧
    2 * finrank K (LinearMap.range (LinearMap.id + blockOperator T)) = ∑ v, finrank K (A v) := by
  have hh := subcubic_quadratic_exact T G hs htri hdeg (involution_zero_defect T hi)
  rw [hi,sub_self,LinearMap.range_zero,finrank_bot,add_zero] at hh
  exact hh

end SubcubicMemo
