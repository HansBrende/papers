import SubcubicMemo.TwoStepStability

/-! The exact rank balance for involutions, over arbitrary characteristic,
from the paid kernel theorem. -/

namespace SubcubicMemo

open Module Finset LeanMachine.SubspaceRecovery MotionDepthCodes
open scoped BigOperators Classical

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
  {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]
  (T : ∀ v u, A u →ₗ[K] A v)

theorem blockOperator_neg : blockOperator (fun v u => -T v u) = -blockOperator T := by
  apply LinearMap.ext
  intro x
  funext v
  simp only [blockOperator_apply, LinearMap.neg_apply, sum_neg_distrib, Pi.neg_apply]

theorem squareBlock_neg (a c : V) : squareBlock (fun v u => -T v u) a c = squareBlock T a c := by
  ext x
  simp [squareBlock, LinearMap.sum_apply, LinearMap.comp_apply]

theorem twoStepDefect_neg : twoStepDefect (fun v u => -T v u) = twoStepDefect T := by
  have h : defectBlock (fun v u => -T v u) = defectBlock T := by
    funext a c
    simp only [defectBlock, squareBlock_neg]
  unfold twoStepDefect
  rw [h]

theorem involution_zero_defect (hinv : (blockOperator T).comp (blockOperator T) = LinearMap.id) :
    twoStepDefect T = 0 := by
  have hb (a c : V) : defectBlock T a c = 0 := by
    by_cases hac : a = c
    · simp [defectBlock, hac]
    rw [defectBlock, if_neg hac, squareBlock_eq]
    ext x
    change blockOperator T (blockOperator T (LinearMap.single K A c x)) a = 0
    have h := congrFun (LinearMap.congr_fun hinv (LinearMap.single K A c x)) a
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.single_apply,
      Pi.single_eq_of_ne hac] using h
  apply LinearMap.ext
  intro x
  funext a
  simp only [twoStepDefect, blockOperator_apply, hb, LinearMap.zero_apply, sum_const_zero,
    Pi.zero_apply]

variable (G : SimpleGraph V) [DecidableRel G.Adj]
  (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
  (hdeg : ∀ v, G.degree v ≤ 3)
  (hgood : RateBound (nbhd (squareCore G)) (1 / 2))

include hs hdeg hgood in
theorem plus_defect_rank_of_squareCore_good : (∑ v, finrank K (A v)) ≤
    2 * finrank K (LinearMap.range (LinearMap.id + blockOperator T)) +
      12 * finrank K (LinearMap.range (twoStepDefect T)) := by
  have h := defect_rank_of_squareCore_good (fun v u => -T v u) G
    (fun v u h => by rw [hs v u h, neg_zero]) hdeg hgood
  rw [blockOperator_neg, sub_neg_eq_add, twoStepDefect_neg] at h
  exact h

include hs hdeg hgood in
theorem involution_exact_ranks
    (hinv : (blockOperator T).comp (blockOperator T) = LinearMap.id) :
    2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) =
      ∑ v, finrank K (A v) ∧
    2 * finrank K (LinearMap.range (LinearMap.id + blockOperator T)) =
      ∑ v, finrank K (A v) := by
  have he := involution_zero_defect T hinv
  have hm := zero_defect_half_of_squareCore_good T G hs hdeg hgood he
  have hp := plus_defect_rank_of_squareCore_good T G hs hdeg hgood
  rw [he, LinearMap.range_zero, finrank_bot, mul_zero, add_zero] at hp
  have hle : LinearMap.range (LinearMap.id + blockOperator T) ≤
      LinearMap.ker (LinearMap.id - blockOperator T) := by
    rintro _ ⟨x, rfl⟩
    change x + blockOperator T x - blockOperator T (x + blockOperator T x) = 0
    have hx : blockOperator T (blockOperator T x) = x := LinearMap.congr_fun hinv x
    rw [map_add, hx, add_comm (blockOperator T x) x, sub_self]
  have hd := Submodule.finrank_mono hle
  have hn := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - blockOperator T)
  rw [Module.finrank_pi_fintype] at hn
  omega

include hs hdeg hgood in
theorem involution_exact_kernels
    (hinv : (blockOperator T).comp (blockOperator T) = LinearMap.id) :
    2 * finrank K (LinearMap.ker (LinearMap.id - blockOperator T)) =
      ∑ v, finrank K (A v) ∧
    2 * finrank K (LinearMap.ker (LinearMap.id + blockOperator T)) =
      ∑ v, finrank K (A v) := by
  obtain ⟨hm, hp⟩ := involution_exact_ranks T G hs hdeg hgood hinv
  have hm' := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - blockOperator T)
  have hp' := LinearMap.finrank_range_add_finrank_ker (LinearMap.id + blockOperator T)
  rw [Module.finrank_pi_fintype] at hm' hp'
  omega

end SubcubicMemo
