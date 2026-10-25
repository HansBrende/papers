import SubcubicMemo.QuadraticInvolution
import SubcubicMemo.DiagonalSquare

/-! Exact quadratic ranks. Restricting to ker(W²-I) replaces the longer
Fitting-filtration argument and gives an equality stronger than its bound. -/

namespace SubcubicMemo

open Module Finset LeanMachine.SubspaceRecovery MotionDepthCodes
open scoped BigOperators Classical

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
  {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]
  (T : ∀ v u, A u →ₗ[K] A v)

theorem squareEmbedding_covers_kernel (hzero : twoStepDefect T = 0) :
    LinearMap.ker (LinearMap.id - blockOperator T) ≤ LinearMap.range (squareEmbedding T) := by
  intro x hx
  have hfix : blockOperator T x = x := by
    have h : x - blockOperator T x = 0 := hx
    exact (sub_eq_zero.mp h).symm
  have hmem (v : V) : x v ∈ squareFixedSpace T v := by
    apply (mem_squareFixedSpace T v _).mpr
    rw [← square_diagonal T hzero, hfix, hfix]
  exact ⟨fun v => ⟨x v, hmem v⟩, rfl⟩

theorem square_restricted_kernel_dimension (hzero : twoStepDefect T = 0) :
    finrank K (LinearMap.ker (LinearMap.id - blockOperator T)) =
      finrank K (LinearMap.ker (LinearMap.id - blockOperator (restrictedSquareBlocks T hzero))) := by
  apply LeanMachine.InvariantKernel.finrank_ker_eq (squareEmbedding T)
    (squareEmbedding_injective T) _ _ _ (squareEmbedding_covers_kernel T hzero)
  apply LinearMap.ext
  intro x
  change squareEmbedding T x - blockOperator T (squareEmbedding T x) =
    squareEmbedding T (x - blockOperator (restrictedSquareBlocks T hzero) x)
  rw [map_sub]
  congr 1
  exact LinearMap.congr_fun (squareEmbedding_intertwines T hzero) x

variable (G : SimpleGraph V) [DecidableRel G.Adj]
  (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
  (hdeg : ∀ v, G.degree v ≤ 3)
  (hgood : RateBound (nbhd (squareCore G)) (1 / 2))

include hs hdeg hgood in
theorem quadratic_exact_minus (hzero : twoStepDefect T = 0) :
    2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) =
      (∑ v, finrank K (A v)) +
        finrank K (LinearMap.range ((blockOperator T).comp (blockOperator T) - LinearMap.id)) := by
  have hs' : ∀ v u, ¬ G.Adj v u → restrictedSquareBlocks T hzero v u = 0 :=
    fun v u h => restrictedSquareBlocks_zero T hzero (hs v u h)
  have hi := (involution_exact_kernels (restrictedSquareBlocks T hzero) G hs' hdeg hgood
    (restrictedSquare_involution T hzero)).1
  have hk := square_restricted_kernel_dimension T hzero
  have hd := squareFixed_dimension T hzero
  have hn := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - blockOperator T)
  have hq := LinearMap.finrank_range_add_finrank_ker
    ((blockOperator T).comp (blockOperator T) - LinearMap.id)
  rw [Module.finrank_pi_fintype] at hn hq
  omega

include hs hdeg hgood in
theorem quadratic_exact_plus (hzero : twoStepDefect T = 0) :
    2 * finrank K (LinearMap.range (LinearMap.id + blockOperator T)) =
      (∑ v, finrank K (A v)) +
        finrank K (LinearMap.range ((blockOperator T).comp (blockOperator T) - LinearMap.id)) := by
  have he : twoStepDefect (fun v u => -T v u) = 0 := by rw [twoStepDefect_neg, hzero]
  have h := quadratic_exact_minus (fun v u => -T v u) G
    (fun v u h => by rw [hs v u h, neg_zero]) hdeg hgood he
  have hsq : (-blockOperator T).comp (-blockOperator T) =
      (blockOperator T).comp (blockOperator T) := by
    apply LinearMap.ext
    intro x
    simp
  rw [blockOperator_neg, sub_neg_eq_add, hsq] at h
  exact h

include hs hdeg hgood in
/-- This includes the earlier invertible-Fitting-summand refinement: only
injectivity on the chosen subspace is needed. -/
theorem quadratic_rank_injective_subspace (hzero : twoStepDefect T = 0)
    (S : Submodule K (∀ v, A v))
    (hS : Function.Injective (((blockOperator T).comp (blockOperator T) - LinearMap.id).domRestrict S)) :
    (∑ v, finrank K (A v)) + finrank K S ≤
      2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) ∧
    (∑ v, finrank K (A v)) + finrank K S ≤
      2 * finrank K (LinearMap.range (LinearMap.id + blockOperator T)) := by
  have hl := Submodule.finrank_mono (LinearMap.range_domRestrict_le_range
    ((blockOperator T).comp (blockOperator T) - LinearMap.id) S)
  rw [LinearMap.finrank_range_of_inj hS] at hl
  rw [quadratic_exact_minus T G hs hdeg hgood hzero,
    quadratic_exact_plus T G hs hdeg hgood hzero]
  omega

end SubcubicMemo
