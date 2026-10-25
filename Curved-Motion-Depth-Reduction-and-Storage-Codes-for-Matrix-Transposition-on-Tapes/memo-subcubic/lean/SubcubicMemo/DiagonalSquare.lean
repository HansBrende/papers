import SubcubicMemo.TwoStepDefect
import LeanMachine.InvariantKernel

/-! Restriction to ker(W²-I) when W² is block diagonal. The restriction is
coordinatewise and preserves all support zeros. -/

namespace SubcubicMemo

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SparseProjection
open scoped BigOperators Classical

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
  {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]
  (T : ∀ v u, A u →ₗ[K] A v)

theorem square_apply (x : ∀ v, A v) (a : V) :
    blockOperator T (blockOperator T x) a = ∑ c, squareBlock T a c (x c) := by
  have he : x = ∑ c, LinearMap.single K A c (x c) :=
    (LinearMap.sum_single_apply A x).symm
  conv_lhs => rw [he]
  simp only [map_sum, Finset.sum_apply]
  apply sum_congr rfl
  intro c _
  exact (LinearMap.congr_fun (squareBlock_eq T a c) (x c)).symm

theorem square_diagonal (hzero : twoStepDefect T = 0) (x : ∀ v, A v) (a : V) :
    blockOperator T (blockOperator T x) a = squareBlock T a a (x a) := by
  rw [square_apply]
  apply sum_eq_single a
  · intro c _ hca
    have he : defectBlock T a c = 0 := by rw [defectBlock_eq, hzero]; simp
    rw [defectBlock, if_neg hca.symm] at he
    rw [he, LinearMap.zero_apply]
  · simp

def squareFixedSpace (v : V) : Submodule K (A v) :=
  LinearMap.ker (squareBlock T v v - LinearMap.id)

theorem mem_squareFixedSpace (v : V) (x : A v) :
    x ∈ squareFixedSpace T v ↔ squareBlock T v v x = x := by
  change squareBlock T v v x - x = 0 ↔ _
  exact sub_eq_zero

def squareEmbedding : (∀ v, squareFixedSpace T v) →ₗ[K] (∀ v, A v) :=
  LinearMap.piMap (fun v => (squareFixedSpace T v).subtype)

theorem squareEmbedding_injective : Function.Injective (squareEmbedding T) := by
  intro x y h
  funext v
  exact Subtype.ext (congrFun h v)

theorem squareEmbedding_fixed (hzero : twoStepDefect T = 0)
    (x : ∀ v, squareFixedSpace T v) :
    blockOperator T (blockOperator T (squareEmbedding T x)) = squareEmbedding T x := by
  funext v
  rw [square_diagonal T hzero]
  exact (mem_squareFixedSpace T v _).mp (x v).property

theorem block_preserves_squareFixed (hzero : twoStepDefect T = 0) (v u : V)
    (x : squareFixedSpace T u) : T v u x.val ∈ squareFixedSpace T v := by
  have hs : blockOperator T (blockOperator T (LinearMap.single K A u x.val)) =
      LinearMap.single K A u x.val := by
    funext a
    rw [square_diagonal T hzero]
    by_cases hau : a = u
    · subst a
      simp only [LinearMap.single_apply, Pi.single_eq_same]
      exact (mem_squareFixedSpace T u _).mp x.property
    · simp [LinearMap.single_apply, Pi.single_eq_of_ne hau]
  have hi : blockOperator T (blockOperator T (blockOperator T (LinearMap.single K A u x.val))) =
      blockOperator T (LinearMap.single K A u x.val) := by rw [hs]
  have hv := congrFun hi v
  rw [square_diagonal T hzero, blockOperator_single] at hv
  exact (mem_squareFixedSpace T v _).mpr hv

noncomputable def restrictedSquareBlocks (hzero : twoStepDefect T = 0) (v u : V) :
    squareFixedSpace T u →ₗ[K] squareFixedSpace T v :=
  ((T v u).domRestrict (squareFixedSpace T u)).codRestrict (squareFixedSpace T v)
    (block_preserves_squareFixed T hzero v u)

theorem restrictedSquareBlocks_zero (hzero : twoStepDefect T = 0) {v u : V}
    (h : T v u = 0) : restrictedSquareBlocks T hzero v u = 0 := by
  ext x : 1
  apply Subtype.ext
  change T v u x.val = 0
  rw [h, LinearMap.zero_apply]

theorem squareEmbedding_intertwines (hzero : twoStepDefect T = 0) :
    (blockOperator T).comp (squareEmbedding T) =
      (squareEmbedding T).comp (blockOperator (restrictedSquareBlocks T hzero)) := by
  apply LinearMap.ext
  intro x
  funext v
  simp only [LinearMap.comp_apply, blockOperator_apply]
  change (∑ u, T v u ((x u).val)) =
    ((blockOperator (restrictedSquareBlocks T hzero) x v) : A v)
  rw [blockOperator_apply]
  simp only [Submodule.coe_sum]
  rfl

theorem restrictedSquare_involution (hzero : twoStepDefect T = 0) :
    (blockOperator (restrictedSquareBlocks T hzero)).comp
      (blockOperator (restrictedSquareBlocks T hzero)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply squareEmbedding_injective T
  have hi (y) : blockOperator T (squareEmbedding T y) =
      squareEmbedding T (blockOperator (restrictedSquareBlocks T hzero) y) :=
    LinearMap.congr_fun (squareEmbedding_intertwines T hzero) y
  change squareEmbedding T (blockOperator (restrictedSquareBlocks T hzero)
    (blockOperator (restrictedSquareBlocks T hzero) x)) = squareEmbedding T x
  rw [← hi, ← hi, squareEmbedding_fixed T hzero]

theorem squareFixed_dimension (hzero : twoStepDefect T = 0) :
    finrank K (LinearMap.ker ((blockOperator T).comp (blockOperator T) - LinearMap.id)) =
      ∑ v, finrank K (squareFixedSpace T v) := by
  have he : (blockOperator T).comp (blockOperator T) - LinearMap.id =
      LinearMap.piMap (fun v => squareBlock T v v - LinearMap.id) := by
    apply LinearMap.ext
    intro x
    funext v
    change blockOperator T (blockOperator T x) v - x v = squareBlock T v v (x v) - x v
    rw [square_diagonal T hzero]
  have hn := LinearMap.finrank_range_add_finrank_ker
    ((blockOperator T).comp (blockOperator T) - LinearMap.id)
  have hs := sum_congr (s₁ := (univ : Finset V)) rfl (fun v _ =>
    LinearMap.finrank_range_add_finrank_ker (squareBlock T v v - LinearMap.id))
  rw [sum_add_distrib] at hs
  have hr : finrank K (LinearMap.range ((blockOperator T).comp (blockOperator T) - LinearMap.id)) =
      ∑ v, finrank K (LinearMap.range (squareBlock T v v - LinearMap.id)) := by
    rw [he, LeanMachine.MatrixRankCertificate.finrank_range_piMap]
  rw [hr, Module.finrank_pi_fintype] at hn
  change _ + (∑ v, finrank K (squareFixedSpace T v)) = _ at hs
  omega

end SubcubicMemo
