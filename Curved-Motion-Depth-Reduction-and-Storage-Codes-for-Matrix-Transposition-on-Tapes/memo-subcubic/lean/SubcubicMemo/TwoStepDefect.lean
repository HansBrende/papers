import SubcubicMemo.SquareSupport
import LeanMachine.BlockRankSparsity
import LeanMachine.LinearCodeRecovery

/-! The actual two-step error operator and its source-separated constraints.
The separated map is not the summed error operator. -/

namespace SubcubicMemo

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SparseProjection
open scoped BigOperators Classical

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
  {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]
  (T : ∀ v u, A u →ₗ[K] A v)

def squareBlock (a c : V) : A c →ₗ[K] A a := ∑ b, (T a b).comp (T b c)

def defectBlock (a c : V) : A c →ₗ[K] A a := if a = c then 0 else squareBlock T a c

def twoStepDefect : (∀ v, A v) →ₗ[K] (∀ v, A v) := blockOperator (defectBlock T)

theorem squareBlock_eq (a c : V) : squareBlock T a c =
    (LinearMap.proj a).comp ((blockOperator T).comp
      ((blockOperator T).comp (LinearMap.single K A c))) := by
  ext x
  simp only [squareBlock, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, blockOperator_apply]
  apply sum_congr rfl
  intro b _
  congr 1
  simpa only [blockOperator_apply] using (blockOperator_single T c b x).symm

theorem defectBlock_eq (a c : V) : defectBlock T a c =
    (LinearMap.proj a).comp ((twoStepDefect T).comp (LinearMap.single K A c)) := by
  ext x
  exact (blockOperator_single (defectBlock T) c a x).symm

variable (G : SimpleGraph V) [DecidableRel G.Adj]
  (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)

include hs in
theorem defectBlock_eq_zero {a c : V} (hc : c ∉ twoStep G a) :
    defectBlock T a c = 0 := by
  by_cases hac : a = c
  · simp [defectBlock, hac]
  rw [defectBlock, if_neg hac, squareBlock]
  apply sum_eq_zero
  intro b _
  by_cases hab : G.Adj a b
  · have hbc : ¬ G.Adj b c := by
      intro hbc
      exact hc ((mem_twoStep G).mpr ⟨Ne.symm hac, b, hab, hbc⟩)
    simp [hs b c hbc]
  · simp [hs a b hab]

include hs in
theorem defectBlock_unique {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : a ≠ c) (hf : (offSquare G).Adj a b ∨ (offSquare G).Adj b c) :
    defectBlock T a c = (T a b).comp (T b c) := by
  rw [defectBlock, if_neg hac, squareBlock]
  apply sum_eq_single b
  · intro z _ hzb
    by_cases haz : G.Adj a z
    · have hzc : ¬ G.Adj z c := by
        intro hzc
        exact hzb (offSquare_unique_middle G hab hbc hac hf haz hzc)
      simp [hs z c hzc]
    · simp [hs a z haz]
  · simp

noncomputable def constraintMask (c : V) : (∀ v, A v) →ₗ[K] (∀ v, A v) :=
  LinearMap.pi fun a => if touchedPair G a c then LinearMap.proj a else 0

noncomputable def sourceConstraint (c : V) : A c →ₗ[K] (∀ v, A v) :=
  (constraintMask (A := A) G c).comp ((twoStepDefect T).comp (LinearMap.single K A c))

noncomputable def separatedConstraint : (∀ v, A v) →ₗ[K] (∀ _c : V, ∀ a, A a) :=
  LinearMap.piMap (sourceConstraint T G)

theorem separatedConstraint_apply (x : ∀ v, A v) (c a : V) :
    separatedConstraint T G x c a =
      if touchedPair G a c then defectBlock T a c (x c) else 0 := by
  change (if touchedPair G a c then LinearMap.proj a else (0 : (∀ v, A v) →ₗ[K] A a))
    (twoStepDefect T (LinearMap.single K A c (x c))) = _
  by_cases h : touchedPair G a c
  · simp only [h, ite_true, LinearMap.proj_apply, twoStepDefect, blockOperator_single]
  · simp [h]

theorem sourceConstraint_rank_le (c : V) :
    finrank K (LinearMap.range (sourceConstraint T G c)) ≤
      finrank K (LinearMap.range ((twoStepDefect T).comp (LinearMap.single K A c))) := by
  rw [sourceConstraint, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

theorem separatedConstraint_rank :
    finrank K (LinearMap.range (separatedConstraint T G)) =
      ∑ c, finrank K (LinearMap.range (sourceConstraint T G c)) :=
  LeanMachine.MatrixRankCertificate.finrank_range_piMap _

include hs in
theorem separatedConstraint_rank_le (hdeg : ∀ v, G.degree v ≤ 3) :
    finrank K (LinearMap.range (separatedConstraint T G)) ≤
      6 * finrank K (LinearMap.range (twoStepDefect T)) := by
  rw [separatedConstraint_rank T G]
  apply (sum_le_sum (fun c _ => sourceConstraint_rank_le T G c)).trans
  apply sum_column_ranks_le (twoStepDefect T) (twoStep G) 6
    (twoStep_card_le_six G hdeg)
  intro a c hc
  rw [← defectBlock_eq]
  exact defectBlock_eq_zero T G hs hc

end SubcubicMemo
