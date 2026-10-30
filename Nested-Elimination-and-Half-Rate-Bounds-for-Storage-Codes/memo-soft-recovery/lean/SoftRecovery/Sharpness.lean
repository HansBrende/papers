import SoftRecovery.ClassS
import SoftRecovery.Innovation
import SoftRecovery.Capacity
import TransposeFollowup.SeparatorSharpness

namespace SoftRecovery

open Finset HalfRate MotionDepthCodes DirectedReciprocity TransposeFollowup
open scoped BigOperators
set_option autoImplicit false

/-- A real entropy witness: one uniformly distributed bit, one coordinate. -/
noncomputable def oneBitRank (S : Finset Unit) : ℝ :=
  codeEntropy (uniformWeight Bool) (fun x (_ : Unit) => x) S

theorem oneBitRank_isPolymatroid : IsPolymatroid oneBitRank :=
  codeEntropy_isPolymatroid _ _ (uniformWeight_nonneg Bool) (sum_uniformWeight Bool)

theorem oneBitRank_univ : oneBitRank univ = Real.log 2 := by
  have hinj : Function.Injective (fun x : Bool => view (univ : Finset Unit) (fun _ => x)) := by
    intro x y h
    have he := congrFun h ()
    simpa [view] using he
  rw [oneBitRank, codeEntropy,
    observationEntropy_injective _ (uniformWeight_nonneg Bool) _ hinj,
    entropy_uniformWeight]
  simp

theorem oneBitRank_singleton (v : Unit) : oneBitRank {v} = Real.log 2 := by
  cases v
  have he : ({()} : Finset Unit) = univ := by ext x; cases x; simp
  rw [he, oneBitRank_univ]

theorem empty_isClassS {V : Type*} [DecidableEq V] : IsClassS (fun _ : V => ∅) := by
  simp [IsClassS, TTFree]

theorem oneBit_decomposable : ∃ pcs, Decomp (fun _ : Unit => ∅) ∅ pcs := by
  simpa using classS_decomp (empty_isClassS (V := Unit)) univ

/-- The coefficient of the residual sum cannot be reduced, even for an empty
Class S relation and the entropy of a single fair bit. -/
theorem residual_coefficient_at_least_one (c : ℝ)
    (hbound : 2 * oneBitRank univ ≤ (∑ v : Unit, oneBitRank {v}) +
      c * ∑ v : Unit, increment oneBitRank ∅ v) : 1 ≤ c := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [oneBitRank_univ, Fintype.sum_unique,
    oneBitRank_singleton, increment, insert_empty_eq,
    oneBitRank_isPolymatroid.empty, sub_zero] at hbound
  nlinarith

theorem residual_bound_attained :
    2 * oneBitRank univ = (∑ v : Unit, oneBitRank {v}) +
      ∑ v : Unit, increment oneBitRank ∅ v := by
  simp only [oneBitRank_univ, Fintype.sum_unique,
    oneBitRank_singleton, increment, insert_empty_eq,
    oneBitRank_isPolymatroid.empty, sub_zero]
  ring

/-- Taking the private helper to be the fair bit itself gives exact recovery. -/
theorem private_helper_recovers : increment oneBitRank {()} () = 0 :=
  increment_of_mem _ (mem_singleton_self _)

theorem private_helper_coefficient_at_least_one (c : ℝ)
    (hbound : oneBitRank univ ≤ c * oneBitRank {()}) : 1 ≤ c := by
  rw [oneBitRank_univ, oneBitRank_singleton] at hbound
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Reuse the existing actual XOR protocol at every positive word width. It is
correct on the full cube and uses one b-bit shared helper, with no messages.
Its two off-diagonal recovery obligations force shared-helper coefficient 2. -/
theorem shared_helper_coefficient_at_least_two (b : ℕ) (hb : 0 < b) (c : ℝ)
    (hbound : (2 * b : ℝ) ≤ c *
      (observationEntropy (uniformWeight (SeparatorSharpness.fullFamily b))
        (fun x : SeparatorSharpness.fullFamily b => (SeparatorSharpness.xorCode b).helper x.val) /
        Real.log 2)) : 2 ≤ c := by
  apply SeparatorSharpness.helper_coefficient_at_least_two b hb c
  rw [SeparatorSharpness.xorCode_cost]
  push_cast
  linarith

theorem shared_helper_one_fails :
    ¬ (2 ≤ observationEntropy (uniformWeight (SeparatorSharpness.fullFamily 1))
      (fun x : SeparatorSharpness.fullFamily 1 => (SeparatorSharpness.xorCode 1).helper x.val) /
      Real.log 2) := by
  rw [SeparatorSharpness.xorCode_helper_bits]
  norm_num

/-- The two digon uses have contexts {B} and {A}. Retaining the first context
and its recovered bit would require {A,B} at the second use; nesting fails. -/
theorem xor_uses_not_nested :
    ¬ NestedUses (∅ : Finset (Fin 3)) [({1}, 0), ({0}, 1)] := by
  norm_num [NestedUses, Finset.subset_iff]

/-- The semantic rule also excludes the digon whenever its second coordinate
is not determined by the first, as for the independent-bit XOR witness. -/
theorem xor_uses_not_retained {h : Finset (Fin 3) → ℝ}
    (hp : 0 < increment h {0} 1) :
    ¬ RetainedUses h ∅ [({1}, 0), ({0}, 1)] := by
  intro hn
  have he := hn.2.1
  have he' : increment h {0} 1 = 0 := by
    have heq : (insert 0 {1} ∪ {0} : Finset (Fin 3)) = insert 1 {0} := by decide
    simpa only [conditionalRank, heq, increment] using he
  linarith

/-- Two fair bits with an explicitly copied first coordinate and a record of
the pair. Coordinates 0 and 1 carry the same value under different names. -/
def copiedContextValues (x : Bool × Bool) (a : Fin 4) : Bool × Bool :=
  if a = 0 ∨ a = 1 then (x.1, false) else if a = 2 then (false, x.2) else x

noncomputable def copiedContextRank : Finset (Fin 4) → ℝ :=
  codeEntropy (uniformWeight (Bool × Bool)) copiedContextValues

theorem copiedContextRank_isPolymatroid : IsPolymatroid copiedContextRank :=
  codeEntropy_isPolymatroid _ _ (uniformWeight_nonneg _) (sum_uniformWeight _)

/-- A strict relaxation: the second context recovers the first symbol from
its copy, but does not contain the first symbol's name. -/
theorem copied_contexts_retained :
    RetainedUses copiedContextRank ∅ [(∅, 0), ({1}, 2)] := by
  refine ⟨conditionalRank_of_subset _ (empty_subset _), ?_, trivial⟩
  apply entropy_conditionalRank_zero_of_recovery _ _ (uniformWeight_nonneg _)
  intro x y he a ha
  have hxy := he 1 (mem_singleton_self _)
  have ha0 : a = 0 := by simpa using ha
  subst a
  simpa [copiedContextValues] using hxy

theorem copied_contexts_not_nested :
    ¬ NestedUses (∅ : Finset (Fin 4)) [(∅, 0), ({1}, 2)] := by
  norm_num [NestedUses, Finset.subset_iff]

/-- Independent fair bits and their parity, as actual finite observations. -/
def parityValues (x : Bool × Bool) (i : Fin 3) : Bool :=
  if i = 0 then x.1 else if i = 1 then x.2 else xor x.1 x.2

noncomputable def parityRank : Finset (Fin 3) → ℝ :=
  codeEntropy (uniformWeight (Bool × Bool)) parityValues

theorem parityRank_isPolymatroid : IsPolymatroid parityRank :=
  codeEntropy_isPolymatroid _ _ (uniformWeight_nonneg _) (sum_uniformWeight _)

private theorem parityValue_entropy (i : Fin 3) :
    observationEntropy (uniformWeight (Bool × Bool)) (fun x => parityValues x i) =
      Real.log 2 := by
  have he : pushforward (uniformWeight (Bool × Bool)) (fun x => parityValues x i) =
      uniformWeight Bool := by
    funext b
    fin_cases i <;> cases b <;>
      norm_num [pushforward, uniformWeight, parityValues, Fintype.sum_prod_type]
  rw [observationEntropy, he, entropy_uniformWeight]
  simp

theorem parityRank_singleton (i : Fin 3) : parityRank {i} = Real.log 2 := by
  have he : parityRank {i} =
      observationEntropy (uniformWeight (Bool × Bool)) (fun x => parityValues x i) := by
    unfold parityRank codeEntropy
    apply observationEntropy_eq_of_same_fibers _ (uniformWeight_nonneg _)
    intro x y
    simp [view_eq_iff]
  rw [he, parityValue_entropy]

private theorem parityPair_injective (i j : Fin 3) (hij : i ≠ j) :
    Function.Injective (fun x : Bool × Bool => (parityValues x i, parityValues x j)) := by
  revert i j
  decide

theorem parityRank_of_pair_subset (S : Finset (Fin 3)) (i j : Fin 3)
    (hij : i ≠ j) (hS : {i, j} ⊆ S) : parityRank S = 2 * Real.log 2 := by
  have hinj : Function.Injective (fun x : Bool × Bool => view S (parityValues x)) := by
    intro x y he
    apply parityPair_injective i j hij
    have ha : ∀ a ∈ S, parityValues x a = parityValues y a := by
      simpa only [view_eq_iff] using he
    exact Prod.ext (ha i (hS (by simp))) (ha j (hS (by simp)))
  rw [parityRank, codeEntropy,
    observationEntropy_injective _ (uniformWeight_nonneg _) _ hinj, entropy_uniformWeight]
  norm_num only [Fintype.card_prod, Fintype.card_bool, Nat.cast_ofNat, Nat.reduceMul]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- The earlier context loses a fair bit, but initially loses no information
about the independent helper. The previous whole-context charge is strict. -/
theorem helperLoss_strictly_smaller :
    helperLoss parityRank 0 ∅ [(∅, 1), (∅, 1)] = 0 ∧
    chainLoss parityRank ∅ [(∅, 1), (∅, 1)] = Real.log 2 := by
  have hp := parityRank_of_pair_subset {0, 1} 0 1 (by decide) (by rfl)
  have hm : mi parityRank 0 {1} = 0 := by
    simp only [mi, parityRank_singleton, hp]
    ring
  simp [helperLoss, chainLoss, hm, mi_empty parityRank_isPolymatroid,
    conditionalRank, parityRank_singleton, parityRank_isPolymatroid.empty]

/-- Revealing parity activates the helper's information about the lost bit.
Helper-specific loss is therefore not monotone under common conditioning. -/
theorem helperLoss_increases_after_reveal :
    helperLoss (contr parityRank {2}) 0 ∅ [(∅, 1), (∅, 1)] = Real.log 2 := by
  have hp02 := parityRank_of_pair_subset {0, 2} 0 2 (by decide) (by rfl)
  have hp12 := parityRank_of_pair_subset {1, 2} 1 2 (by decide) (by rfl)
  have hp012 := parityRank_of_pair_subset {0, 1, 2} 0 1 (by decide) (by decide)
  have hm : mi (contr parityRank {2}) 0 {1} = Real.log 2 := by
    simp only [mi, contr, singleton_union, insert_union, hp02, hp12, hp012,
      parityRank_singleton]
    ring
  simp [helperLoss, hm, mi_empty (contr_isPolymatroid parityRank_isPolymatroid {2}),
    max_eq_right (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]

/-- Revealing a raw fair bit receives a full coordinate credit: the effective
charge is one bit instead of the old two-bit reveal charge. -/
theorem oneBit_reveal_credit :
    2 * mutualRank oneBitRank univ univ ∅ -
      revealCredit oneBitRank id (fun _ => Real.log 2) ∅ univ = Real.log 2 := by
  simp [mutualRank, conditionalRank, revealCredit, oneBitRank_singleton,
    oneBitRank_isPolymatroid.empty]
  ring

end SoftRecovery
