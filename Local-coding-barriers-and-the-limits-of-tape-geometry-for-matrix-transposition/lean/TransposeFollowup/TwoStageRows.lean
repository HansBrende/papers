import TransposeFollowup.RowSuffix
import TransposeFollowup.FixedSupportSandwich

/-! The precise two-stage architecture: local input map/permutation, a
triangular bijection, local bijections, a permutation, a causal second stage,
and local final maps/permutation. Only the first stage and middle local maps
are required to be invertible. Both public orders are arbitrary.
-/

namespace TransposeFollowup

set_option autoImplicit false
open Classical

structure TwoStageRows (n : ℕ) (Q : Type*) where
  inputPerm : Equiv.Perm (Fin n)
  inputMap : Fin n → Q → Q
  first : TriangularRows n Q
  middleMap : Fin n → Q ≃ Q
  middlePerm : Equiv.Perm (Fin n)
  second : CausalRows n Q
  outputPerm : Equiv.Perm (Fin n)
  outputMap : Fin n → Q → Q

namespace TwoStageRows

variable {n : ℕ} {Q : Type*} (T : TwoStageRows n Q)

def input (x : Fin n → Q) (i : Fin n) : Q := T.inputMap i (x (T.inputPerm i))

noncomputable def forward [Fintype Q] : (Fin n → Q) ≃ (Fin n → Q) :=
  T.first.equiv.trans (Equiv.piCongrRight T.middleMap)

@[simp] theorem forward_apply [Fintype Q] (x : Fin n → Q) (i : Fin n) :
    T.forward x i = T.middleMap i (T.first.apply x i) := rfl

def finalMap (y : Fin n → Q) (i : Fin n) : Q :=
  T.outputMap i (T.second.apply (fun j => y (T.middlePerm j)) (T.outputPerm i))

noncomputable def apply [Fintype Q] (x : Fin n → Q) : Fin n → Q :=
  T.finalMap (T.forward (T.input x))

theorem inverse_block_injective [Fintype Q] : BlockInjective T.forward.symm := by
  apply blockInjective_inverse
  exact blockInjective_rowwise T.first.apply T.first.block_injective T.middleMap

def intermediateSuffix (r : ℕ) : Finset (Fin n) :=
  rowSuffix (T.middlePerm.symm.trans T.second.order) r

def inputRows (r : ℕ) : Finset (Fin n) := (T.intermediateSuffix r).image T.inputPerm

def outputSuffix (r : ℕ) : Finset (Fin n) :=
  rowSuffix (T.outputPerm.trans T.second.order) r

theorem intermediateSuffix_card {r : ℕ} (hr : r ≤ n) :
    (T.intermediateSuffix r).card = r := rowSuffix_card _ hr

theorem inputRows_card {r : ℕ} (hr : r ≤ n) : (T.inputRows r).card = r := by
  rw [inputRows, Finset.card_image_of_injective _ T.inputPerm.injective]
  exact T.intermediateSuffix_card hr

theorem outputSuffix_card {r : ℕ} (hr : r ≤ n) :
    (T.outputSuffix r).card = r := rowSuffix_card _ hr

theorem input_support (r : ℕ) (x y : Fin n → Q)
    (h : ∀ i ∈ T.inputRows r, x i = y i) :
    ∀ i ∈ T.intermediateSuffix r, T.input x i = T.input y i := by
  intro i hi
  exact congrArg (T.inputMap i) (h _ (Finset.mem_image_of_mem T.inputPerm hi))

theorem output_support (r : ℕ) (x y : Fin n → Q)
    (h : ∀ i ∉ T.intermediateSuffix r, x i = y i) :
    ∀ i ∉ T.outputSuffix r, T.finalMap x i = T.finalMap y i := by
  intro i hi
  apply congrArg (T.outputMap i)
  apply T.second.suffix_support r
  · intro j hj
    apply h
    simpa only [intermediateSuffix, mem_rowSuffix, Equiv.trans_apply,
      T.middlePerm.symm_apply_apply] using hj
  · simpa only [outputSuffix, mem_rowSuffix, Equiv.trans_apply] using hi

/-- Exact branch count; no helper conditioning or independence assumption is
used. The correct family can be empty or arbitrarily correlated. -/
theorem correct_family_card {b : ℕ} (T : TwoStageRows n (Row n b))
    (F : Finset (FiniteMatrix n b)) (hc : ∀ x ∈ F, T.apply x = transposed x)
    (r : ℕ) (hr : r ≤ n) :
    F.card ≤ 2 ^ ((n - r) * n * b + r * r * b) := by
  have h := fixed_support_transpose_count T.forward.symm T.finalMap T.input
    (T.intermediateSuffix r) (T.inputRows r) (T.outputSuffix r)
    T.inverse_block_injective (T.input_support r) (T.output_support r) F hc
  rwa [T.intermediateSuffix_card hr, T.inputRows_card hr, T.outputSuffix_card hr] at h

end TwoStageRows
end TransposeFollowup
