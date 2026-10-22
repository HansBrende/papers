import TransposeFollowup.FiniteEntropy
import TransposeFollowup.LocalProtocol
import Mathlib.InformationTheory.Coding.Kraft

/-!
# Entropy of charged public transcripts

This uses Mathlib's prefix-free Kraft inequality, including the singleton
empty transcript case. Variable-length messages are charged by their actual
length; no fixed-length padding or uncharged stopping symbol is assumed.
-/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

theorem entropy_le_expected_length_log_two (S : Finset (List Bool))
    (hS : InformationTheory.IsPrefixFree (S : Set (List Bool)))
    (p : S → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1) :
    entropy p ≤ (∑ w : S, p w * (w.val.length : ℝ)) * Real.log 2 := by
  classical
  let q : S → ℝ := fun w => (1 / 2 : ℝ) ^ w.val.length
  have hq : ∀ w, 0 < q w := fun w => pow_pos (by norm_num) _
  have hq1 : ∑ w : S, q w ≤ 1 := by
    calc
      ∑ w : S, q w = ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length :=
        Finset.sum_coe_sort S (fun w => (1 / 2 : ℝ) ^ w.length)
      _ ≤ 1 := by simpa using hS.finsetSum_one_div_card_pow_length_le_one
  have h := entropy_le_crossEntropy p q hp (fun w => (hq w).le) hp1 hq1
    (fun w _ => hq w)
  have hlog : ∀ w, Real.log (q w) = -((w.val.length : ℝ) * Real.log 2) := by
    intro w
    simp [q, Real.log_pow]
  calc
    entropy p ≤ -(∑ w, p w * Real.log (q w)) := h
    _ = (∑ w : S, p w * (w.val.length : ℝ)) * Real.log 2 := by
      simp only [hlog, mul_neg, Finset.sum_neg_distrib, neg_neg, ← mul_assoc,
        ← Finset.sum_mul]

end TransposeFollowup
