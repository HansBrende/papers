import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Paid degree reduction in a finite directed incidence relation

Input and receiver ports are counted separately. A bound on every receiver's
degree bounds the total incidence count, and therefore the number of heavily
reused inputs. Deleting both ports of those coordinates bounds both degrees.
-/

namespace LeanMachine.IncidenceTrimming

open scoped BigOperators

variable {V : Type*} [Fintype V]
variable (E : V → V → Prop) [DecidableRel E]

/-- The number of receivers using input `p`. -/
def leftDegree (p : V) : ℕ := (Finset.univ.filter (E p)).card

/-- The size of the recovery set for receiver `q`. -/
def rightDegree (q : V) : ℕ := (Finset.univ.filter (fun p => E p q)).card

/-- Coordinates whose input port is used more than `M` times. -/
def heavy (M : ℕ) : Finset V := Finset.univ.filter (fun p => M < leftDegree E p)

/-- Both ports of every heavy coordinate are deleted. -/
def retained [DecidableEq V] (M : ℕ) : Finset V := Finset.univ \ heavy E M

/-- The left degree after restricting the receiver coordinates to `Q`. -/
def leftDegreeOn (Q : Finset V) (p : V) : ℕ := (Q.filter (E p)).card

/-- The right degree after restricting the input coordinates to `Q`. -/
def rightDegreeOn (Q : Finset V) (q : V) : ℕ :=
  (Q.filter (fun p => E p q)).card

/-- Count all incidences in either order. -/
theorem sum_leftDegree_eq_sum_rightDegree :
    ∑ p, leftDegree E p = ∑ q, rightDegree E q := by
  simp only [leftDegree, rightDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Receiver degree bounds control the total incidence count. -/
theorem sum_leftDegree_le (B : ℕ) (hB : ∀ q, rightDegree E q ≤ B) :
    ∑ p, leftDegree E p ≤ B * Fintype.card V := by
  rw [sum_leftDegree_eq_sum_rightDegree]
  calc
    ∑ q, rightDegree E q ≤ ∑ _q : V, B := Finset.sum_le_sum (fun q _ => hB q)
    _ = B * Fintype.card V := by simp [Nat.mul_comm]

/-- The strict heavy threshold gives the stronger `(M+1)` counting bound. -/
theorem heavy_card_mul_succ_le (M B : ℕ) (hB : ∀ q, rightDegree E q ≤ B) :
    (heavy E M).card * (M + 1) ≤ B * Fintype.card V := by
  calc
    (heavy E M).card * (M + 1) = ∑ _p ∈ heavy E M, (M + 1) := by simp
    _ ≤ ∑ p ∈ heavy E M, leftDegree E p := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.mem_filter.mp hp |>.2
    _ ≤ ∑ p, leftDegree E p := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ B * Fintype.card V := sum_leftDegree_le E B hB

/-- The usual degree-trimming budget, with natural division rounded down. -/
theorem heavy_card_le (M B : ℕ) (hM : 0 < M) (hB : ∀ q, rightDegree E q ≤ B) :
    (heavy E M).card ≤ (B * Fintype.card V) / M := by
  apply (Nat.le_div_iff_mul_le hM).mpr
  exact (Nat.mul_le_mul_left _ (Nat.le_succ M)).trans (heavy_card_mul_succ_le E M B hB)

/-- The retained coordinates and the paid coordinates partition the universe. -/
theorem retained_card_add_heavy_card [DecidableEq V] (M : ℕ) :
    (retained E M).card + (heavy E M).card = Fintype.card V := by
  simpa only [retained, Finset.card_univ] using
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (heavy E M))

/-- Restriction of receiver coordinates never increases a left degree. -/
theorem leftDegreeOn_le (Q : Finset V) (p : V) :
    leftDegreeOn E Q p ≤ leftDegree E p :=
  Finset.card_le_card (Finset.filter_subset_filter (E p) (Finset.subset_univ Q))

/-- Restriction of input coordinates never increases a right degree. -/
theorem rightDegreeOn_le (Q : Finset V) (q : V) :
    rightDegreeOn E Q q ≤ rightDegree E q :=
  Finset.card_le_card
    (Finset.filter_subset_filter (fun p => E p q) (Finset.subset_univ Q))

/-- Every surviving input has degree at most the chosen threshold, even before
discarding receivers. This also applies to every further induced restriction. -/
theorem retained_leftDegree_le [DecidableEq V] (M : ℕ) {p : V} (hp : p ∈ retained E M) :
    leftDegree E p ≤ M := by
  have hp' : p ∉ heavy E M := (Finset.mem_sdiff.mp hp).2
  simpa only [heavy, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hp'

/-- The exact finite core of paid degree trimming. No symmetry, loop exclusion,
or computation hypothesis is assumed. -/
theorem degree_trimming [DecidableEq V] (M B : ℕ) (hM : 0 < M)
    (hB : ∀ q, rightDegree E q ≤ B) :
    (heavy E M).card ≤ (B * Fintype.card V) / M ∧
      (∀ p ∈ retained E M, leftDegreeOn E (retained E M) p ≤ max B M) ∧
      (∀ q ∈ retained E M, rightDegreeOn E (retained E M) q ≤ max B M) := by
  refine ⟨heavy_card_le E M B hM hB, ?_, ?_⟩
  · intro p hp
    exact ((leftDegreeOn_le E _ p).trans (retained_leftDegree_le E M hp)).trans
      (le_max_right B M)
  · intro q _
    exact ((rightDegreeOn_le E _ q).trans (hB q)).trans (le_max_left B M)

end LeanMachine.IncidenceTrimming
