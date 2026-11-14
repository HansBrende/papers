import MotionDepthCodes.StorageCode
import TransposeFollowup.ConditionalObservation
import ClosureBarriers

/-!
# Soft order and exact subcode selection

The soft order inequality below is proved for polymatroids, so it also
applies to entropies and conditional entropies. The two subcode-selection
statements at the end are retained as proposition definitions. Their proofs
are in `SubcodeSelection` and `ConditionalSubcode`; the latter also strengthens
the record bound to conditional entropy. They use actual finite probability
laws: a polymatroid alone cannot supply the words of the asserted subcode. Entropies use natural logarithms.
-/

namespace LeanBacklog.EntropyConsolidation

open Finset MotionDepthCodes TransposeFollowup
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [DecidableEq V]

/-- The conditional entropy of one coordinate, interpreted as a rank increment. -/
def recoveryError (h : Finset V → ℝ) (H : V → Finset V) (v : V) : ℝ :=
  h (insert v (H v)) - h (H v)

private theorem marginal_le {h : Finset V → ℝ} (hh : IsPolymatroid h)
    {A B : Finset V} {v : V} (hAB : A ⊆ B) :
    h (insert v B) - h B ≤ h (insert v A) - h A := by
  have hs := hh.submod (insert v A) B
  rw [Finset.insert_union, Finset.union_eq_right.mpr hAB] at hs
  have hm := hh.mono (Finset.subset_inter (Finset.subset_insert v A) hAB)
  linarith

/-- Helpers inside `A` must precede their targets. Helpers in `B` are already known. -/
theorem acyclic_conditional_le {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (H : V → Finset V) (rank : V → ℕ) (A B : Finset V)
    (hH : ∀ v ∈ A, H v ⊆ A ∪ B)
    (hr : ∀ v ∈ A, ∀ u ∈ A, u ∈ H v → rank u < rank v) :
    h (A ∪ B) - h B ≤ ∑ v ∈ A, recoveryError h H v := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases he : A = ∅
    · simp [he]
    obtain ⟨v, hv, hmax⟩ := A.exists_max_image rank (Finset.nonempty_iff_ne_empty.mpr he)
    have hH' : ∀ u ∈ A.erase v, H u ⊆ A.erase v ∪ B := by
      intro u hu z hz
      rcases Finset.mem_union.mp (hH u (Finset.mem_of_mem_erase hu) hz) with hza | hzb
      · apply Finset.mem_union_left
        apply Finset.mem_erase.mpr
        refine ⟨?_, hza⟩
        intro hzv
        subst z
        exact (not_lt_of_ge (hmax u (Finset.mem_of_mem_erase hu)))
          (hr u (Finset.mem_of_mem_erase hu) v hv hz)
      · exact Finset.mem_union_right _ hzb
    have hind := ih (A.erase v) (Finset.erase_ssubset hv) hH'
      (fun u hu z hz => hr u (Finset.mem_of_mem_erase hu) z (Finset.mem_of_mem_erase hz))
    have hHv : H v ⊆ A.erase v ∪ B := by
      intro z hz
      rcases Finset.mem_union.mp (hH v hv hz) with hza | hzb
      · apply Finset.mem_union_left
        refine Finset.mem_erase.mpr ⟨?_, hza⟩
        intro hzv
        subst z
        exact (Nat.lt_irrefl _) (hr v hv v hv hz)
      · exact Finset.mem_union_right _ hzb
    have hm := marginal_le hh (v := v) hHv
    have heq : insert v (A.erase v ∪ B) = A ∪ B := by
      rw [← Finset.insert_union, Finset.insert_erase hv]
    rw [heq] at hm
    have hsum := Finset.sum_erase_add A (recoveryError h H) hv
    change h (A ∪ B) - h (A.erase v ∪ B) ≤ recoveryError h H v at hm
    linarith

variable [Fintype V]

/-- Soft order: information shared with helpers on an induced acyclic set
is bounded by total correlation. No exact recovery or singleton cap is assumed. -/
theorem soft_order {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (H : V → Finset V) (A : Finset V) (rank : V → ℕ)
    (hr : ∀ v ∈ A, ∀ u ∈ A, u ∈ H v → rank u < rank v) :
    (∑ v ∈ A, (h {v} - recoveryError h H v)) ≤ (∑ v, h {v}) - h univ := by
  have heq : A ∪ (univ \ A) = (univ : Finset V) :=
    Finset.union_sdiff_of_subset (Finset.subset_univ A)
  have hc := acyclic_conditional_le hh H rank A (univ \ A)
    (fun v _ => by rw [heq]; exact Finset.subset_univ _) hr
  rw [heq] at hc
  have hm := hh.le_sum_singleton (univ \ A)
  have hsum := Finset.sum_sdiff (f := fun v => h {v}) (Finset.subset_univ A)
  rw [Finset.sum_sub_distrib]
  linarith

/-- Actual-distribution version, obtained from the existing entropy library. -/
theorem soft_order_entropy {Ω α : Type*} [Fintype Ω] [Fintype α]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → V → α) (H : V → Finset V) (A : Finset V) (rank : V → ℕ)
    (hr : ∀ v ∈ A, ∀ u ∈ A, u ∈ H v → rank u < rank v) :
    (∑ v ∈ A, (codeEntropy p X {v} - recoveryError (codeEntropy p X) H v)) ≤
      (∑ v, codeEntropy p X {v}) - codeEntropy p X univ :=
  soft_order (codeEntropy_isPolymatroid p X hp hp1) H A rank hr

/-- The same acyclicity notion as the assigned-rule theorem; no ordering is
an extra hypothesis beyond an explicit certificate of finite acyclicity. -/
theorem soft_order_of_acyclic {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (H : V → Finset V) (A : Finset V) (hA : ClosureBarriers.RankAcyclic H A) :
    (∑ v ∈ A, (h {v} - recoveryError h H v)) ≤ (∑ v, h {v}) - h univ := by
  obtain ⟨rank, hr⟩ := hA
  exact soft_order hh H A rank hr

/-- Original statement, proved by `SubcodeSelection.subcodeSelectionTarget`:
an exact storage subcode inside the positive
support, with the paid recovery-error entropy bound. No independent-source or
linearity assumption. Nonemptiness is explicit because `Real.log 0 = 0` in Lean. -/
def SubcodeSelectionTarget : Prop :=
  ∀ (Ω α : Type) [Fintype Ω] [Fintype α] [DecidableEq α]
    (p : Ω → ℝ), (∀ ω, 0 ≤ p ω) → (∑ ω, p ω = 1) →
    ∀ (X : Ω → V → α) (H : V → Finset V),
    ∃ D : Finset (V → α), D.Nonempty ∧
      (∀ x ∈ D, ∃ ω, 0 < p ω ∧ X ω = x) ∧ IsStorageCode H D ∧
      codeEntropy p X univ - (∑ v, recoveryError (codeEntropy p X) H v) ≤
        Real.log D.card

/-- Original statement, proved by `ConditionalSubcode.conditionalSubcodeSelectionTarget`:
the selected code lies in one record fibre.
The record can be correlated with the input, rather than a function of it. -/
def ConditionalSubcodeSelectionTarget : Prop :=
  ∀ (Ω α β : Type) [Fintype Ω] [Fintype α] [Fintype β] [DecidableEq α]
    (p : Ω → ℝ), (∀ ω, 0 ≤ p ω) → (∑ ω, p ω = 1) →
    ∀ (X : Ω → V → α) (Z : Ω → β) (H : V → Finset V),
    ∃ (z : β) (D : Finset (V → α)), D.Nonempty ∧
      (∀ x ∈ D, ∃ ω, 0 < p ω ∧ Z ω = z ∧ X ω = x) ∧ IsStorageCode H D ∧
      codeEntropy p X univ - observationEntropy p Z -
        (∑ v, conditionalObservationEntropy p (fun ω => X ω v)
          (fun ω => (view (H v) (X ω), Z ω))) ≤ Real.log D.card

#print axioms acyclic_conditional_le
#print axioms soft_order
#print axioms soft_order_entropy
#print axioms soft_order_of_acyclic

end LeanBacklog.EntropyConsolidation
