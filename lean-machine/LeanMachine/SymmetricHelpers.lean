import LeanMachine.IncidenceTrimming
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

/-!
# Paid normalization of finite helper relations

Delete heavily reused helper rows, add reverse incidences, and add self loops.
The resulting relation is symmetric and reflexive with bounded width. The
fixed row/column cross has an exact inclusion-exclusion cardinality. These
finite relation statements make no claim about code capacity on their own.
-/

namespace LeanMachine.SymmetricHelpers

open Finset
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Targets that use `r` as a helper. -/
def reverseHelpers (ρ : V → Finset V) (r : V) : Finset V :=
  univ.filter fun s => r ∈ ρ s

/-- Helpers used by strictly more than `R` targets. -/
def heavyHelpers (ρ : V → Finset V) (R : ℕ) : Finset V :=
  univ.filter fun r => R < (reverseHelpers ρ r).card

/-- Delete the specified helper rows from every recovery set. -/
def trimHelpers (ρ : V → Finset V) (H : Finset V) (r : V) : Finset V :=
  ρ r \ H

/-- Symmetric reflexive closure of the trimmed relation. -/
def normalizedHelpers (ρ : V → Finset V) (H : Finset V) (r : V) : Finset V :=
  insert r (trimHelpers ρ H r ∪ reverseHelpers (trimHelpers ρ H) r)

@[simp] theorem mem_reverseHelpers (ρ : V → Finset V) (r s : V) :
    s ∈ reverseHelpers ρ r ↔ r ∈ ρ s := by simp [reverseHelpers]

@[simp] theorem mem_heavyHelpers (ρ : V → Finset V) (R : ℕ) (r : V) :
    r ∈ heavyHelpers ρ R ↔ R < (reverseHelpers ρ r).card := by simp [heavyHelpers]

omit [Fintype V] in
@[simp] theorem mem_trimHelpers (ρ : V → Finset V) (H : Finset V) (r s : V) :
    s ∈ trimHelpers ρ H r ↔ s ∈ ρ r ∧ s ∉ H := by simp [trimHelpers]

@[simp] theorem mem_normalizedHelpers (ρ : V → Finset V) (H : Finset V) (r s : V) :
    s ∈ normalizedHelpers ρ H r ↔
      s = r ∨ s ∈ trimHelpers ρ H r ∨ r ∈ trimHelpers ρ H s := by
  simp only [normalizedHelpers, mem_insert, mem_union, mem_reverseHelpers]

theorem normalizedHelpers_reflexive (ρ : V → Finset V) (H : Finset V) (r : V) :
    r ∈ normalizedHelpers ρ H r := mem_insert_self _ _

theorem normalizedHelpers_symmetric (ρ : V → Finset V) (H : Finset V) (r s : V) :
    s ∈ normalizedHelpers ρ H r ↔ r ∈ normalizedHelpers ρ H s := by
  simp only [mem_normalizedHelpers]
  tauto

theorem trimHelpers_subset_normalizedHelpers (ρ : V → Finset V) (H : Finset V) (r : V) :
    trimHelpers ρ H r ⊆ normalizedHelpers ρ H r :=
  subset_trans subset_union_left (subset_insert _ _)

/-- Only the explicitly deleted helpers can be absent from the normalized set. -/
theorem helpers_subset_normalized_union (ρ : V → Finset V) (H : Finset V) (r : V) :
    ρ r ⊆ normalizedHelpers ρ H r ∪ H := by
  intro s hs
  by_cases hH : s ∈ H
  · exact mem_union_right _ hH
  · exact mem_union_left _ (trimHelpers_subset_normalizedHelpers ρ H r
      (mem_sdiff.mpr ⟨hs, hH⟩))

/-- Trimming a helper deletes its entire reverse set and preserves all others. -/
theorem reverse_trimHelpers (ρ : V → Finset V) (H : Finset V) (r : V) :
    reverseHelpers (trimHelpers ρ H) r = if r ∈ H then ∅ else reverseHelpers ρ r := by
  by_cases hr : r ∈ H <;> ext s <;> simp [hr]

theorem reverse_trim_heavy_card_le (ρ : V → Finset V) (R : ℕ) (r : V) :
    (reverseHelpers (trimHelpers ρ (heavyHelpers ρ R)) r).card ≤ R := by
  rw [reverse_trimHelpers]
  by_cases hr : r ∈ heavyHelpers ρ R
  · simp [hr]
  · simp only [hr, ite_false]
    simpa only [mem_heavyHelpers, not_lt] using hr

/-- Forward width plus the reverse threshold and one self loop. No `R>0` is needed. -/
theorem normalizedHelpers_card_le (ρ : V → Finset V) (w R : ℕ)
    (hρ : ∀ r, (ρ r).card ≤ w) (r : V) :
    (normalizedHelpers ρ (heavyHelpers ρ R) r).card ≤ w + R + 1 := by
  have hf : (trimHelpers ρ (heavyHelpers ρ R) r).card ≤ w :=
    (card_le_card sdiff_subset).trans (hρ r)
  have hr := reverse_trim_heavy_card_le ρ R r
  calc
    _ ≤ (trimHelpers ρ (heavyHelpers ρ R) r ∪
        reverseHelpers (trimHelpers ρ (heavyHelpers ρ R)) r).card + 1 := card_insert_le _ _
    _ ≤ (trimHelpers ρ (heavyHelpers ρ R) r).card +
        (reverseHelpers (trimHelpers ρ (heavyHelpers ρ R)) r).card + 1 :=
      Nat.add_le_add_right (card_union_le _ _) 1
    _ ≤ w + R + 1 := by omega

/-- Reuse the existing incidence double count with its strict-threshold saving. -/
theorem heavyHelpers_card_mul_succ_le (ρ : V → Finset V) (w R : ℕ)
    (hρ : ∀ r, (ρ r).card ≤ w) :
    (heavyHelpers ρ R).card * (R + 1) ≤ w * Fintype.card V := by
  have h := LeanMachine.IncidenceTrimming.heavy_card_mul_succ_le
    (fun p q : V => p ∈ ρ q) R w (fun q => by
      simpa [LeanMachine.IncidenceTrimming.rightDegree] using hρ q)
  have hl (r : V) : LeanMachine.IncidenceTrimming.leftDegree
      (fun p q : V => p ∈ ρ q) r = (reverseHelpers ρ r).card := by
    unfold LeanMachine.IncidenceTrimming.leftDegree reverseHelpers
    congr 1
  have he : LeanMachine.IncidenceTrimming.heavy (fun p q : V => p ∈ ρ q) R =
      heavyHelpers ρ R := by
    ext r
    simp only [LeanMachine.IncidenceTrimming.heavy, mem_filter, mem_univ,
      true_and, mem_heavyHelpers, hl]
  rw [he] at h
  exact h

/-- Rows and columns that are fixed when the label set `H` is paid for. -/
def fixedCross (H : Finset V) : Finset (V × V) :=
  H ×ˢ univ ∪ univ ×ˢ H

@[simp] theorem mem_fixedCross (H : Finset V) (p : V × V) :
    p ∈ fixedCross H ↔ p.1 ∈ H ∨ p.2 ∈ H := by simp [fixedCross]

/-- Exact cost, keeping the overlap of the paid rows and columns. -/
theorem fixedCross_card_add_square (H : Finset V) :
    (fixedCross H).card + H.card ^ 2 = 2 * Fintype.card V * H.card := by
  have hi : (H ×ˢ univ) ∩ (univ ×ˢ H) = H ×ˢ H := by
    ext p
    simp
  have h := card_union_add_card_inter (H ×ˢ (univ : Finset V)) (univ ×ˢ H)
  rw [hi] at h
  simp only [card_product, card_univ] at h
  change (fixedCross H).card + H.card * H.card =
    H.card * Fintype.card V + Fintype.card V * H.card at h
  nlinarith only [h]

theorem fixedCross_card_le (H : Finset V) :
    (fixedCross H).card ≤ 2 * Fintype.card V * H.card := by
  have h := fixedCross_card_add_square H
  omega

end LeanMachine.SymmetricHelpers
