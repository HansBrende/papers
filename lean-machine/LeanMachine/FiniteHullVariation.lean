import LeanMachine.IndexedSourceBank
import Mathlib.Data.Finset.Max

set_option autoImplicit false

/-! The movement of every slot of a fixed bank over a finite set's time hull.
The empty hull is a degenerate interval at a supplied default time. -/

namespace LeanMachine.FiniteHullVariation

open Classical Finset SourceBank MonotonePatches
open scoped BigOperators
noncomputable section

def endpoints (S : Finset ℕ) (t : ℕ) : ℕ × ℕ :=
  if h : S.Nonempty then (S.min' h, S.max' h) else (t, t)

@[simp] theorem endpoints_empty (t : ℕ) : endpoints ∅ t = (t, t) := by
  simp [endpoints]

@[simp] theorem endpoints_singleton (s t : ℕ) : endpoints {s} t = (s, s) := by
  simp [endpoints]

theorem endpoints_bounds {S : Finset ℕ} {t : ℕ} (hS : ∀ u ∈ S, u ≤ t) :
    (endpoints S t).1 ≤ (endpoints S t).2 ∧ (endpoints S t).2 ≤ t := by
  unfold endpoints
  split_ifs with h
  · exact ⟨S.min'_le (S.max' h) (S.max'_mem h), hS _ (S.max'_mem h)⟩
  · exact ⟨le_rfl, le_rfl⟩

theorem mem_endpoints {S : Finset ℕ} {t u : ℕ} (hu : u ∈ S) :
    (endpoints S t).1 ≤ u ∧ u ≤ (endpoints S t).2 := by
  simp only [endpoints, dite_eq_left (show S.Nonempty from ⟨u, hu⟩)]
  exact ⟨min'_le _ _ hu, le_max' _ _ hu⟩

def movement (B : Bank) (x : ℕ → ℕ) (S : Finset ℕ) (t : ℕ) : ℝ :=
  ∑ i : Fin B.length, ∑ u ∈ Ico (endpoints S t).1 (endpoints S t).2,
    dist (x (indexed B i u) : ℝ) (x (indexed B i (u + 1)) : ℝ)

theorem movement_nonneg (B : Bank) (x : ℕ → ℕ) (S : Finset ℕ) (t : ℕ) :
    0 ≤ movement B x S t := sum_nonneg fun _ _ => sum_nonneg fun _ _ => dist_nonneg

@[simp] theorem movement_empty (B : Bank) (x : ℕ → ℕ) (t : ℕ) :
    movement B x ∅ t = 0 := by simp [movement]

@[simp] theorem movement_singleton (B : Bank) (x : ℕ → ℕ) (s t : ℕ) :
    movement B x {s} t = 0 := by simp [movement]

/-- The hull may be traversed once by every slot, so its movement is at most
that of the complete bank over the computation horizon. -/
theorem movement_le_cost (B : Bank) (x : ℕ → ℕ) {S : Finset ℕ} {t n : ℕ}
    (hS : ∀ u ∈ S, u ≤ t) (ht : t ≤ n) :
    movement B x S t ≤ cost B (fun u => (x u : ℝ)) n := by
  rw [← indexed_cost]
  apply sum_le_sum
  intro i _
  apply sum_le_sum_of_subset_of_nonneg
  · intro u hu
    exact mem_range.mpr ((mem_Ico.mp hu).2.trans_le ((endpoints_bounds hS).2.trans ht))
  · intros; exact dist_nonneg

end
end LeanMachine.FiniteHullVariation
