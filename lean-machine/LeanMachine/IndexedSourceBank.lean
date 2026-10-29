import LeanMachine.SourceBank
import Mathlib.Data.List.OfFn

/-! A list bank as a finite family. Values discard multiplicity; variation
retains it. Both presentations are definitionally the same collection. -/

namespace LeanMachine.SourceBank

open Classical Finset MonotonePatches
noncomputable section

def indexed (B : Bank) (i : Fin B.length) : ℕ → ℕ := B.get i

theorem indexed_values (B : Bank) (t : ℕ) :
    univ.image (fun i => indexed B i t) = values B t := by
  ext u
  simp only [mem_image, mem_univ, true_and, mem_values]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨B.get i, List.get_mem B i, hi⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨i, rfl⟩

theorem indexed_cost {X : Type*} [PseudoMetricSpace X]
    (B : Bank) (Y : ℕ → X) (n : ℕ) :
    (∑ i, variation (Y ∘ indexed B i) n) = cost B Y n := by
  conv_rhs => rw [cost, ← List.ofFn_get B]
  simp only [List.map_ofFn, List.sum_ofFn, indexed, Function.comp_def]

theorem indexed_nonempty {B : Bank} {t u : ℕ} (hu : u ∈ values B t) :
    Nonempty (Fin B.length) := by
  rw [← indexed_values] at hu
  obtain ⟨i, _, _⟩ := mem_image.mp hu
  exact ⟨i⟩

end
end LeanMachine.SourceBank
