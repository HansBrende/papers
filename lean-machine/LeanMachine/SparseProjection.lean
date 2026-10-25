import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi

/-! A sparse generating family pays for all coordinate projections of its
span. The independent subfamily is chosen from the original generators, so
the sparsity hypothesis is retained. -/

namespace LeanMachine.SparseProjection

open Module Finset Submodule
open scoped BigOperators Classical

variable {K W ι J : Type*} [Field K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] [Fintype J]
  {A : J → Type*} [∀ j, AddCommGroup (A j)] [∀ j, Module K (A j)]
  [∀ j, FiniteDimensional K (A j)]

theorem projection_rank_le_support [Fintype ι] (f : ι → W)
    (p : W →ₗ[K] A j) :
    finrank K ((span K (Set.range f)).map p) ≤
      (univ.filter fun i => p (f i) ≠ 0).card := by
  classical
  let s := univ.filter fun i => p (f i) ≠ 0
  have he : (span K (Set.range f)).map p =
      span K (Set.range fun i : s => p (f i.val)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases h : p (f i) = 0
      · simp [h]
      · exact subset_span ⟨⟨i, by simpa [s]⟩, rfl⟩
    · apply span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.val, rfl⟩
  rw [he]
  simpa only [Set.finrank, Fintype.card_coe] using
    finrank_range_le_card (R := K) (fun i : s => p (f i.val))

/-- The bound counts nonzero block projections of the original generators;
it does not assume that arbitrary vectors of their span are sparse. -/
theorem sum_projection_ranks_le (f : ι → W) (p : ∀ j, W →ₗ[K] A j)
    (k : ℕ) (hs : ∀ i, (univ.filter fun j => p j (f i) ≠ 0).card ≤ k) :
    (∑ j, finrank K ((span K (Set.range f)).map (p j))) ≤
      k * finrank K (span K (Set.range f)) := by
  classical
  obtain ⟨κ, a, _, hspan, hli⟩ := exists_linearIndependent' K f
  let : Finite κ := hli.finite
  let : Fintype κ := Fintype.ofFinite κ
  rw [← hspan, finrank_span_eq_card hli]
  calc
    (∑ j, finrank K ((span K (Set.range (f ∘ a))).map (p j))) ≤
        ∑ j, (univ.filter fun i : κ => p j (f (a i)) ≠ 0).card := by
      exact sum_le_sum (fun j _ => projection_rank_le_support (f ∘ a) (p j))
    _ = ∑ i : κ, (univ.filter fun j => p j (f (a i)) ≠ 0).card := by
      simp only [card_filter]
      rw [sum_comm]
    _ ≤ ∑ _i : κ, k := sum_le_sum (fun i _ => hs (a i))
    _ = k * Fintype.card κ := by simp [Nat.mul_comm]

end LeanMachine.SparseProjection
