import LeanMachine.SparseProjection
import LeanMachine.MatrixRankCertificate

/-! A block-row support bound controls the sum of block-column ranks,
independently of all block dimensions. -/

namespace LeanMachine.SparseProjection

open Module Finset Submodule
open scoped BigOperators Classical

variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]
  {A : J → Type*} [∀ j, AddCommGroup (A j)] [∀ j, Module K (A j)]
  [∀ j, FiniteDimensional K (A j)]

def rowFamily (E : (∀ j, A j) →ₗ[K] (∀ j, A j))
    (i : Σ j, Module.Dual K (A j)) : Module.Dual K (∀ j, A j) :=
  E.dualMap ((LinearMap.proj i.1).dualMap i.2)

theorem rowFamily_span (E : (∀ j, A j) →ₗ[K] (∀ j, A j)) :
    span K (Set.range (rowFamily E)) = LinearMap.range E.dualMap := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_range_self _ _
  · rintro _ ⟨f, rfl⟩
    have he : (∑ j, rowFamily E ⟨j, f.comp (LinearMap.single K A j)⟩) =
        E.dualMap f := by
      ext x
      simp only [LinearMap.sum_apply, rowFamily, LinearMap.dualMap_apply,
        LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.single_apply]
      rw [← map_sum, LinearMap.sum_single_apply]
    rw [← he]
    apply sum_mem
    intro j _
    exact subset_span ⟨⟨j, f.comp (LinearMap.single K A j)⟩, rfl⟩

/-- A basis is selected from actual row functionals before counting support.
The result holds over any field and for unequal or zero block widths. -/
theorem sum_column_ranks_le (E : (∀ j, A j) →ₗ[K] (∀ j, A j))
    (S : J → Finset J) (k : ℕ) (hcard : ∀ j, (S j).card ≤ k)
    (hs : ∀ a c, c ∉ S a →
      (LinearMap.proj a).comp (E.comp (LinearMap.single K A c)) = 0) :
    (∑ c, finrank K (LinearMap.range (E.comp (LinearMap.single K A c)))) ≤
      k * finrank K (LinearMap.range E) := by
  have h := sum_projection_ranks_le (rowFamily E)
    (fun c => (LinearMap.single K A c).dualMap) k (by
      intro i
      apply (card_le_card (show (univ.filter fun c =>
        (LinearMap.single K A c).dualMap (rowFamily E i) ≠ 0) ⊆ S i.1 from ?_)).trans
        (hcard i.1)
      intro c hc
      by_contra hn
      have hz := hs i.1 c hn
      have he : (LinearMap.single K A c).dualMap (rowFamily E i) = 0 := by
        ext x
        change i.2 (E (LinearMap.single K A c x) i.1) = 0
        have hx := LinearMap.congr_fun hz x
        change E (LinearMap.single K A c x) i.1 = 0 at hx
        rw [hx, map_zero]
      exact (mem_filter.mp hc).2 he)
  rw [rowFamily_span, LinearMap.finrank_range_dualMap_eq_finrank_range] at h
  convert h using 1
  apply sum_congr rfl
  intro c _
  rw [← LinearMap.range_comp, LinearMap.dualMap_comp_dualMap,
    LinearMap.finrank_range_dualMap_eq_finrank_range]

end LeanMachine.SparseProjection
