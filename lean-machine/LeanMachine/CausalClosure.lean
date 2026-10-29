import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union

/-! Finite causal closures and their undominated suppliers. -/

namespace LeanMachine

open Classical Finset
noncomputable section

structure CausalClosure where
  reach : ℕ → Finset ℕ
  self_mem : ∀ t, t ∈ reach t
  trans : ∀ {t u v}, u ∈ reach t → v ∈ reach u → v ∈ reach t
  past : ∀ {t u}, u ∈ reach t → u ≤ t

namespace CausalClosure

variable (C : CausalClosure)

def hull (S : Finset ℕ) : Finset ℕ := S.biUnion C.reach

def maximal (S : Finset ℕ) : Finset ℕ :=
  S.filter fun t => ∀ u ∈ S, t ∈ C.reach u → u = t

theorem maximal_subset (S : Finset ℕ) : C.maximal S ⊆ S := filter_subset ..

/-- Maximizing the ordinary time among dominators gives a maximal supplier;
the only order fact needed is that reachability cannot increase time. -/
theorem exists_maximal {S : Finset ℕ} {t : ℕ} (ht : t ∈ S) :
    ∃ u ∈ C.maximal S, t ∈ C.reach u := by
  let D := S.filter fun u => t ∈ C.reach u
  obtain ⟨u, hu, hmax⟩ := D.exists_max_image id
    ⟨t, mem_filter.mpr ⟨ht, C.self_mem t⟩⟩
  obtain ⟨huS, htu⟩ := mem_filter.mp hu
  refine ⟨u, mem_filter.mpr ⟨huS, ?_⟩, htu⟩
  intro v hv huv
  exact Nat.le_antisymm (hmax v (mem_filter.mpr ⟨hv, C.trans huv htu⟩)) (C.past huv)

/-- The whole complete closure is unchanged, not just its seed set. -/
theorem hull_maximal (S : Finset ℕ) : C.hull (C.maximal S) = C.hull S := by
  apply Subset.antisymm
  · exact biUnion_subset_biUnion_of_subset_left _ (C.maximal_subset S)
  · intro v hv
    obtain ⟨t, ht, hvt⟩ := mem_biUnion.mp hv
    obtain ⟨u, hu, htu⟩ := C.exists_maximal ht
    exact mem_biUnion.mpr ⟨u, hu, C.trans htu hvt⟩

theorem root_mem_maximal {S : Finset ℕ} {t : ℕ} (ht : t ∈ S)
    (hS : ∀ u ∈ S, u ≤ t) : t ∈ C.maximal S := by
  exact mem_filter.mpr ⟨ht, fun u hu htu => Nat.le_antisymm (hS u hu) (C.past htu)⟩

/-- Removing suppliers already in a closed base preserves the augmented set. -/
theorem closed_union_hull_maximal_diff {B : Finset ℕ}
    (hB : ∀ t ∈ B, C.reach t ⊆ B) (S : Finset ℕ) :
    B ∪ C.hull (C.maximal (S \ B)) = B ∪ C.hull S := by
  rw [C.hull_maximal]
  apply Subset.antisymm
  · exact union_subset_union (Subset.refl B)
      (biUnion_subset_biUnion_of_subset_left _ sdiff_subset)
  · intro u hu
    rcases mem_union.mp hu with hu | hu
    · exact mem_union_left _ hu
    · obtain ⟨t, ht, hut⟩ := mem_biUnion.mp hu
      by_cases htB : t ∈ B
      · exact mem_union_left _ (hB t htB hut)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨t, mem_sdiff.mpr ⟨ht, htB⟩, hut⟩)

end CausalClosure
end
end LeanMachine
