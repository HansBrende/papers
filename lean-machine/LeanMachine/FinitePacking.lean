import Mathlib

/-!
# Packing finite families of bounded overlap

A maximal disjoint subfamily covers every member by intersection. Bounded
member size and bounded point multiplicity control the number of members
charged to each selected member.
-/

namespace LeanMachine.FinitePacking

open scoped BigOperators

/-- Extract a disjoint subfamily without losing more than the product of
the size and point-multiplicity bounds. -/
theorem exists_disjoint_subfamily {I V : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq V] (S : I → Finset V) (a b : ℕ)
    (hne : ∀ i, (S i).Nonempty) (hsize : ∀ i, (S i).card ≤ a)
    (hmult : ∀ v, (Finset.univ.filter (fun i => v ∈ S i)).card ≤ b) :
    ∃ J : Finset I, (J : Set I).PairwiseDisjoint S ∧
      Fintype.card I ≤ a * b * J.card := by
  classical
  obtain ⟨J, _, hJ⟩ := Finite.exists_le_maximal
    (p := fun J : Finset I => (J : Set I).PairwiseDisjoint S)
    (a := ∅) (by simp)
  have hcover : ∀ i, ∃ j ∈ J, ¬ Disjoint (S i) (S j) := by
    intro i
    by_contra! hnone
    have hins : ((insert i J : Finset I) : Set I).PairwiseDisjoint S := by
      rw [Finset.coe_insert]
      exact Set.pairwise_insert.mpr ⟨hJ.1, fun j hj _ =>
        ⟨hnone j hj, (hnone j hj).symm⟩⟩
    have hi : i ∈ J := hJ.2 hins (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
    obtain ⟨v, hv⟩ := hne i
    exact Finset.disjoint_left.mp (hnone i hi) hv hv
  let meet (j : I) := Finset.univ.filter (fun i => ¬ Disjoint (S i) (S j))
  have hmeet (j : I) : (meet j).card ≤ a * b := by
    have hsub : meet j ⊆ (S j).biUnion (fun v => Finset.univ.filter (fun i => v ∈ S i)) := by
      intro i hi
      obtain ⟨v, hvi, hvj⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
      exact Finset.mem_biUnion.mpr ⟨v, hvj,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvi⟩⟩
    calc
      _ ≤ ((S j).biUnion (fun v => Finset.univ.filter (fun i => v ∈ S i))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ v ∈ S j, (Finset.univ.filter (fun i => v ∈ S i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ S j, b := Finset.sum_le_sum (fun v _ => hmult v)
      _ = (S j).card * b := by simp
      _ ≤ a * b := Nat.mul_le_mul_right b (hsize j)
  have hall : (Finset.univ : Finset I) ⊆ J.biUnion meet := by
    intro i _
    obtain ⟨j, hj, hij⟩ := hcover i
    exact Finset.mem_biUnion.mpr ⟨j, hj,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
  refine ⟨J, hJ.1, ?_⟩
  calc
    _ ≤ (J.biUnion meet).card := by simpa using Finset.card_le_card hall
    _ ≤ ∑ j ∈ J, (meet j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ J, a * b := Finset.sum_le_sum (fun j _ => hmeet j)
    _ = a * b * J.card := by simp [Nat.mul_comm]

/-- A bound on every disjoint subfamily bounds the whole finite family. -/
theorem card_le_of_disjoint_bound {I V : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq V] (S : I → Finset V) (a b : ℕ)
    (hne : ∀ i, (S i).Nonempty) (hsize : ∀ i, (S i).card ≤ a)
    (hmult : ∀ v, (Finset.univ.filter (fun i => v ∈ S i)).card ≤ b)
    (M : ℝ) (hM : ∀ J : Finset I, (J : Set I).PairwiseDisjoint S → (J.card : ℝ) ≤ M) :
    (Fintype.card I : ℝ) ≤ (a : ℝ) * (b : ℝ) * M := by
  obtain ⟨J, hJ, hcard⟩ := exists_disjoint_subfamily S a b hne hsize hmult
  have hc : (Fintype.card I : ℝ) ≤ (a : ℝ) * (b : ℝ) * J.card := by exact_mod_cast hcard
  exact hc.trans (mul_le_mul_of_nonneg_left (hM J hJ) (by positivity))

end LeanMachine.FinitePacking
