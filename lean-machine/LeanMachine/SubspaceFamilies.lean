import LeanMachine.SubspaceDefect

/-! Dimension budgets for finitely many named, distinct coordinate spaces. -/

namespace LeanMachine.SubspaceDefect

open Module Finset
open scoped BigOperators Classical

variable {ι J K W : Type*} [Fintype ι] [Fintype J] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem family_mass_le (U : ι → Submodule K W) (S : Submodule K W)
    (f : J → ι) (hf : Function.Injective f) (L : J → Submodule K W)
    (hL : ∀ i, L i ≤ U (f i) ⊓ S) :
    (∑ i, finrank K (L i)) ≤ ∑ v, finrank K (U v ⊓ S : Submodule K W) := by
  calc
    _ ≤ ∑ i, finrank K (U (f i) ⊓ S : Submodule K W) :=
      sum_le_sum (fun i _ => Submodule.finrank_mono (hL i))
    _ = ∑ v ∈ univ.image f, finrank K (U v ⊓ S : Submodule K W) := by
      rw [sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

/-- Exhausting the positive-deficit budget determines every coordinate
intersection, including the zero intersections outside the named family. -/
theorem exact_finite_family (U : ι → Submodule K W) (S : Submodule K W)
    (hpos : 1 ≤ defect U S) (f : J → ι) (hf : Function.Injective f)
    (L : J → Submodule K W) (hL : ∀ i, L i ≤ U (f i) ⊓ S)
    (hbudget : (∑ i, finrank K (L i)) + 1 = 2 * finrank K S) :
    defect U S = 1 ∧ (∀ i, U (f i) ⊓ S = L i) ∧
      (∀ v, (∀ i, v ≠ f i) → U v ⊓ S = ⊥) := by
  let m : ι → ℕ := fun v => ∑ i, if v = f i then finrank K (L i) else 0
  have hmimage (i : J) : m (f i) = finrank K (L i) := by simp [m, hf.eq_iff]
  have hmoutside {v : ι} (h : ∀ i, v ≠ f i) : m v = 0 := by simp [m, h]
  have hm : ∀ v, m v ≤ finrank K (U v ⊓ S : Submodule K W) := by
    intro v
    by_cases h : ∃ i, v = f i
    · obtain ⟨i, rfl⟩ := h
      rw [hmimage]
      exact Submodule.finrank_mono (hL i)
    · rw [hmoutside (fun i he => h ⟨i, he⟩)]
      exact Nat.zero_le _
  have hsum : ∑ v, m v = ∑ i, finrank K (L i) := by
    unfold m
    rw [sum_comm]
    simp
  obtain ⟨ht, he⟩ := exact_intersections U S hpos m hm (by rw [hsum]; exact hbudget)
  refine ⟨ht, ?_, ?_⟩
  · intro i
    apply Eq.symm
    apply Submodule.eq_of_le_of_finrank_eq (hL i)
    rw [he, hmimage]
  · intro v hv
    apply Submodule.finrank_eq_zero.mp
    rw [he, hmoutside hv]

/-- A one-dimensional subspace either lies in a test space or is disjoint
from it. No distributivity of the subspace lattice is used. -/
theorem line_le_or_disjoint (L S : Submodule K W) (hL : finrank K L = 1) :
    L ≤ S ∨ Disjoint L S := by
  by_cases hI : L ⊓ S = ⊥
  · exact Or.inr (disjoint_iff.mpr hI)
  have hdim : 0 < finrank K (L ⊓ S : Submodule K W) := by
    have hn : finrank K (L ⊓ S : Submodule K W) ≠ 0 :=
      fun h => hI (Submodule.finrank_eq_zero.mp h)
    omega
  have hle := Submodule.finrank_mono (inf_le_left : L ⊓ S ≤ L)
  have he : L ⊓ S = L := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  exact Or.inl (inf_eq_left.mp he)

end LeanMachine.SubspaceDefect
