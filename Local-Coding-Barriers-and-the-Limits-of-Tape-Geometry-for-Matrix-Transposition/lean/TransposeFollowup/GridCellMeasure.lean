import TransposeFollowup.MonotoneCellOverlap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! Exact mass of unions of open grid cells, and coverage of the unit interval
outside a finite null set of grid endpoints. -/

namespace TransposeFollowup

open Classical MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false

def gridCell {n : ℕ} (i : Fin n) : Set ℝ := {x | InGridCell i x}

def gridCells {n : ℕ} (A : Finset (Fin n)) : Set ℝ := ⋃ i ∈ A, gridCell i

def gridBoundary (n : ℕ) : Set ℝ := Set.range (fun j : Fin (n + 1) => (j.val : ℝ) / n)

theorem gridCell_eq_Ioo {n : ℕ} (i : Fin n) :
    gridCell i = Ioo ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  ext x
  simp only [gridCell, InGridCell, mem_ofPred_eq, mem_Ioo,
    div_lt_iff₀ hn, lt_div_iff₀ hn, mul_comm x (n : ℝ)]

theorem gridCell_measurable {n : ℕ} (i : Fin n) : MeasurableSet (gridCell i) := by
  rw [gridCell_eq_Ioo]
  exact measurableSet_Ioo

theorem gridCell_pairwise_disjoint {n : ℕ} :
    Pairwise (fun i j : Fin n => Disjoint (gridCell i) (gridCell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (Fin.ext (Nat.le_antisymm (gridCell_index_mono hi hj le_rfl)
    (gridCell_index_mono hj hi le_rfl)))

theorem gridCell_subset_unit {n : ℕ} (i : Fin n) : gridCell i ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  change (i.val : ℝ) < n * x ∧ (n : ℝ) * x < i.val + 1 at hx
  constructor <;> nlinarith

theorem gridCells_subset_unit {n : ℕ} (A : Finset (Fin n)) :
    gridCells A ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hi
  exact gridCell_subset_unit i hx

theorem gridCells_measurable {n : ℕ} (A : Finset (Fin n)) : MeasurableSet (gridCells A) := by
  exact MeasurableSet.biUnion (Finset.countable_toSet A) (fun i _ => gridCell_measurable i)

theorem gridCell_volume_real {n : ℕ} (i : Fin n) :
    volume.real (gridCell i) = 1 / (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  rw [gridCell_eq_Ioo, Real.volume_real_Ioo_of_le (by gcongr; linarith)]
  ring

theorem gridCells_volume_ne_top {n : ℕ} (A : Finset (Fin n)) : volume (gridCells A) ≠ ⊤ := by
  exact ne_top_of_le_ne_top (by simp) (measure_mono (gridCells_subset_unit A))

theorem gridCells_volume_real {n : ℕ} (A : Finset (Fin n)) :
    volume.real (gridCells A) = (A.card : ℝ) / n := by
  have hfinite : ∀ i ∈ A, volume (gridCell i) ≠ ⊤ := by
    intro i _
    rw [gridCell_eq_Ioo, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  rw [gridCells, measureReal_biUnion_finset
    (fun i _ j _ hij => gridCell_pairwise_disjoint hij)
    (fun i _ => gridCell_measurable i) hfinite]
  simp_rw [gridCell_volume_real]
  simp [div_eq_mul_inv]

theorem gridBoundary_volume (n : ℕ) : volume (gridBoundary n) = 0 :=
  (Set.finite_range _).measure_zero volume

theorem gridBoundary_subset_unit {n : ℕ} (hn : 0 < n) :
    gridBoundary n ⊆ Icc (0 : ℝ) 1 := by
  rintro x ⟨j, rfl⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hj : (j.val : ℝ) ≤ n := by exact_mod_cast (show j.val ≤ n by have := j.isLt; omega)
  exact ⟨by positivity, (div_le_one hn').mpr hj⟩

theorem exists_gridCell_of_not_boundary {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hb : x ∉ gridBoundary n) : ∃ i : Fin n, InGridCell i x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg hn'.le hx.1
  have hnxn : (n : ℝ) * x ≤ n := by nlinarith [hx.2]
  have hfloor := Nat.floor_le hnx
  have hupper := Nat.lt_floor_add_one ((n : ℝ) * x)
  have hfn : ⌊(n : ℝ) * x⌋₊ ≤ n := by exact_mod_cast hfloor.trans hnxn
  have hne : (⌊(n : ℝ) * x⌋₊ : ℝ) ≠ (n : ℝ) * x := by
    intro he
    apply hb
    refine ⟨⟨⌊(n : ℝ) * x⌋₊, by omega⟩, ?_⟩
    exact (div_eq_iff hn'.ne').mpr (by simpa [mul_comm] using he)
  have hlt := lt_of_le_of_ne hfloor hne
  have hfin : ⌊(n : ℝ) * x⌋₊ < n := by exact_mod_cast hlt.trans_le hnxn
  exact ⟨⟨⌊(n : ℝ) * x⌋₊, hfin⟩, hlt, hupper⟩

theorem unit_subset_gridCells_union_boundary {n : ℕ} (hn : 0 < n) :
    Icc (0 : ℝ) 1 ⊆ gridCells (Finset.univ : Finset (Fin n)) ∪ gridBoundary n := by
  intro x hx
  by_cases hb : x ∈ gridBoundary n
  · exact Or.inr hb
  · obtain ⟨i, hi⟩ := exists_gridCell_of_not_boundary hn hx hb
    exact Or.inl (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hi⟩⟩)

end TransposeFollowup
