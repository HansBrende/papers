import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Finite raw-input erosion. Any interval cover pays at most two radius
strips per interval; maximal disjoint components are only a special case. -/

namespace AdaptiveTransfer

open Finset Classical
open scoped BigOperators

def inputErosion (U : Finset ℤ) (R : ℕ) : Finset ℤ :=
  U.filter fun z => Icc (z - (R : ℤ)) (z + (R : ℤ)) ⊆ U

/-- An actual point shadow of an eroded read is a read in the original set. -/
theorem inputErosion_shadow_mem {U : Finset ℤ} {R : ℕ} {y x : ℤ}
    (hy : y ∈ inputErosion U R) (hshadow : |y - x| ≤ R) : x ∈ U := by
  have hh := abs_le.mp hshadow
  exact (mem_filter.mp hy).2 (mem_Icc.mpr ⟨by omega, by omega⟩)

theorem trimmed_interval_subset_erosion {U : Finset ℤ} {a b : ℤ} (R : ℕ)
    (hab : Icc a b ⊆ U) : Icc (a + (R : ℤ)) (b - (R : ℤ)) ⊆ inputErosion U R := by
  intro z hz
  obtain ⟨haz, hzb⟩ := mem_Icc.mp hz
  apply mem_filter.mpr
  refine ⟨hab (mem_Icc.mpr ⟨by omega, by omega⟩), ?_⟩
  intro y hy
  obtain ⟨hzy, hyz⟩ := mem_Icc.mp hy
  exact hab (mem_Icc.mpr ⟨by omega, by omega⟩)

def intervalFringe (a b : ℤ) (R : ℕ) : Finset ℤ :=
  Ico a (a + (R : ℤ)) ∪ Ioc (b - (R : ℤ)) b

theorem intervalFringe_card_le (a b : ℤ) (R : ℕ) :
    (intervalFringe a b R).card ≤ 2 * R := by
  calc
    _ ≤ (Ico a (a + (R : ℤ))).card + (Ioc (b - (R : ℤ)) b).card := card_union_le _ _
    _ = 2 * R := by simp only [Int.card_Ico, Int.card_Ioc]; omega

theorem interval_union_erosion_loss {ι : Type*} (I : Finset ι)
    (a b : ι → ℤ) (R : ℕ) :
    ((I.biUnion fun i => Icc (a i) (b i)) \
      inputErosion (I.biUnion fun i => Icc (a i) (b i)) R).card ≤ 2 * R * I.card := by
  let U := I.biUnion fun i => Icc (a i) (b i)
  have hsub : U \ inputErosion U R ⊆ I.biUnion fun i => intervalFringe (a i) (b i) R := by
    intro z hz
    obtain ⟨hzU, hznot⟩ := mem_sdiff.mp hz
    obtain ⟨i, hi, hzi⟩ := mem_biUnion.mp hzU
    obtain ⟨haz, hzb⟩ := mem_Icc.mp hzi
    have htrim : z ∉ Icc (a i + (R : ℤ)) (b i - (R : ℤ)) := by
      intro hztrim
      apply hznot
      exact trimmed_interval_subset_erosion R
        (fun y hy => mem_biUnion.mpr ⟨i, hi, hy⟩) hztrim
    apply mem_biUnion.mpr
    refine ⟨i, hi, ?_⟩
    by_cases hzleft : z < a i + (R : ℤ)
    · exact mem_union_left _ (mem_Ico.mpr ⟨haz, hzleft⟩)
    · apply mem_union_right
      apply mem_Ioc.mpr
      refine ⟨?_, hzb⟩
      by_contra hn
      exact htrim (mem_Icc.mpr ⟨by omega, by omega⟩)
  calc
    _ ≤ (I.biUnion fun i => intervalFringe (a i) (b i) R).card := card_le_card hsub
    _ ≤ ∑ i ∈ I, (intervalFringe (a i) (b i) R).card := card_biUnion_le
    _ ≤ ∑ _i ∈ I, 2 * R := sum_le_sum fun i _ => intervalFringe_card_le _ _ _
    _ = 2 * R * I.card := by simp [mul_comm]

theorem demanded_erosion_loss {ι : Type*} (I : Finset ι)
    (a b : ι → ℤ) (R : ℕ) (V : Finset ℤ)
    (hV : V ⊆ I.biUnion fun i => Icc (a i) (b i)) :
    V.card ≤ (V ∩ inputErosion (I.biUnion fun i => Icc (a i) (b i)) R).card +
      2 * R * I.card := by
  let U := I.biUnion fun i => Icc (a i) (b i)
  have hsub : V \ inputErosion U R ⊆ U \ inputErosion U R := by
    intro z hz
    exact mem_sdiff.mpr ⟨hV (mem_sdiff.mp hz).1, (mem_sdiff.mp hz).2⟩
  have hc := (card_le_card hsub).trans (interval_union_erosion_loss I a b R)
  have heq := card_sdiff_add_card_inter V (inputErosion U R)
  change V.card ≤ (V ∩ inputErosion U R).card + 2 * R * I.card
  omega

end AdaptiveTransfer
