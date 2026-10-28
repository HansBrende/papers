import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum

/-!
# Finite interval covers

A finite cover by order-connected sets has a subcover and a packing of
the same size. Each original set contains at most one packing point.
Double counting then bounds this subcover by every fractional cover.
The target may be empty, and the order-connected sets need not be closed
or bounded. No optimization or linear-programming library is needed.
-/

namespace LeanMachine.IntervalCover

open Classical
open scoped BigOperators

/-- A greedy cover comes with an equally large packing certificate. -/
theorem exists_cover_packing {α ι : Type*} [LinearOrder α]
    (S : Finset α) (I : Finset ι) (A : ι → Set α)
    (hconv : ∀ i ∈ I, (A i).OrdConnected)
    (hcover : ∀ x ∈ S, ∃ i ∈ I, x ∈ A i) :
    ∃ C ⊆ I, ∃ P ⊆ S,
      (∀ x ∈ S, ∃ i ∈ C, x ∈ A i) ∧ C.card = P.card ∧
      ∀ i ∈ I, (P.filter (fun x => x ∈ A i)).card ≤ 1 := by
  classical
  induction S using Finset.strongInductionOn generalizing I with
  | _ S ih =>
    obtain hS | hS := S.eq_empty_or_nonempty
    · subst S
      exact ⟨∅, Finset.empty_subset _, ∅, by simp⟩
    obtain ⟨x, hx, hmin⟩ := S.exists_min_image id hS
    let B := S.filter (fun y => ∃ i ∈ I, x ∈ A i ∧ y ∈ A i)
    have hxB : x ∈ B := by
      obtain ⟨i, hi, hxi⟩ := hcover x hx
      exact Finset.mem_filter.mpr ⟨hx, i, hi, hxi, hxi⟩
    obtain ⟨y, hyB, hmax⟩ := B.exists_max_image id ⟨x, hxB⟩
    obtain ⟨hy, j, hj, hxj, hyj⟩ := Finset.mem_filter.mp hyB
    have hxy : x ≤ y := hmax x hxB
    let T := S.filter (fun z => y < z)
    have hTS : T ⊆ S := Finset.filter_subset _ _
    have hxT : x ∉ T := by simp [T, not_lt_of_ge hxy]
    have hsep (i : ι) (hi : i ∈ I) (hxi : x ∈ A i)
        (z : α) (hz : z ∈ T) : z ∉ A i := by
      intro hzi
      exact (Finset.mem_filter.mp hz).2.not_ge
        (hmax z (Finset.mem_filter.mpr ⟨hTS hz, i, hi, hxi, hzi⟩))
    have hTcover : ∀ z ∈ T, ∃ i ∈ I.erase j, z ∈ A i := by
      intro z hz
      obtain ⟨i, hi, hzi⟩ := hcover z (hTS hz)
      have hij : i ≠ j := by
        intro he
        exact hsep j hj hxj z hz (he ▸ hzi)
      exact ⟨i, Finset.mem_erase.mpr ⟨hij, hi⟩, hzi⟩
    obtain ⟨C, hCI, P, hPT, hCcover, hcard, hpack⟩ :=
      ih T (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, fun he => hxT (he ▸ hx)⟩)
        (I.erase j) (fun i hi => hconv i (Finset.mem_of_mem_erase hi)) hTcover
    have hjC : j ∉ C := fun hj' => (Finset.mem_erase.mp (hCI hj')).1 rfl
    have hxP : x ∉ P := fun hx' => hxT (hPT hx')
    refine ⟨insert j C, Finset.insert_subset hj (hCI.trans (Finset.erase_subset _ _)),
      insert x P, Finset.insert_subset hx (hPT.trans hTS), ?_, ?_, ?_⟩
    · intro z hz
      by_cases hyz : y < z
      · obtain ⟨i, hi, hzi⟩ := hCcover z (Finset.mem_filter.mpr ⟨hz, hyz⟩)
        exact ⟨i, Finset.mem_insert_of_mem hi, hzi⟩
      · exact ⟨j, Finset.mem_insert_self _ _,
          (hconv j hj).out hxj hyj ⟨hmin z hz, le_of_not_gt hyz⟩⟩
    · simp only [Finset.card_insert_of_notMem hjC, Finset.card_insert_of_notMem hxP, hcard]
    · intro i hi
      by_cases hxi : x ∈ A i
      · have hempty : P.filter (fun z => z ∈ A i) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro z hz
          exact hsep i hi hxi z (hPT hz)
        simp [Finset.filter_insert, hxi, hempty]
      · have hij : i ≠ j := by rintro rfl; exact hxi hxj
        simpa [Finset.filter_insert, hxi] using hpack i (Finset.mem_erase.mpr ⟨hij, hi⟩)

/-- Weak duality for any finite incidence relation, with no order hypothesis. -/
theorem packing_le_fractional_cover {α ι : Type*}
    (P : Finset α) (I : Finset ι) (A : ι → Set α) (w : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i)
    (hcover : ∀ x ∈ P, 1 ≤ ∑ i ∈ I, if x ∈ A i then w i else 0)
    (hpack : ∀ i ∈ I, (P.filter (fun x => x ∈ A i)).card ≤ 1) :
    (P.card : ℝ) ≤ ∑ i ∈ I, w i := by
  calc
    _ = ∑ _x ∈ P, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ P, ∑ i ∈ I, if x ∈ A i then w i else 0 :=
      Finset.sum_le_sum hcover
    _ = ∑ i ∈ I, ((P.filter (fun x => x ∈ A i)).card : ℝ) * w i := by
      rw [Finset.sum_comm]
      simp [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ I, w i := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using mul_le_mul_of_nonneg_right (show
        ((P.filter (fun x => x ∈ A i)).card : ℝ) ≤ 1 by exact_mod_cast hpack i hi) (hw i hi)

/-- Fractional covers of finite targets by order-connected sets round without loss. -/
theorem exists_subcover_le_weight {α ι : Type*} [LinearOrder α]
    (S : Finset α) (I : Finset ι) (A : ι → Set α) (w : ι → ℝ)
    (hconv : ∀ i ∈ I, (A i).OrdConnected) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hcover : ∀ x ∈ S, 1 ≤ ∑ i ∈ I, if x ∈ A i then w i else 0) :
    ∃ C ⊆ I, (∀ x ∈ S, ∃ i ∈ C, x ∈ A i) ∧ (C.card : ℝ) ≤ ∑ i ∈ I, w i := by
  have hc : ∀ x ∈ S, ∃ i ∈ I, x ∈ A i := by
    intro x hx
    by_contra! h
    have hz : (∑ i ∈ I, if x ∈ A i then w i else 0) = 0 :=
      Finset.sum_eq_zero (fun i hi => ite_eq_right (h i hi))
    have := hcover x hx
    rw [hz] at this
    norm_num at this
  obtain ⟨C, hCI, P, hPS, hc, heq, hp⟩ := exists_cover_packing S I A hconv hc
  refine ⟨C, hCI, hc, ?_⟩
  rw [heq]
  exact packing_le_fractional_cover P I A w hw (fun x hx => hcover x (hPS hx)) hp

end LeanMachine.IntervalCover
