import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Popular intersections of indexed rows in a small common universe.
The rows need not be distinct: indices retain their multiplicities. -/
namespace TransposeFollowup.ScalarMetric
open scoped BigOperators
open Finset
set_option autoImplicit false

/-- Cauchy--Schwarz and double counting, retaining repeated indexed rows. -/
theorem indexed_row_intersection_energy {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (P : Finset α) (R : ι → Finset α)
    (hsub : ∀ i ∈ I, R i ⊆ P) :
    (∑ i ∈ I, ((R i).card : ℝ)) ^ 2 ≤
      (P.card : ℝ) * ∑ i ∈ I, ∑ j ∈ I, ((R i ∩ R j).card : ℝ) := by
  classical
  let w : ι → α → ℝ := fun i z => if z ∈ R i then 1 else 0
  have hrow (i : ι) (hi : i ∈ I) : ∑ z ∈ P, w i z = ((R i).card : ℝ) := by
    simp [w, inter_eq_right.mpr (hsub i hi)]
  have hinter (i : ι) (hi : i ∈ I) (j : ι) :
      ∑ z ∈ P, w i z * w j z = ((R i ∩ R j).card : ℝ) := by
    have hf : P.filter (fun z => z ∈ R i ∧ z ∈ R j) = R i ∩ R j := by
      ext z
      simp only [mem_filter, mem_inter]
      exact ⟨fun h => h.2, fun h => ⟨hsub i hi h.1, h⟩⟩
    have hw (z : α) : w i z * w j z = if z ∈ R i ∧ z ∈ R j then 1 else 0 := by
      simp only [w]; split_ifs <;> simp_all
    simp_rw [hw]
    simp [hf]
  have hsum : ∑ z ∈ P, ∑ i ∈ I, w i z = ∑ i ∈ I, ((R i).card : ℝ) := by
    rw [sum_comm]
    exact sum_congr rfl hrow
  have hsq : ∑ z ∈ P, (∑ i ∈ I, w i z) ^ 2 =
      ∑ i ∈ I, ∑ j ∈ I, ((R i ∩ R j).card : ℝ) := by
    simp_rw [sq, sum_mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_comm]
    exact sum_congr rfl (fun j _ => hinter i hi j)
  have h := sq_sum_le_card_mul_sum_sq (s := P) (f := fun z => ∑ i ∈ I, w i z)
  rwa [hsum, hsq] at h

/-- If `N` indexed rows each have `N` elements and fit in `K*N` positions,
there is a row meeting at least `N/(2*K)` rows in at least `N/(2*K)` positions.
Division-free bounds avoid any integer rounding convention. -/
theorem exists_popular_row_intersections {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (P : Finset α) (R : ι → Finset α) {K : ℝ}
    (hI : I.Nonempty) (hK : 0 < K)
    (hsub : ∀ i ∈ I, R i ⊆ P) (hcard : ∀ i ∈ I, (R i).card = I.card)
    (hP : (P.card : ℝ) ≤ K * I.card) :
    ∃ i ∈ I, ∃ E : Finset ι, E ⊆ I ∧
      (I.card : ℝ) ≤ 2 * K * E.card ∧
      ∀ j ∈ E, (I.card : ℝ) ≤ 2 * K * (R i ∩ R j).card := by
  classical
  let N : ℝ := I.card
  let S : ι → ℝ := fun i => ∑ j ∈ I, ((R i ∩ R j).card : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hI.card_pos
  have hS (i : ι) : 0 ≤ S i := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  obtain ⟨i, hi, hmax⟩ := I.exists_max_image S hI
  have htotal : ∑ a ∈ I, S a ≤ N * S i := by
    calc
      _ ≤ ∑ _a ∈ I, S i := sum_le_sum (fun a ha => hmax a ha)
      _ = _ := by simp [N]
  have henergy := indexed_row_intersection_energy I P R hsub
  have hrows : ∑ a ∈ I, ((R a).card : ℝ) = N * N := by
    calc
      _ = ∑ _a ∈ I, N := sum_congr rfl (fun a ha => by rw [hcard a ha])
      _ = _ := by simp [N]
  rw [hrows] at henergy
  have hbound : (N * N) ^ 2 ≤ (K * N) * (N * S i) := henergy.trans
    (mul_le_mul hP htotal (sum_nonneg (fun a _ => hS a)) (by positivity))
  have havg : N * N ≤ K * S i := by
    apply (mul_le_mul_iff_of_pos_left (show 0 < N * N by positivity)).mp
    nlinarith only [hbound]
  let E := I.filter (fun j => N ≤ 2 * K * (R i ∩ R j).card)
  have hsplit : 2 * K * S i ≤ 2 * K * (E.card : ℝ) * N + N * N := by
    have hpoint (j : ι) (hj : j ∈ I) :
        2 * K * ((R i ∩ R j).card : ℝ) ≤
          (if j ∈ E then 2 * K * N else 0) + N := by
      by_cases hjE : j ∈ E
      · have hc : ((R i ∩ R j).card : ℝ) ≤ N := by
          dsimp [N]
          exact_mod_cast (card_le_card (inter_subset_left (s₁ := R i) (s₂ := R j))).trans_eq (hcard i hi)
        have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * K by positivity)
        simp only [hjE, ↓reduceIte]
        linarith
      · have hjlow : 2 * K * ((R i ∩ R j).card : ℝ) < N := by
          simpa [E, hj, not_le] using hjE
        simp only [hjE, ↓reduceIte, zero_add]
        exact hjlow.le
    calc
      _ = ∑ j ∈ I, 2 * K * ((R i ∩ R j).card : ℝ) := by rw [mul_sum]
      _ ≤ ∑ j ∈ I, ((if j ∈ E then 2 * K * N else 0) + N) := sum_le_sum hpoint
      _ = _ := by
        rw [sum_add_distrib]
        simp only [sum_ite_mem, sum_const, nsmul_eq_mul]
        have hIE : I ∩ E = E := inter_eq_right.mpr (filter_subset _ _)
        rw [hIE]
        dsimp [N]
        ring
  refine ⟨i, hi, E, filter_subset _ _, ?_, ?_⟩
  · apply (mul_le_mul_iff_of_pos_right hN).mp
    nlinarith only [havg, hsplit]
  · intro j hj
    exact (mem_filter.mp hj).2

end TransposeFollowup.ScalarMetric
