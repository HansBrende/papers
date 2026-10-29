import LeanMachine.FractionalCover
import LeanMachine.IntervalGapArea

set_option autoImplicit false

/-!
# Fractional set covers through shared raw intervals

Weights are transferred to shared interval components before interval
rounding. The proof retains the exact weighted incidence cost and charges
each component's raw width only once.
-/

namespace LeanMachine.FractionalIntervalGap

open Finset
open scoped BigOperators
noncomputable section

variable {ι β : Type*} [Fintype ι] [Fintype β]

def componentWeight (C : ι → Finset β) (w : ι → ℝ) (c : β) : ℝ := by
  classical
  exact ∑ u, if c ∈ C u then w u else 0

omit [Fintype β] in
theorem componentWeight_nonneg (C : ι → Finset β) {w : ι → ℝ}
    (hw : ∀ u, 0 ≤ w u) (c : β) : 0 ≤ componentWeight C w c := by
  classical
  apply sum_nonneg
  intro u _
  split_ifs
  · exact hw u
  · rfl

theorem componentWeight_cost (C : ι → Finset β) (w : ι → ℝ) :
    (∑ c, componentWeight C w c) = ∑ u, ((C u).card : ℝ) * w u := by
  classical
  unfold componentWeight
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  simp

/-- Transfer fractional coverage to shared components. Coincident components
receive the sum of all contributing root weights. -/
theorem componentWeight_covers {S : Finset ℕ} {A : ι → Set ℕ}
    (C : ι → Finset β) (lo hi : β → ℕ)
    (hsub : ∀ u, ∀ z ∈ A u, ∃ c ∈ C u, lo c ≤ z ∧ z ≤ hi c)
    {w : ι → ℝ} (hw : FractionalCover.Covers S A w) :
    FractionalCover.Covers S (fun c => Set.Icc (lo c) (hi c)) (componentWeight C w) := by
  classical
  refine ⟨componentWeight_nonneg C hw.1, fun z hz => ?_⟩
  apply (hw.2 z hz).trans
  have hswap : (∑ c, if z ∈ Set.Icc (lo c) (hi c) then componentWeight C w c else 0) =
      ∑ u, ∑ c, if z ∈ Set.Icc (lo c) (hi c) then
        (if c ∈ C u then w u else 0) else 0 := by
    calc
      _ = ∑ c, ∑ u, if z ∈ Set.Icc (lo c) (hi c) then
          (if c ∈ C u then w u else 0) else 0 := by
        apply sum_congr rfl
        intro c _
        by_cases hc : z ∈ Set.Icc (lo c) (hi c) <;> simp [componentWeight, hc]
      _ = _ := sum_comm
  have hdec : (∑ c, @ite ℝ (z ∈ Set.Icc (lo c) (hi c))
      (Classical.propDecidable _) (componentWeight C w c) 0) =
      ∑ c, if z ∈ Set.Icc (lo c) (hi c) then componentWeight C w c else 0 := by
    apply sum_congr rfl
    intro c _
    by_cases hc : z ∈ Set.Icc (lo c) (hi c) <;> simp only [hc, ↓reduceIte]
  apply le_trans ?_ (hdec.trans hswap).symm.le
  apply sum_le_sum
  intro u _
  have hnonneg (c : β) : 0 ≤ if z ∈ Set.Icc (lo c) (hi c) then
      (if c ∈ C u then w u else 0) else 0 := by
    split_ifs <;> first | exact hw.1 u | rfl
  by_cases hzu : z ∈ A u
  · obtain ⟨c, hc, hlo, hhi⟩ := hsub u z hzu
    have hsingle := single_le_sum (fun c _ => hnonneg c) (mem_univ c)
    simpa only [ite_eq_left hzu, Set.mem_Icc, and_self_iff,
      show z ∈ Set.Icc (lo c) (hi c) from ⟨hlo, hhi⟩, ite_true,
      ite_eq_left hc] using hsingle
  · simpa only [ite_eq_right hzu] using sum_nonneg fun c _ => hnonneg c

/-- Interval rounding counts each distinct shared component only once. -/
theorem exists_subcover {S : Finset ℕ} {A : ι → Set ℕ}
    (C : ι → Finset β) (lo hi : β → ℕ)
    (hsub : ∀ u, ∀ z ∈ A u, ∃ c ∈ C u, lo c ≤ z ∧ z ≤ hi c)
    {w : ι → ℝ} (hw : FractionalCover.Covers S A w) :
    ∃ I : Finset β, (∀ z ∈ S, ∃ c ∈ I, lo c ≤ z ∧ z ≤ hi c) ∧
      (I.card : ℝ) ≤ ∑ u, ((C u).card : ℝ) * w u := by
  classical
  have hc := componentWeight_covers C lo hi hsub hw
  obtain ⟨I, _, hcover, hcard⟩ := IntervalCover.exists_subcover_le_weight S univ
    (fun c => Set.Icc (lo c) (hi c)) (componentWeight C w)
    (fun _ _ => Set.ordConnected_Icc) (fun c _ => hc.1 c) hc.2
  exact ⟨I, hcover, hcard.trans_eq (componentWeight_cost C w)⟩

/-- Exact weighted component incidence can be used instead of a uniform
component-count bound. Widths are charged on the shared component family. -/
theorem point_area_lower_of_incidence_budget {L : ℕ} (hL : 0 < L)
    {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L) {A : ι → Set ℕ}
    (C : ι → Finset β) (lo hi : β → ℕ)
    (hsub : ∀ u, ∀ z ∈ A u, ∃ c ∈ C u, lo c ≤ z ∧ z ≤ hi c)
    {w : ι → ℝ} (hw : FractionalCover.Covers S A w) {α M : ℝ}
    (hV : (∑ c, ((hi c - lo c : ℕ) : ℝ)) ≤ α * L)
    (hM : (∑ u, ((C u).card : ℝ) * w u) ≤ M) :
    (max (1 - α) 0) ^ 2 / (2 * M) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L := by
  classical
  obtain ⟨I, hcover, hcount⟩ := exists_subcover C lo hi hsub hw
  have hwidth : (∑ c ∈ I, ((hi c - lo c : ℕ) : ℝ)) ≤ α * L := by
    apply le_trans _ hV
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
  exact IntervalGapArea.point_area_lower_of_budgets hL hS hSL I lo hi
    hcover hwidth (hcount.trans hM)

omit [Fintype β] in
/-- Uniform component counts specialize the exact weighted incidence ledger. -/
theorem incidence_le_uniform_cost (C : ι → Finset β) {w : ι → ℝ}
    (hw : ∀ u, 0 ≤ w u) {p : ℝ} (hp : ∀ u, ((C u).card : ℝ) ≤ p) :
    (∑ u, ((C u).card : ℝ) * w u) ≤ p * FractionalCover.cost w := by
  calc
    _ ≤ ∑ u, p * w u := sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (hp u) (hw u)
    _ = _ := by rw [← mul_sum]; rfl

/-- The minimum fractional-cover value supplies the original gap-area bound.
No independent positivity hypothesis on the component-count budget is needed. -/
theorem point_area_lower_of_uniform_bound {L : ℕ} (hL : 0 < L)
    {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L) {A : ι → Set ℕ}
    (C : ι → Finset β) (lo hi : β → ℕ)
    (hsub : ∀ u, ∀ z ∈ A u, ∃ c ∈ C u, lo c ≤ z ∧ z ≤ hi c)
    (hfeasible : ∃ w, FractionalCover.Covers S A w) {α p : ℝ}
    (hV : (∑ c, ((hi c - lo c : ℕ) : ℝ)) ≤ α * L)
    (hp : ∀ u, ((C u).card : ℝ) ≤ p) :
    (max (1 - α) 0) ^ 2 / (2 * p * FractionalCover.value S A) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L := by
  obtain ⟨w, hw, hcost, _⟩ := FractionalCover.exists_optimal hfeasible
  have hM := incidence_le_uniform_cost C hw.1 hp
  rw [hcost] at hM
  simpa only [mul_assoc] using
    point_area_lower_of_incidence_budget hL hS hSL C lo hi hsub hw hV hM

/-- Finite extended cover numbers reduce to the same minimum-value theorem. -/
theorem point_area_lower_of_finite_number {L : ℕ} (hL : 0 < L)
    {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L) {A : ι → Set ℕ}
    (C : ι → Finset β) (lo hi : β → ℕ)
    (hsub : ∀ u, ∀ z ∈ A u, ∃ c ∈ C u, lo c ≤ z ∧ z ≤ hi c)
    (hfinite : FractionalCover.number S A ≠ ⊤) {α p : ℝ}
    (hV : (∑ c, ((hi c - lo c : ℕ) : ℝ)) ≤ α * L)
    (hp : ∀ u, ((C u).card : ℝ) ≤ p) :
    (max (1 - α) 0) ^ 2 / (2 * p * (FractionalCover.number S A).toReal) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L := by
  have hfeasible := (FractionalCover.number_ne_top_iff S A).mp hfinite
  rw [FractionalCover.number_toReal hfeasible]
  exact point_area_lower_of_uniform_bound hL hS hSL C lo hi hsub hfeasible hV hp

end
end LeanMachine.FractionalIntervalGap
