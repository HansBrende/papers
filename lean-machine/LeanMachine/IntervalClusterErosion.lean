import LeanMachine.AnchoredGapErosion
import LeanMachine.CircularSubdivision
import LeanMachine.IntervalOscillation

/-! Complete observable ranges over time intervals give anchored erosion.
Intervals may overlap and need not form a partition. -/

namespace LeanMachine.IntervalClusterErosion

open Classical Finset CyclicSelection AnchoredCircularCover AnchoredGapErosion
open WeightedCircularGap CircularSubdivision IntervalOscillation
open scoped BigOperators
noncomputable section

theorem mem_closed_arc_of_between {N a b u : ℕ} (hab : a ≤ b) (hb : b < N)
    (hu : a ≤ u ∧ u ≤ b) : u ∈ arc N a (b - a + 1) := by
  apply mem_image.mpr
  refine ⟨u - a, mem_range.mpr (by omega), ?_⟩
  rw [Nat.add_sub_of_le hu.1, Nat.mod_eq_of_lt (hu.2.trans_lt hb)]

/-- The actual union of all range intervals is paid once. Its quadratic
erosion bound also holds with the easier sum-of-variations budget. -/
theorem area_lower_bound {κ : Type*} {L : ℕ} {S₀ S : Finset ℕ}
    (hS₀ : S₀.Nonempty) (hS₀L : S₀ ⊆ range L)
    (hS : S.Nonempty) (hSL : S ⊆ range L)
    (I : Finset κ) (Y : κ → ℕ → ℕ) (first last rep : κ → ℕ)
    (hrep : ∀ i ∈ I, first i ≤ rep i ∧ rep i ≤ last i)
    (hrange : ∀ i ∈ I, ∀ u, first i ≤ u → u ≤ last i → Y i u < L)
    (hanchor : ∀ i ∈ I, Y i (rep i) ∈ S₀)
    (hcover : ∀ a ∈ S, a ∈ S₀ ∨ ∃ i ∈ I, ∃ u,
      first i ≤ u ∧ u ≤ last i ∧ Y i u = a) {E : ℝ}
    (hE : (∑ i ∈ I, ∑ u ∈ Ico (first i) (last i),
      dist (Y i u : ℝ) (Y i (u + 1) : ℝ)) ≤ E) :
    GapErosion.pointArea (range S₀.card) (gap L S₀ hS₀) L -
      penalty (min (E / (L : ℝ)) 1) ≤
    GapErosion.pointArea (range S.card) (gap L S hS) L := by
  let a i := lower (Y i) (first i) (last i)
  let b i := upper (Y i) (first i) (last i)
  let len i := b i - a i
  have hab i : a i ≤ b i := lower_le_upper ..
  have hb i (hi : i ∈ I) : b i < L := by
    obtain ⟨u, hu, he⟩ := upper_attained (Y i) (first i) (last i)
    obtain ⟨hu₁, hu₂⟩ := (mem_times ((hrep i hi).1.trans (hrep i hi).2)).mp hu
    change upper (Y i) (first i) (last i) < L
    rw [he]
    exact hrange i hi u hu₁ hu₂
  have ha i (hi : i ∈ I) : a i < L := (hab i).trans_lt (hb i hi)
  have hlen i (hi : i ∈ I) : len i ≤ L := by have := hb i hi; dsimp [len]; omega
  have hmem i (hi : i ∈ I) {u : ℕ} (hu : first i ≤ u ∧ u ≤ last i) :
      Y i u ∈ arc L (a i) (len i + 1) := by
    have ht := (mem_times (hu.1.trans hu.2)).mpr hu
    exact mem_closed_arc_of_between (hab i) (hb i hi) ⟨lower_le ht, le_upper ht⟩
  have hcover' : S ⊆ S₀ ∪ coveredVertices L I a len := by
    intro z hz
    rcases hcover z hz with hz | ⟨i, hi, u, hu₁, hu₂, rfl⟩
    · exact mem_union_left _ hz
    · exact mem_union_right _ (mem_biUnion.mpr ⟨i, hi, hmem i hi ⟨hu₁, hu₂⟩⟩)
  have hcost : ((coveredEdges L I a len).card : ℝ) ≤ E := by
    have hcard : (coveredEdges L I a len).card ≤ ∑ i ∈ I, len i := by
      exact card_biUnion_le.trans (sum_le_sum fun i hi => (arc_card (hlen i hi)).le)
    calc
      _ ≤ ∑ i ∈ I, (len i : ℝ) := by exact_mod_cast hcard
      _ ≤ _ := (sum_le_sum fun i hi =>
        oscillation_le_interval_variation (Y i) ((hrep i hi).1.trans (hrep i hi).2)).trans hE
  have h := AnchoredGapErosion.area_lower_bound hS₀ hS₀L hS hSL I a len ha hlen
    (fun i hi => ⟨Y i (rep i), hanchor i hi, hmem i hi (hrep i hi)⟩)
    hcover' (w := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
    (by simpa [circumference] using (Nat.cast_pos.mpr (cycle_pos hS₀ hS₀L) : (0 : ℝ) < L))
    (by simpa [coveredLength] using hcost)
  simpa only [area_one hS₀ hS₀L, area_one hS hSL,
    circumference, sum_const, card_range, nsmul_eq_mul, mul_one] using h

end
end LeanMachine.IntervalClusterErosion
