import SourceCovers.OrbitCountDeficit

set_option autoImplicit false

/-!
# Finite distribution of complete-bank covers

The fraction of phase-column pairs whose actual cover weight is at most a
nonnegative threshold is bounded by that threshold times the mean reciprocal
cover weight. Both averages use the same phases and columns.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- The proportion of phase-column pairs with complete-bank fractional cover
weight at most `s`. An empty averaging set has value zero. -/
def meanCoverBelow (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ) (d b : ℕ) (A : Finset ℕ)
    (s : ℝ) : ℝ :=
  (∑ ρ ∈ A, ∑ j ∈ range d,
    if phaseCoreCover hc hM E x t d b ρ j ≤ s then (1 : ℝ) else 0) / (A.card * d)

/-- The finite distribution is between zero and one, including empty phase
sets or zero columns, without any validity assumptions on the geometry. -/
theorem meanCoverBelow_bounds (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ) (d b : ℕ) (A : Finset ℕ)
    (s : ℝ) :
    0 ≤ meanCoverBelow hc hM E x t d b A s ∧
      meanCoverBelow hc hM E x t d b A s ≤ 1 := by
  have hden : (0 : ℝ) ≤ A.card * d := by positivity
  constructor
  · exact div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => by
      split_ifs <;> norm_num) hden
  · apply div_le_one_of_le₀ _ hden
    calc
      _ ≤ ∑ ρ ∈ A, ∑ j ∈ range d, (1 : ℝ) :=
        sum_le_sum fun _ _ => sum_le_sum fun _ _ => by split_ifs <;> norm_num
      _ = _ := by simp

/-- A finite reciprocal Markov bound for the actual complete-bank covers.
Legal phases and actual output times make every sampled cover positive; no
nonemptiness premise is needed for the phase set. -/
theorem meanCoverBelow_le_mul_meanReciprocalCover (hc : HasSpanColoring K 2)
    {M d b : ℕ} (hM : 2 ≤ M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (hn : ∀ z < d * d * b, t z < T)
    (A : Finset ℕ) (hAM : ∀ ρ ∈ A, ρ < M) {s : ℝ} (hs : 0 ≤ s) :
    meanCoverBelow hc hM E x t d b A s ≤
      s * meanReciprocalCover hc hM E x t d b A := by
  have hpoint : ∀ ρ ∈ A, ∀ j ∈ range d,
      (if phaseCoreCover hc hM E x t d b ρ j ≤ s then (1 : ℝ) else 0) ≤
        s * (1 / phaseCoreCover hc hM E x t d b ρ j) := by
    intro ρ hρ j hj
    have htime := hn _ ((column_indices hd hb (mem_range.mp hj)).1.trans_lt
      (column_indices hd hb (mem_range.mp hj)).2)
    have hκ : 1 ≤ phaseCoreCover hc hM E x t d b ρ j :=
      (fractionalCoreCover_exactSourceBank_bounds hc hM (hAM ρ hρ) E x htime).2.1
    have hκpos := lt_of_lt_of_le zero_lt_one hκ
    by_cases h : phaseCoreCover hc hM E x t d b ρ j ≤ s
    · simpa only [ite_eq_left h, mul_one_div] using (one_le_div hκpos).mpr h
    · simpa only [ite_eq_right h] using mul_nonneg hs (one_div_nonneg.mpr hκpos.le)
  calc
    meanCoverBelow hc hM E x t d b A s ≤
        (∑ ρ ∈ A, ∑ j ∈ range d, s * (1 / phaseCoreCover hc hM E x t d b ρ j)) /
          (A.card * d) :=
      div_le_div_of_nonneg_right
        (sum_le_sum fun ρ hρ => sum_le_sum fun j hj => hpoint ρ hρ j hj) (by positivity)
    _ = s * meanReciprocalCover hc hM E x t d b A := by
      simp only [meanReciprocalCover, ← mul_sum, mul_div_assoc]

end
end SourceCovers
