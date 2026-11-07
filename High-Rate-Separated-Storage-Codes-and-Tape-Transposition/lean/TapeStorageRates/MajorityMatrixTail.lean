import TapeStorageRates.OddGirthLinearSeed
import TapeStorageRates.MajorityRank
import TapeStorageRates.MajoritySupport
import Mathlib.Order.Filter.AtTopBot.Ring

/-! # One actual amplified matrix sequence on a positive seed tail -/

namespace TapeStorageRates.OddGirthLinearSeed

open Filter DirectedRecovery

set_option autoImplicit false
noncomputable section

variable {K : Type} [Field K] [Fintype K] {D : ℕ} {ρ : ℝ}
variable (S : OddGirthLinearSeed K D ρ)

/-- The original tensor coordinates, before their optional relabeling by a
single finite ordinal. -/
abbrev majorityCoordinates (m j : ℕ) := Fin m → Fin (S.size j)

/-- The check matrix whose binary syndrome partition is used throughout. -/
def majorityCheck (m j : ℕ) :
    Matrix (S.majorityCoordinates m j) (S.majorityCoordinates m j) K :=
  1 - Majority.matrix (S.recoveryMatrix j) m

open Classical in
/-- A single finite prefix makes every coordinate set nonempty. The same
actual check matrices then witness growth, rank, degree, and paired distance;
these are matrix properties, independent of the choice of a syndrome fibre. -/
theorem exists_majority_matrix_tail (h2 : (2 : K) ≠ 0)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) {m : ℕ} (hm : Odd m) :
    ∃ j₀ : ℕ,
      (∀ j, 0 < S.size (j + j₀)) ∧
      Tendsto (fun j => Fintype.card (S.majorityCoordinates m (j + j₀))) atTop atTop ∧
      (∀ j q, S.majorityCheck m (j + j₀) q q = 1) ∧
      (∀ j, ((S.majorityCheck m (j + j₀)).rank : ℝ) ≤
        Real.exp (-LeanMachine.BinomialTail.decay ρ * m) *
          Fintype.card (S.majorityCoordinates m (j + j₀))) ∧
      (∀ j v, (pairedIncidenceGraph (matrixHelpers (S.majorityCheck m (j + j₀)))).degree v + 1
        ≤ (D + 1)^m) ∧
      ∀ r : ℕ, ∀ᶠ j in atTop, ∀ q : S.majorityCoordinates m (j + j₀),
        ¬ (pairedIncidenceGraph (matrixHelpers (S.majorityCheck m (j + j₀)))).edist
          (Sum.inl q) (Sum.inr q) ≤ r := by
  classical
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp S.eventually_size_pos
  have hpos (j : ℕ) : 0 < S.size (j + j₀) := hj₀ _ (Nat.le_add_left _ _)
  have hmpos : 0 < m := by obtain ⟨k, hk⟩ := hm; omega
  have hA (j : ℕ) (q p : Fin (S.size j)) (h : S.recoveryMatrix j q p ≠ 0) :
      (S.graph j).Adj q p := by
    by_contra hn
    exact h (S.recoveryMatrix_supported j q p hn)
  refine ⟨j₀, hpos, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [majorityCoordinates, Function.comp_def] using
      (Filter.tendsto_pow_atTop (α := ℕ) hmpos.ne').comp
        (S.growing.comp (tendsto_add_atTop_nat j₀))
  · intro j q
    exact Majority.check_diagonal (S.recoveryMatrix _) (S.recoveryMatrix_diagonal _) h2 hm q
  · intro j
    simpa [majorityCheck, majorityCoordinates] using
      Majority.check_rank_le_exp (S.recoveryMatrix (j + j₀)) h2 (S.code _)
        (S.code_le_kernel _) m (by simpa using hpos j) hρ hρ1
        (by simpa using S.dimension (j + j₀))
  · intro j v
    exact Majority.check_helpers_degree_add_one_le (S.graph (j + j₀))
      (S.recoveryMatrix _) (hA _) h2 hm (S.degree _) v
  · intro r
    filter_upwards [(tendsto_add_atTop_nat j₀).eventually (S.long_odd r)] with j hj
    exact Majority.check_helpers_paired_far (S.graph (j + j₀))
      (S.recoveryMatrix _) (hA _) h2 hm hj

end
end TapeStorageRates.OddGirthLinearSeed
