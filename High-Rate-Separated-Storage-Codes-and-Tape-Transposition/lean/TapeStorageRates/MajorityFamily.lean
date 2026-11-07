import TapeStorageRates.MajorityMatrixTail
import TapeStorageRates.SyndromeRates
import TapeStorageRates.RelabelFamily
import TapeStorageRates.DegreeInversion
import LeanMachine.OddPowerChoice

/-! # Actual separated binary families from an explicit linear seed

All codes in this file are syndrome fibres on the original tensor coordinates.
The only existence input is `OddGirthLinearSeed`; no machine realization or
efficient generation of its recovery coefficients is asserted.
-/

namespace TapeStorageRates

open Filter DirectedRecovery MotionDepthCodes

set_option autoImplicit false
noncomputable section

namespace Majority

variable {K V : Type*} [Field K] [Fintype K] [Fintype V] [DecidableEq V]

/-- The actual majority matrix has a nonempty binary syndrome fibre with
exponentially small rate deficit. No alphabet expansion is used. -/
theorem exists_binary_code_rate (A : Matrix V V K) (hdiag : ∀ v, A v v = 0)
    (h2 : (2 : K) ≠ 0) (U : Submodule K (V → K))
    (hU : U ≤ LinearMap.ker (1 - A).mulVecLin) {m : ℕ} (hm : Odd m)
    (hV : 0 < Fintype.card V) {ρ : ℝ} (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    (hρU : ρ * Fintype.card V ≤ Module.finrank K U) :
    ∃ C : Finset ((Fin m → V) → Bool), C.Nonempty ∧
      IsStorageCode (matrixHelpers (1 - matrix A m)) C ∧
      1 - Real.logb 2 (Fintype.card K) *
        Real.exp (-LeanMachine.BinomialTail.decay ρ * m) ≤ storageCodeRate C := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp hV
  obtain ⟨C, hC, hs, hr⟩ := matrix_exists_binary_code_rate (1 - matrix A m)
    (fun v => by rw [check_diagonal A hdiag h2 hm v]; exact one_ne_zero)
  refine ⟨C, hC, hs, le_trans ?_ hr⟩
  have hq : 0 ≤ Real.logb 2 (Fintype.card K) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)
  have hN : 0 < (Fintype.card (Fin m → V) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (Fin m → V) : ℝ) = (Fintype.card V : ℝ)^m := by
    simp
  have hbound := mul_le_mul_of_nonneg_right
    (check_rank_le_exp A h2 U hU m hV hρ hρ1 hρU) hq
  apply sub_le_sub_left
  apply (div_le_iff₀ hN).mpr
  rw [hcard]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hbound

end Majority

namespace OddGirthLinearSeed

variable {K : Type} [Field K] [Fintype K] {D : ℕ} {ρ : ℝ}
variable (S : OddGirthLinearSeed K D ρ)

include S

/-- A positive-dimensional seed cannot have degree zero. This removes an
otherwise unnecessary hypothesis from degree-cap inversion. -/
theorem degree_pos (hρ : 0 < ρ) : 0 < D := by
  classical
  obtain ⟨j, hj⟩ := (S.eventually_size_pos).exists
  by_contra hD
  have hD0 : D = 0 := by omega
  have hA : S.recoveryMatrix j = 0 := by
    ext q p
    apply S.recoveryMatrix_supported j q p
    intro hqp
    have hp := hqp.degree_pos_left
    have hd := S.degree j q
    omega
  have hb := S.finrank_add_check_rank_le j
  simp only [hA, sub_zero, Matrix.rank_one, Fintype.card_fin] at hb
  have hr := S.dimension j
  have hn : 0 < (S.size j : ℝ) := by exact_mod_cast hj
  have hzero : Module.finrank K (S.code j) = 0 := by omega
  rw [hzero, Nat.cast_zero] at hr
  exact (not_le_of_gt (mul_pos hρ hn)) hr

/-- Fixing any odd amplification order before the family index grows gives
an actual separated binary family. A finite initial seed prefix is discarded
only to make every displayed length positive. -/
theorem exists_majority_family (h2 : (2 : K) ≠ 0)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) {m : ℕ} (hm : Odd m) :
    ∃ F : SeparatedBinaryFamily ((D + 1)^m), ∀ j,
      1 - Real.logb 2 (Fintype.card K) *
        Real.exp (-LeanMachine.BinomialTail.decay ρ * m) ≤ storageCodeRate (F.code j) := by
  classical
  obtain ⟨j₀, hpos, hgrow, _, _, hdegree, hfar⟩ :=
    S.exists_majority_matrix_tail h2 hρ hρ1 hm
  let V (j : ℕ) := S.majorityCoordinates m (j + j₀)
  let N (j : ℕ) := matrixHelpers (S.majorityCheck m (j + j₀))
  have hex (j : ℕ) := Majority.exists_binary_code_rate (S.recoveryMatrix (j + j₀))
    (S.recoveryMatrix_diagonal _) h2 (S.code _) (S.code_le_kernel _) hm
    (by simpa using hpos j) hρ hρ1 (by simpa using S.dimension (j + j₀))
  choose C hC hs hr using hex
  have hcardpos (j : ℕ) : 0 < Fintype.card (V j) := by
    simpa [V, majorityCoordinates] using pow_pos (hpos j) m
  have hdegree' (j : ℕ) (v : V j ⊕ V j) :
      (pairedIncidenceGraph (N j)).degree v ≤ (D + 1)^m :=
    (Nat.le_add_right _ 1).trans (hdegree j v)
  obtain ⟨F, hF⟩ := exists_separated_family_of_finite_coordinates V N C
    hcardpos hgrow hC hs hdegree' hfar
  exact ⟨F, fun j => (hF j).2.symm ▸ hr j⟩

/-- Every cap at least `D + 1` supports a family with a polynomially small
binary rate deficit. The field, seed, and rate margin are fixed before the
cap, and the amplification order is fixed before the family index grows. -/
theorem exists_family_at_cap (h2 : (2 : K) ≠ 0)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) {Δ : ℕ} (hΔ : D + 1 ≤ Δ) :
    ∃ F : SeparatedBinaryFamily Δ, ∀ j,
      1 - (Real.logb 2 (Fintype.card K) * Real.exp (2 * LeanMachine.BinomialTail.decay ρ)) *
        (Δ : ℝ) ^ (-LeanMachine.BinomialTail.decay ρ / Real.log (D + 1 : ℕ)) ≤
          storageCodeRate (F.code j) := by
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hρ
  have hp : 1 < D + 1 := by have := S.degree_pos hρpos; omega
  have ha := LeanMachine.BinomialTail.decay_pos hρ hρ1
  obtain ⟨m, _, hm, hmcap, _, he⟩ :=
    LeanMachine.OddPowerChoice.exists_odd_power_and_decay hp hΔ ha.le
  obtain ⟨F, hF⟩ := S.exists_majority_family h2 hρ hρ1 hm
  refine ⟨F.atCap hmcap, fun j => ?_⟩
  have hq : 0 ≤ Real.logb 2 (Fintype.card K) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)
  have herror := mul_le_mul_of_nonneg_left he hq
  rw [← mul_assoc] at herror
  exact (sub_le_sub_left herror 1).trans (hF j)

end OddGirthLinearSeed

end
end TapeStorageRates
