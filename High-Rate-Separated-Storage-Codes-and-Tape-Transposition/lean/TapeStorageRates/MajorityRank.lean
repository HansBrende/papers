import TapeStorageRates.MajorityMatrix
import TapeStorageRates.MajorityCounting
import TapeStorageRates.MajorityRate

/-! # Exact rank bounds from a specified fixed subspace -/

namespace TapeStorageRates.Majority

open Finset Module
open scoped BigOperators

set_option autoImplicit false
noncomputable section

variable {K V : Type*} [Field K] [Fintype V] [DecidableEq V]

/-- Membership in the original check kernel is exactly the fixed-vector
property required by the tensor operator. -/
theorem fixed_of_check_kernel (A : Matrix V V K) (U : Submodule K (V → K))
    (hU : U ≤ LinearMap.ker (1 - A).mulVecLin) {x : V → K} (hx : x ∈ U) :
    A.mulVecLin x = x := by
  have h := hU hx
  change (1 - A).mulVec x = 0 at h
  have he : x - A.mulVec x = 0 := by simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using h
  exact (sub_eq_zero.mp he).symm

/-- Exact integer budget before rewriting the independent-basis count. -/
theorem check_rank_add_goodIndices_le (A : Matrix V V K) (h2 : (2 : K) ≠ 0)
    (U : Submodule K (V → K)) (hU : U ≤ LinearMap.ker (1 - A).mulVecLin) (m : ℕ) :
    (1 - matrix A m).rank +
      (goodIndices (leftIndices (finrank K U) (Fintype.card V - finrank K U)) m).card ≤
        Fintype.card V ^ m := by
  have h := subspace_goodIndices_card_le_finrank_ker_of_dimension A.mulVecLin h2 U
    (fun _ hx => fixed_of_check_kernel A U hU hx) (Fintype.card V) (Module.finrank_pi K) m
  have h' := Nat.add_le_add_left h (1 - matrix A m).rank
  rw [check_rank_add_finrank_ker] at h'
  exact h'

/-- The full exact binomial dimension guarantee, expressed as an upper
bound on the actual check matrix rank. The supplied subspace may be
strictly smaller than the original check kernel. -/
theorem check_rank_add_binomial_le (A : Matrix V V K) (h2 : (2 : K) ≠ 0)
    (U : Submodule K (V → K)) (hU : U ≤ LinearMap.ker (1 - A).mulVecLin) (m : ℕ) :
    (1 - matrix A m).rank +
      (∑ a ∈ (range (m + 1)).filter (fun a => m < 2 * a),
        m.choose a * (finrank K U)^a * (Fintype.card V - finrank K U)^(m-a)) ≤
      Fintype.card V ^ m := by
  have hk : finrank K U ≤ Fintype.card V := by
    simpa only [Module.finrank_pi] using U.finrank_le
  have h := check_rank_add_goodIndices_le A h2 U hU m
  rw [goodIndices_card_eq_binomial_sum] at h
  simpa only [leftIndices_card, Fintype.card_sum, Fintype.card_fin,
    Nat.add_sub_of_le hk] using h

/-- A specified seed margin above one half gives an exponentially small
rank fraction for the actual majority check matrix. -/
theorem check_rank_le_exp (A : Matrix V V K) (h2 : (2 : K) ≠ 0)
    (U : Submodule K (V → K)) (hU : U ≤ LinearMap.ker (1 - A).mulVecLin) (m : ℕ)
    (hV : 0 < Fintype.card V) {ρ : ℝ} (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    (hρU : ρ * Fintype.card V ≤ finrank K U) :
    ((1 - matrix A m).rank : ℝ) ≤
      Real.exp (-LeanMachine.BinomialTail.decay ρ * m) * (Fintype.card V : ℝ)^m := by
  have hk : finrank K U ≤ Fintype.card V := by
    simpa only [Module.finrank_pi] using U.finrank_le
  let P := leftIndices (finrank K U) (Fintype.card V - finrank K U)
  have hc : Fintype.card (Fin (finrank K U) ⊕ Fin (Fintype.card V - finrank K U)) =
      Fintype.card V := by simp only [Fintype.card_sum, Fintype.card_fin, Nat.add_sub_of_le hk]
  have hn : 0 < Fintype.card (Fin (finrank K U) ⊕ Fin (Fintype.card V - finrank K U)) :=
    hc.symm ▸ hV
  have hr : ρ ≤ (P.card : ℝ) /
      Fintype.card (Fin (finrank K U) ⊕ Fin (Fintype.card V - finrank K U)) := by
    simp only [hc, P, leftIndices_card]
    exact (le_div_iff₀ (by exact_mod_cast hV)).mpr hρU
  have hgood := goodIndices_card_ge_exp P m hn hρ hρ1 hr
  rw [hc] at hgood
  have hbudget : ((1 - matrix A m).rank : ℝ) + ((goodIndices P m).card : ℝ) ≤
      (Fintype.card V : ℝ)^m := by
    exact_mod_cast check_rank_add_goodIndices_le A h2 U hU m
  nlinarith

end
end TapeStorageRates.Majority
