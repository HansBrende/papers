import TapeStorageRates.OddGirthLinearSeed
import LeanMachine.BlockRankSparsity
import LeanMachine.BinomialTail

/-! # Sparse check ranks and the amplification exponent

The scalar specialization of the existing block-rank theorem bounds the
seed's possible rate. Consequently the power-law exponent is below one.
-/

namespace TapeStorageRates

open Finset Module Filter
open scoped BigOperators

set_option autoImplicit false
noncomputable section

variable {K V : Type*} [Field K] [Fintype V] [DecidableEq V]

/-- A nonzero diagonal and at most `s` supported coordinates per row force
rank at least `N/s`, over every field. -/
theorem matrix_card_le_support_mul_rank (H : Matrix V V K)
    (hd : ∀ v, H v v ≠ 0) (S : V → Finset V) (s : ℕ)
    (hc : ∀ v, (S v).card ≤ s) (hs : ∀ i j, j ∉ S i → H i j = 0) :
    Fintype.card V ≤ s * H.rank := by
  have hi (c : V) : Function.Injective (H.mulVecLin.comp (LinearMap.single K (fun _ : V => K) c)) := by
    intro x y h
    have hv := congrFun h c
    simp only [LinearMap.comp_apply, LinearMap.single_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_single] at hv
    exact mul_left_cancel₀ (hd c) hv
  have hr (c : V) :
      finrank K (LinearMap.range (H.mulVecLin.comp (LinearMap.single K (fun _ : V => K) c))) = 1 := by
    rw [LinearMap.finrank_range_of_inj (hi c), Module.finrank_self]
  have h := LeanMachine.SparseProjection.sum_column_ranks_le H.mulVecLin S s hc (by
    intro a c hca
    ext
    simp [Matrix.mulVec_single, hs a c hca])
  simpa [hr, Matrix.rank] using h

/-- A graph-supported recovery matrix gives the scalar sparse-rank bound. -/
theorem graph_check_card_le_mul_rank (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Matrix V V K) (hA : ∀ i j, ¬G.Adj i j → A i j = 0)
    {D : ℕ} (hD : ∀ v, G.degree v ≤ D) :
    Fintype.card V ≤ (D + 1) * (1 - A).rank := by
  apply matrix_card_le_support_mul_rank (1 - A)
    (fun v => by simp [Matrix.sub_apply, hA v v (G.loopless.irrefl v)])
    (fun v => insert v (G.neighborFinset v)) (D + 1)
  · intro v
    simpa [card_insert_of_notMem (G.notMem_neighborFinset_self v),
      SimpleGraph.card_neighborFinset_eq_degree] using Nat.add_le_add_right (hD v) 1
  · intro i j hj
    have hji : j ≠ i := fun he => hj (mem_insert.mpr (Or.inl he))
    have ha : ¬G.Adj i j := fun he => hj (mem_insert.mpr (Or.inr (G.mem_neighborFinset i j |>.mpr he)))
    simp [Matrix.sub_apply, Ne.symm hji, hA i j ha]

/-- Any supplied linear code on a graph of degree at most `D` has rate at
most `D/(D+1)`. The lower-rate parameter can be arbitrary. -/
theorem graph_code_rate_le_degree_fraction (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Matrix V V K) (hA : ∀ i j, ¬G.Adj i j → A i j = 0)
    {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (U : Submodule K (V → K))
    (hU : U ≤ LinearMap.ker (1 - A).mulVecLin) (hV : 0 < Fintype.card V)
    {ρ : ℝ} (hρU : ρ * Fintype.card V ≤ finrank K U) :
    ρ ≤ (D : ℝ) / (D + 1) := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
  have hb : (finrank K U : ℝ) + ((1 - A).rank : ℝ) ≤ Fintype.card V := by
    exact_mod_cast LeanMachine.LinearRecovery.finrank_add_rank_le U A hU
  have hs : (Fintype.card V : ℝ) ≤ ((D : ℝ) + 1) * ((1 - A).rank : ℝ) := by
    exact_mod_cast graph_check_card_le_mul_rank G A hA hD
  have hr : ((1 - A).rank : ℝ) ≤ (1 - ρ) * Fintype.card V := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ D + 1)
  have hc : 1 ≤ ((D : ℝ) + 1) * (1 - ρ) :=
    (mul_le_mul_iff_of_pos_right hn).mp (by nlinarith [hs, hm])
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < D + 1)).mpr
  nlinarith

namespace OddGirthLinearSeed

variable {F : Type} [Field F] [Fintype F] {D : ℕ} {ρ : ℝ}

/-- The seed existence premise itself supplies the elementary inverse-degree
rate constraint. Only one positive-size level is needed. -/
theorem rate_le_degree_fraction (S : OddGirthLinearSeed F D ρ) :
    ρ ≤ (D : ℝ) / (D + 1) := by
  classical
  obtain ⟨j, hj⟩ := S.eventually_size_pos.exists
  apply graph_code_rate_le_degree_fraction (S.graph j) (S.recoveryMatrix j)
    (S.recoveryMatrix_supported j) (S.degree j) (S.code j) (S.code_le_kernel j)
    (by simpa using hj)
  simpa using S.dimension j

end OddGirthLinearSeed

namespace Majority

/-- The decay constant agrees with the equivalent half-logarithm formula. -/
theorem decay_eq_neg_half_log {ρ : ℝ} (hρ : 0 ≤ ρ * (1 - ρ)) :
    LeanMachine.BinomialTail.decay ρ = -Real.log (4 * ρ * (1 - ρ)) / 2 := by
  have he : (2 * Real.sqrt (ρ * (1 - ρ)))^2 = 4 * ρ * (1 - ρ) := by
    rw [mul_pow, Real.sq_sqrt hρ]
    ring
  have h := Real.log_pow (2 * Real.sqrt (ρ * (1 - ρ))) 2
  rw [he] at h
  dsimp [LeanMachine.BinomialTail.decay]
  norm_num at h
  linarith

/-- The seed rate constraint makes the amplification decay strictly smaller
than half the logarithm of its degree-growth base. -/
theorem decay_lt_half_log_degree {D : ℕ} {ρ : ℝ} (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    (hbound : ρ ≤ (D : ℝ) / (D + 1)) :
    LeanMachine.BinomialTail.decay ρ < Real.log ((D : ℝ) + 1) / 2 := by
  let d : ℝ := D + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hb : ρ * d ≤ D := (le_div_iff₀ hd).mp hbound
  have hc : 1 ≤ (1 - ρ) * d := by dsimp [d] at *; nlinarith
  have hp : 0 < ρ * (1 - ρ) := mul_pos (by linarith) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ 4 * ρ)
  have hprod : 1 < (4 * ρ * (1 - ρ)) * d := by nlinarith
  have hz : 0 < 4 * ρ * (1 - ρ) := by nlinarith
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 1) hprod
  rw [Real.log_one, Real.log_mul hz.ne' hd.ne'] at hl
  rw [decay_eq_neg_half_log hp.le]
  dsimp [d] at hl
  linarith

/-- The same-support binary exponent is positive and strictly below one half. -/
theorem exponent_mem_Ioo {D : ℕ} {ρ : ℝ} (hD : 0 < D)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) (hbound : ρ ≤ (D : ℝ) / (D + 1)) :
    0 < LeanMachine.BinomialTail.decay ρ / Real.log ((D : ℝ) + 1) ∧
      LeanMachine.BinomialTail.decay ρ / Real.log ((D : ℝ) + 1) < 1 / 2 := by
  have hlog : 0 < Real.log ((D : ℝ) + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < D + 1))
  refine ⟨div_pos (LeanMachine.BinomialTail.decay_pos hρ hρ1) hlog, ?_⟩
  apply (div_lt_iff₀ hlog).mpr
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using decay_lt_half_log_degree hρ hρ1 hbound

end Majority
end
end TapeStorageRates
