import AdaptiveTransfer.CoreReplayClass
import AdaptiveTransfer.NativeReturnCounting

/-! Exact ordinary and sparse message costs for actual multi-core classes.
Each selected-run entry pays either its clustered fringe or its complementary
head window. This proves the single k*max bill, not a sum of two k bills. -/

namespace AdaptiveTransfer
open Transpose Finset NativeRelations LeanMachine
open scoped BigOperators

namespace CoreReplayClass
variable {M : TM} {P : ℕ} {π : Fin P → Fin P} (g : CoreReplayClass M P π)

theorem snapshotDomain_card : Fintype.card g.SnapshotDomain =
    if g.start = 0 then 0 else ∑ h : Fin M.k, (g.core h).card := by
  simp only [SnapshotDomain, Fintype.card_sigma, Fintype.card_coe, snapshotCells_card]
  split_ifs <;> simp

theorem entryCells_card_le {L : ℕ} (hfr : ∀ h, (g.fringe h).card ≤ L) (hwin : 2 * g.radius + 1 ≤ L)
    (r : ℕ) (h : Fin M.k) : (g.entryCells r h).card ≤ L := by
  unfold entryCells
  split_ifs
  · exact hfr h
  · have he : (Icc (g.workEntry r h - g.radius) (g.workEntry r h + g.radius)).card = 2 * g.radius + 1 := by
      rw [Int.card_Icc]
      omega
    exact he ▸ hwin

theorem entryDomain_card_le {N L : ℕ} (hN : (runStarts g.times).card ≤ N)
    (hfr : ∀ h, (g.fringe h).card ≤ L) (hwin : 2 * g.radius + 1 ≤ L) :
    Fintype.card g.EntryDomain ≤ N * M.k * L := by
  simp only [EntryDomain, Fintype.card_sigma, Fintype.card_coe]
  calc
    _ ≤ ∑ _r : runStarts g.times, ∑ _h : Fin M.k, L :=
      sum_le_sum fun r _ => sum_le_sum fun h _ => g.entryCells_card_le hfr hwin r.val h
    _ = (runStarts g.times).card * M.k * L := by simp [Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hN)

theorem bits_card_bound (q a : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    g.inputs.card ≤ 2 ^ (P - g.omitted.card + g.ordinaryBits q a) *
      returnSparseMenu M.k g.limit g.tags (M.g + 1) := by
  classical
  calc
    g.inputs.card ≤ (Fintype.card g.Exterior * Fintype.card g.Ordinary) * Fintype.card g.Imports := by
      simpa only [Fintype.card_coe, Fintype.card_prod] using
        Fintype.card_le_of_injective _ g.records_injective
    _ ≤ (2 ^ (P - g.omitted.card) * 2 ^ g.ordinaryBits q a) *
        returnSparseMenu M.k g.limit g.tags (M.g + 1) := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul g.exterior_card.le (g.ordinary_card_le q a hq ha)
      · simpa only [returnSparseMenu, ← sparseMenu_truncate] using g.imports_card_le
    _ = _ := by rw [pow_add]

/-- All source-dependent native fields have already been encoded and replayed;
this final invoice uses only the actual geometric saving and finite budgets. -/
theorem saving_exponent_le (q a N L : ℕ) (hN : (runStarts g.times).card ≤ N)
    (hfr : ∀ h, (g.fringe h).card ≤ L) (hwin : 2 * g.radius + 1 ≤ L)
    (saving : ℝ) (hsaving : saving ≤ (g.omitted.card : ℝ) - (a : ℝ) * Fintype.card g.SnapshotDomain) :
    ((P - g.omitted.card + g.ordinaryBits q a : ℕ) : ℝ) ≤
      (P : ℝ) - saving + (N : ℝ) * q + (a : ℝ) * N * M.k * L := by
  have hc : g.omitted.card ≤ P := by simpa only [Fintype.card_fin] using card_le_univ g.omitted
  have hr : ((runStarts g.times).card : ℝ) ≤ N := by exact_mod_cast hN
  have hq' := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg q)
  have he : (Fintype.card g.EntryDomain : ℝ) ≤ (N : ℝ) * M.k * L := by
    exact_mod_cast g.entryDomain_card_le hN hfr hwin
  have ha' := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg a)
  simp only [ordinaryBits, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hc]
  nlinarith

theorem saving_card_bound (q a N L : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a)
    (hN : (runStarts g.times).card ≤ N) (hfr : ∀ h, (g.fringe h).card ≤ L)
    (hwin : 2 * g.radius + 1 ≤ L) (saving : ℝ)
    (hsaving : saving ≤ (g.omitted.card : ℝ) - (a : ℝ) * Fintype.card g.SnapshotDomain) :
    (g.inputs.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - saving + (N : ℝ) * q +
      (a : ℝ) * N * M.k * L) * (returnSparseMenu M.k g.limit g.tags (M.g + 1) : ℕ) := by
  have hh : (g.inputs.card : ℝ) ≤ (2 : ℝ) ^ ((P - g.omitted.card + g.ordinaryBits q a : ℕ) : ℝ) *
      (returnSparseMenu M.k g.limit g.tags (M.g + 1) : ℕ) := by exact_mod_cast g.bits_card_bound q a hq ha
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (g.saving_exponent_le q a N L hN hfr hwin saving hsaving)) (by positivity))

end CoreReplayClass
end AdaptiveTransfer
