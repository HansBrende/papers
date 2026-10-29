import SourceCovers.SubsetHelper
import LeanMachine.SubsetGapCounting
import LeanMachine.CyclicGapScaling
import Mathlib.Analysis.SpecificLimits.Basic

/-! The helper cost and the actual raw-circle gap area have the exact
calibration in Proposition 7.3. The limits allow arbitrary positive row
repetitions and bit widths, including logarithmic entry width. -/

namespace SourceCovers.SubsetHelper

open Finset LeanMachine CyclicSelection Filter
open scoped BigOperators Classical Topology
noncomputable section

theorem input_bits_pos {N k h b : ℕ} (hN : 0 < N) (hk : k ≤ N)
    (hh : 0 < h) (hb : 0 < b) : 0 < inputBits N k h b := by
  have hF := Nat.choose_pos hk
  unfold inputBits side
  positivity

theorem bin_length {N k h b : ℕ} (hN : 0 < N) :
    inputBits N k h b / N = N * (N.choose k) ^ 2 * h ^ 2 * b := by
  have he : inputBits N k h b = N * (N * (N.choose k) ^ 2 * h ^ 2 * b) := by
    unfold inputBits side
    ring
  rw [he, Nat.mul_div_right _ hN]

theorem bin_length_pos {N k h b : ℕ} (hN : 0 < N) (hk : k ≤ N)
    (hh : 0 < h) (hb : 0 < b) : 0 < inputBits N k h b / N := by
  rw [bin_length hN]
  have hF := Nat.choose_pos hk
  positivity

theorem bin_length_mul {N k h b : ℕ} (hN : 0 < N) :
    (inputBits N k h b / N) * N = inputBits N k h b := by
  rw [bin_length hN]
  unfold inputBits side
  ring

theorem helper_fraction {N k h b : ℕ} (hN : 0 < N) (hk : k ≤ N)
    (hh : 0 < h) (hb : 0 < b) :
    (helperBits N k h b : ℝ) / inputBits N k h b =
      ((N : ℝ) - k) / (N * (k + 1)) := by
  have hL : (inputBits N k h b : ℝ) ≠ 0 := by
    exact_mod_cast (input_bits_pos hN hk hh hb).ne'
  rw [helper_bits_formula N k h b hN hk]
  field_simp

/-- The physical raw anchors, with the integer bin length `L/N`. -/
def rawPoints (N k h b : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image ((inputBits N k h b / N) * ·)

theorem rawPoints_subset {N k h b : ℕ} (hN : 0 < N) (hk : k ≤ N)
    (hh : 0 < h) (hb : 0 < b) {S : Finset ℕ} (hS : S ⊆ range N) :
    rawPoints N k h b S ⊆ range (inputBits N k h b) := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  exact mem_range.mpr ((Nat.mul_lt_mul_of_pos_left (mem_range.mp (hS hi))
    (bin_length_pos hN hk hh hb)).trans_eq (bin_length_mul hN))

def meanGapArea (N k h b : ℕ) : ℝ :=
  (∑ S ∈ (range N).powersetCard k,
    pointGapArea (inputBits N k h b) (rawPoints N k h b S)) / N.choose k

/-- The mean is independent of both repetition and word width. The
formal statement also includes `k = 1` and `k = N`. -/
theorem mean_gap_formula {N k h b : ℕ} (hk : 0 < k) (hkN : k ≤ N)
    (hh : 0 < h) (hb : 0 < b) :
    meanGapArea N k h b = (2 * (N : ℝ) - k + 1) / (2 * N * (k + 1)) := by
  have hN : 0 < N := hk.trans_le hkN
  have he (S : Finset ℕ) :
      pointGapArea (inputBits N k h b) (rawPoints N k h b S) = pointGapArea N S := by
    unfold rawPoints
    conv_lhs => arg 1; rw [← bin_length_mul hN]
    exact pointGapArea_scaled (bin_length_pos hN hkN hh hb) S
  simp only [meanGapArea, he]
  exact mean_pointGapArea hk hkN

theorem gap_helper_calibration {N k h b : ℕ} (hk : 0 < k) (hkN : k ≤ N)
    (hh : 0 < h) (hb : 0 < b) :
    meanGapArea N k h b =
      (helperBits N k h b : ℝ) / inputBits N k h b + 1 / (2 * N) := by
  have hN : 0 < N := hk.trans_le hkN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mean_gap_formula hk hkN hh hb, helper_fraction hN hkN hh hb]
  field_simp
  ring

theorem query_row_fraction {N k h : ℕ} (hN : 0 < N) (hk : k ≤ N)
    (hh : 0 < h) (S : SubsetPlacement.Subset (Fin N) k) :
    (Fintype.card (S.val × Fin (N.choose k * h)) : ℝ) / side N k h = (k : ℝ) / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hFR : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, S.property,
    side, Nat.cast_mul]
  field_simp

theorem query_fraction_limit (k : ℕ) :
    Tendsto (fun N : ℕ => (k : ℝ) / N) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat _

/-- Fixed subset size, with arbitrary positive repetitions and word widths. -/
theorem helper_fraction_limit (k : ℕ) (h b : ℕ → ℕ)
    (hh : ∀ N, 0 < h N) (hb : ∀ N, 0 < b N) :
    Tendsto (fun N : ℕ => (helperBits N k (h N) (b N) : ℝ) / inputBits N k (h N) (b N))
      atTop (𝓝 (1 / (k + 1))) := by
  have ht : Tendsto (fun N : ℕ => (1 - (k : ℝ) / N) / (k + 1)) atTop
      (𝓝 (1 / (k + 1))) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (query_fraction_limit k)).div_const (k + 1 : ℝ)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k + 1)] with N hN
  have hn : 0 < N := by omega
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [helper_fraction hn (by omega) (hh N) (hb N)]
  field_simp

theorem mean_gap_limit {k : ℕ} (hk : 0 < k) (h b : ℕ → ℕ)
    (hh : ∀ N, 0 < h N) (hb : ∀ N, 0 < b N) :
    Tendsto (fun N : ℕ => meanGapArea N k (h N) (b N))
      atTop (𝓝 (1 / (k + 1))) := by
  have hz : Tendsto (fun N : ℕ => 1 / (2 * (N : ℝ))) atTop (𝓝 0) := by
    simpa only [div_div] using tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)
  have ht := (helper_fraction_limit k h b hh hb).add hz
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k] with N hN
  exact (gap_helper_calibration hk hN (hh N) (hb N)).symm

theorem calibration_limits {k : ℕ} (hk : 0 < k) (h b : ℕ → ℕ)
    (hh : ∀ N, 0 < h N) (hb : ∀ N, 0 < b N) :
    Tendsto (fun N : ℕ => (k : ℝ) / N) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => (helperBits N k (h N) (b N) : ℝ) / inputBits N k (h N) (b N))
      atTop (𝓝 (1 / (k + 1))) ∧
    Tendsto (fun N : ℕ => meanGapArea N k (h N) (b N)) atTop (𝓝 (1 / (k + 1))) :=
  ⟨query_fraction_limit k, helper_fraction_limit k h b hh hb, mean_gap_limit hk h b hh hb⟩

end
end SourceCovers.SubsetHelper
