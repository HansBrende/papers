import LeanMachine.AnchoredCircularCover
import LeanMachine.PartitionEnergy

set_option autoImplicit false

/-!
# Anchored erosion of circular gap area

The geometry preserves the partition of uncovered elementary edges. The
partition-energy bound then charges the union of covered edges once, retaining
the quadratic saving. Real weights are lengths, not multiplicities or rounded
integer coordinates. Original anchors need not be retained in the target.
-/

namespace LeanMachine.AnchoredGapErosion

open Finset CyclicSelection WeightedCircularGap AnchoredCircularCover
open scoped BigOperators
noncomputable section

variable {κ : Type*}

/-- Normalized loss when a fraction `e` of the circumference is covered. -/
def penalty (e : ℝ) : ℝ := e - e ^ 2 / 2

theorem penalty_mono {e f : ℝ} (hef : e ≤ f) (hf : f ≤ 1) :
    penalty e ≤ penalty f := by
  unfold penalty
  nlinarith [mul_nonneg (sub_nonneg.mpr hef) (show 0 ≤ 2 - e - f by linarith)]

theorem penalty_le_self (e : ℝ) : penalty e ≤ e := by
  unfold penalty
  linarith [sq_nonneg e]

theorem penalty_nonneg {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) : 0 ≤ penalty e := by
  simpa [penalty] using penalty_mono he he1

theorem penalty_le_half (e : ℝ) : penalty e ≤ 1 / 2 := by
  unfold penalty
  nlinarith [sq_nonneg (1 - e)]

/-- Length of the arc union, with overlaps paid only once. -/
def coveredLength (N : ℕ) (w : ℕ → ℝ) (I : Finset κ) (start len : κ → ℕ) : ℝ :=
  ∑ e ∈ coveredEdges N I start len, w e

theorem coveredLength_nonneg {N : ℕ} {w : ℕ → ℝ} (hN : 0 < N)
    (hw : ∀ e < N, 0 ≤ w e) (I : Finset κ) (start len : κ → ℕ) :
    0 ≤ coveredLength N w I start len :=
  sum_nonneg fun _ he => hw _ (mem_range.mp (coveredEdges_subset hN I start len he))

theorem coveredLength_le {N : ℕ} {w : ℕ → ℝ} (hN : 0 < N)
    (hw : ∀ e < N, 0 ≤ w e) (I : Finset κ) (start len : κ → ℕ) :
    coveredLength N w I start len ≤ circumference N w :=
  sum_le_sum_of_subset_of_nonneg (coveredEdges_subset hN I start len)
    (fun _ he _ => hw _ (mem_range.mp he))

/-- A supplied upper bound on union length can exceed the circumference.
Clipping its normalized value at one preserves the quadratic saving. -/
theorem normalized_loss {L C E Q₀ Q : ℝ} (hL : 0 < L)
    (hCL : C ≤ L) (hCE : C ≤ E)
    (hQ : Q₀ - Q ≤ 2 * L * C - C ^ 2) :
    Q₀ / (2 * L ^ 2) - penalty (min (E / L) 1) ≤ Q / (2 * L ^ 2) := by
  have hden : 0 < 2 * L ^ 2 := by positivity
  have he : C / L ≤ min (E / L) 1 :=
    le_min (div_le_div_of_nonneg_right hCE hL.le) ((div_le_one hL).mpr hCL)
  have hp := penalty_mono he (min_le_right (E / L) 1)
  have hdiv := (div_le_div_iff_of_pos_right hden).mpr hQ
  have hid : (2 * L * C - C ^ 2) / (2 * L ^ 2) = penalty (C / L) := by
    unfold penalty
    field_simp
  rw [hid, sub_div] at hdiv
  linarith

section Cover

variable {N : ℕ} {S₀ S : Finset ℕ}
  (hS₀ : S₀.Nonempty) (hS₀N : S₀ ⊆ range N)
  (hS : S.Nonempty) (hSN : S ⊆ range N)
  (I : Finset κ) (start len : κ → ℕ)
  (hstart : ∀ i ∈ I, start i < N) (hlen : ∀ i ∈ I, len i ≤ N)
  (hanchor : ∀ i ∈ I, ∃ q ∈ S₀, q ∈ arc N (start i) (len i + 1))
  (hcover : S ⊆ S₀ ∪ coveredVertices N I start len)
  {w : ℕ → ℝ} (hw : ∀ e < N, 0 ≤ w e)

include hS₀N hSN hstart hlen hanchor hcover hw

/-- Actual gap energies obey the sharper union-length loss. -/
theorem energy_loss_le :
    WeightedCircularGap.energy N S₀ hS₀ w - WeightedCircularGap.energy N S hS w ≤
      2 * circumference N w * coveredLength N w I start len -
        coveredLength N w I start len ^ 2 := by
  rw [energy_eq_partitionEnergy hS₀ hS₀N, energy_eq_partitionEnergy hS hSN]
  have h := PartitionEnergy.energy_loss_le_paid_mass (range N) (coveredEdges N I start len)
    w (edgeLabel N S₀ hS₀) (edgeLabel N S hS) (fun e he => hw e (mem_range.mp he))
    (uncovered_pair_labels hS₀ hS₀N hS hSN I start len hstart hlen hanchor hcover)
  simpa only [inter_eq_right.mpr (coveredEdges_subset (cycle_pos hS₀ hS₀N) I start len),
    circumference, coveredLength] using h

/-- Full anchored-erosion theorem for arbitrary real elementary lengths. -/
theorem area_lower_bound (hL : 0 < circumference N w) {E : ℝ}
    (hE : coveredLength N w I start len ≤ E) :
    area N S₀ hS₀ w - penalty (min (E / circumference N w) 1) ≤ area N S hS w := by
  exact normalized_loss hL (coveredLength_le (cycle_pos hS₀ hS₀N) hw I start len) hE
    (energy_loss_le hS₀ hS₀N hS hSN I start len hstart hlen hanchor hcover hw)

/-- The original linear loss follows directly from the stronger theorem. -/
theorem area_lower_bound_linear (hL : 0 < circumference N w) {E : ℝ}
    (hE : coveredLength N w I start len ≤ E) :
    area N S₀ hS₀ w - E / circumference N w ≤ area N S hS w := by
  have h := area_lower_bound hS₀ hS₀N hS hSN I start len hstart hlen hanchor hcover hw hL hE
  have hp := (penalty_le_self (min (E / circumference N w) 1)).trans (min_le_left _ _)
  linarith

end Cover
end
end LeanMachine.AnchoredGapErosion
