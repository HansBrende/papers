import TapeStorageRates.MajorityFamily
import TapeStorageRates.RelabelPartition

/-! # Actual syndrome partition families at every degree cap -/

namespace TapeStorageRates

open Filter Finset DirectedRecovery

set_option autoImplicit false
noncomputable section

open Classical in
/-- One fixed full-cube partition at each length in a growing family. The
label bound is on its actual attained labels, not nominal output width. -/
structure BinaryPartitionFamily (Δ : ℕ) (ε : ℝ) where
  size : ℕ → ℕ
  size_pos : ∀ j, 0 < size j
  growing : Tendsto size atTop atTop
  Label : ℕ → Type
  recovery : (j : ℕ) → Fin (size j) → Finset (Fin (size j))
  encoder : (j : ℕ) → (Fin (size j) → Bool) → Label j
  indexCode : ∀ j, IsIndexCode (recovery j) (encoder j)
  label_count : ∀ j, ((univ.image (encoder j)).card : ℝ) ≤ (2 : ℝ)^(ε * size j)
  degree_le : ∀ j v, (pairedIncidenceGraph (recovery j)).degree v ≤ Δ
  paired_far : ∀ r : ℕ, ∀ᶠ j in atTop, ∀ q : Fin (size j),
    ¬ (pairedIncidenceGraph (recovery j)).edist (Sum.inl q) (Sum.inr q) ≤ r

namespace BinaryPartitionFamily

open Classical in
/-- Only coordinate names change; the encoder and every attained label are
preserved exactly. -/
def ofFiniteCoordinates (V Y : ℕ → Type) [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)]
    (N : (j : ℕ) → V j → Finset (V j)) (E : (j : ℕ) → (V j → Bool) → Y j)
    {Δ : ℕ} {ε : ℝ} (hpos : ∀ j, 0 < Fintype.card (V j))
    (hgrow : Tendsto (fun j => Fintype.card (V j)) atTop atTop)
    (hindex : ∀ j, IsIndexCode (N j) (E j))
    (hcount : ∀ j, ((univ.image (E j)).card : ℝ) ≤ (2 : ℝ)^(ε * Fintype.card (V j)))
    (hdegree : ∀ j v, (pairedIncidenceGraph (N j)).degree v ≤ Δ)
    (hfar : ∀ r : ℕ, ∀ᶠ j in atTop, ∀ q : V j,
      ¬ (pairedIncidenceGraph (N j)).edist (Sum.inl q) (Sum.inr q) ≤ r) :
    BinaryPartitionFamily Δ ε where
  size j := Fintype.card (V j)
  size_pos := hpos
  growing := hgrow
  Label := Y
  recovery j := relabelRelation (Fintype.equivFin (V j)) (N j)
  encoder j := relabelEncoder (Fintype.equivFin (V j)) (E j)
  indexCode j := relabel_isIndexCode _ (hindex j)
  label_count j := by
    have he := congrArg (fun s : Finset (Y j) => (s.card : ℝ))
      (relabelEncoder_image (Fintype.equivFin (V j)) (E j))
    exact he.trans_le (hcount j)
  degree_le j v :=
    (degree_le_of_pairedEmbedding (relabelPorts (Fintype.equivFin (V j)) (N j)) v).trans
      (hdegree j _)
  paired_far r := by
    filter_upwards [hfar r] with j hj
    intro q hq
    exact hj ((Fintype.equivFin (V j)).symm q)
      ((AboveHalf.edist_map_le (relabelPorts (Fintype.equivFin (V j)) (N j)).toHom
        (Sum.inl q) (Sum.inr q)).trans hq)

/-- Increasing either budget preserves the entire partition family. -/
def weaken {δ Δ : ℕ} {ε η : ℝ} (F : BinaryPartitionFamily δ ε)
    (hΔ : δ ≤ Δ) (hε : ε ≤ η) : BinaryPartitionFamily Δ η :=
  { F with
    label_count := fun j => (F.label_count j).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)))
    degree_le := fun j v => (F.degree_le j v).trans hΔ }

open Classical in
/-- Any growing sequence of supported check matrices with a normalized rank
budget supplies full syndrome partitions. This adapter is independent of the
majority construction. -/
def ofMatrices {K : Type} [Field K] [Fintype K]
    (V : ℕ → Type) [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)]
    (H : (j : ℕ) → Matrix (V j) (V j) K) {Δ : ℕ} {δ : ℝ}
    (hpos : ∀ j, 0 < Fintype.card (V j))
    (hgrow : Tendsto (fun j => Fintype.card (V j)) atTop atTop)
    (hdiag : ∀ j v, H j v v ≠ 0)
    (hrank : ∀ j, ((H j).rank : ℝ) ≤ δ * Fintype.card (V j))
    (hdegree : ∀ j v, (pairedIncidenceGraph (matrixHelpers (H j))).degree v ≤ Δ)
    (hfar : ∀ r : ℕ, ∀ᶠ j in atTop, ∀ q : V j,
      ¬ (pairedIncidenceGraph (matrixHelpers (H j))).edist (Sum.inl q) (Sum.inr q) ≤ r) :
    BinaryPartitionFamily Δ (Real.logb 2 (Fintype.card K) * δ) := by
  let E (j : ℕ) := matrixSyndrome (H j) (bitInField K)
  have hindex (j : ℕ) : IsIndexCode (matrixHelpers (H j)) (E j) :=
    matrixSyndrome_isIndexCode (H j) (bitInField K) bitInField_injective (hdiag j)
  have hcount (j : ℕ) : ((univ.image (E j)).card : ℝ) ≤
      (2 : ℝ)^((Real.logb 2 (Fintype.card K) * δ) * Fintype.card (V j)) := by
    apply (matrixSyndrome_image_card_le_rpow (H j) (bitInField K) univ
      (b := 2) (by norm_num)).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hq : 0 ≤ Real.logb 2 (Fintype.card K) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)
    have h := mul_le_mul_of_nonneg_right (hrank j) hq
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  exact ofFiniteCoordinates V (fun j => V j → K) (fun j => matrixHelpers (H j)) E
    hpos hgrow hindex (fun j => by
      convert hcount j using 1
      congr 2
      ext z
      simp) hdegree hfar

end BinaryPartitionFamily

namespace OddGirthLinearSeed

variable {K : Type} [Field K] [Fintype K] {D : ℕ} {ρ : ℝ}
variable (S : OddGirthLinearSeed K D ρ)

include S

/-- The full syndrome partitions of the amplified matrices satisfy the
exponential label budget on the same coordinates and recovery relation. -/
theorem exists_majority_partition_family (h2 : (2 : K) ≠ 0)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) {m : ℕ} (hm : Odd m) :
    Nonempty (BinaryPartitionFamily ((D + 1)^m)
      (Real.logb 2 (Fintype.card K) * Real.exp (-LeanMachine.BinomialTail.decay ρ * m))) := by
  classical
  obtain ⟨j₀, hpos, hgrow, hdiag, hrank, hdegree, hfar⟩ :=
    S.exists_majority_matrix_tail h2 hρ hρ1 hm
  let V (j : ℕ) := S.majorityCoordinates m (j + j₀)
  let H (j : ℕ) : Matrix (V j) (V j) K := S.majorityCheck m (j + j₀)
  have hcardpos (j : ℕ) : 0 < Fintype.card (V j) := by
    simpa [V, majorityCoordinates] using pow_pos (hpos j) m
  exact ⟨BinaryPartitionFamily.ofMatrices V H
    (Δ := (D + 1)^m) (δ := Real.exp (-LeanMachine.BinomialTail.decay ρ * m)) hcardpos hgrow
    (fun j v => by rw [show H j v v = 1 from hdiag j v]; exact one_ne_zero)
    hrank (fun j v => (Nat.le_add_right _ 1).trans (hdegree j v)) hfar⟩

/-- At every cap above the explicit threshold, one actual family of full
partitions has the polynomial label budget. Its encoder is fixed before any
source subset or confidence parameter is selected. -/
theorem exists_partition_family_at_cap (h2 : (2 : K) ≠ 0)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) {Δ : ℕ} (hΔ : D + 1 ≤ Δ) :
    Nonempty (BinaryPartitionFamily Δ
      ((Real.logb 2 (Fintype.card K) * Real.exp (2 * LeanMachine.BinomialTail.decay ρ)) *
        (Δ : ℝ)^(-LeanMachine.BinomialTail.decay ρ / Real.log (D + 1 : ℕ)))) := by
  have hp : 1 < D + 1 := by
    have := S.degree_pos (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hρ)
    omega
  obtain ⟨m, _, hm, hmcap, _, he⟩ := LeanMachine.OddPowerChoice.exists_odd_power_and_decay
    hp hΔ (LeanMachine.BinomialTail.decay_pos hρ hρ1).le
  obtain ⟨F⟩ := S.exists_majority_partition_family h2 hρ hρ1 hm
  have hq : 0 ≤ Real.logb 2 (Fintype.card K) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)
  refine ⟨F.weaken hmcap ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hq

end OddGirthLinearSeed

end
end TapeStorageRates
