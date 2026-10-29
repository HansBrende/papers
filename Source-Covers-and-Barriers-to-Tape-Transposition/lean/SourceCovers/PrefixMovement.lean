import SourceCovers.ContinuationMovement
import SourceCovers.PrefixErrorLimit
import LeanMachine.BoundedLiminf

set_option autoImplicit false

/-! Actual movement and its quadratic loss, averaged over admissible phases
and output columns of the original finite prefixes. -/

namespace SourceCovers.AdmissibleGeometry

open Classical Finset LeanMachine
open scoped BigOperators
noncomputable section

variable {c β : ℝ} {N : ℕ} (G : AdmissibleGeometry c β N 2) (O : SortedCore G.core)

/-- `φ = id` gives mean normalized movement; the clipped quadratic penalty
gives the sharper loss used in the finite deficit. -/
def prefixMeanMovement (J R M : ℕ) (hM : 2 ≤ M) (φ : ℝ → ℝ) : ℝ :=
  𝔼 ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M,
    𝔼 j ∈ range G.d, φ (phaseMovement (G.core_coloring.mono (O.selectedPrefix_subset J))
      hM G.exceptions G.x G.inputLength ρ (columnFirst G.t (G.d * G.b) j))

theorem prefixMeanMovement_mono (J R M : ℕ) (hM : 2 ≤ M) {φ ψ : ℝ → ℝ}
    (hφψ : ∀ z ≥ 0, φ z ≤ ψ z) :
    G.prefixMeanMovement O J R M hM φ ≤ G.prefixMeanMovement O J R M hM ψ := by
  exact expect_le_expect fun _ _ => expect_le_expect fun _ _ =>
    hφψ _ (phaseMovement_nonneg ..)

theorem prefixMeanMovement_bounds {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    0 ≤ G.prefixMeanMovement O J R M hM id ∧
      G.prefixMeanMovement O J R M hM id ≤ (bankCost M 1 : ℝ) * c := by
  have hA : (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M).Nonempty :=
    card_pos.mp ((Nat.sub_pos_of_lt hRM).trans_le
      (protected_phase_average _ _ (O.subprefix_card_le J R) hRM).1)
  constructor
  · exact expect_nonneg fun _ _ => expect_nonneg fun _ _ => phaseMovement_nonneg ..
  · apply expect_le hA
    intro ρ _
    apply expect_le (nonempty_range_iff.mpr G.hd.ne')
    intro j hj
    have ht := G.append_lt _ ((column_indices G.hd G.hb (mem_range.mp hj)).1.trans_lt
      (column_indices G.hd G.hb (mem_range.mp hj)).2)
    have h := phaseMovement_le (G.core_coloring.mono (O.selectedPrefix_subset J))
      hM G.exceptions G.x (L := G.inputLength) (ρ := ρ) ht G.raw_step
    apply h.trans
    apply (div_le_iff₀ (by exact_mod_cast G.inputLength_pos : (0 : ℝ) < G.inputLength)).mpr
    have hT : ((G.T - 1 : ℕ) : ℝ) ≤ G.T := by exact_mod_cast Nat.sub_le G.T 1
    have ht' : ((G.T - 1 : ℕ) : ℝ) ≤ c * G.inputLength := hT.trans (by
      simpa only [inputLength, Nat.cast_mul] using G.runtime)
    nlinarith [mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg (bankCost M 1))]

theorem prefixMeanPenalty_bounds {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    0 ≤ G.prefixMeanMovement O J R M hM (fun z => AnchoredGapErosion.penalty (min z 1)) ∧
      G.prefixMeanMovement O J R M hM (fun z => AnchoredGapErosion.penalty (min z 1)) ≤ 1 / 2 := by
  have hA : (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M).Nonempty :=
    card_pos.mp ((Nat.sub_pos_of_lt hRM).trans_le
      (protected_phase_average _ _ (O.subprefix_card_le J R) hRM).1)
  exact ⟨expect_nonneg fun _ _ => expect_nonneg fun _ _ =>
      AnchoredGapErosion.penalty_nonneg (le_min (phaseMovement_nonneg ..) (by norm_num))
        (min_le_right _ _),
    expect_le hA fun _ _ => expect_le (nonempty_range_iff.mpr G.hd.ne') fun _ _ =>
      AnchoredGapErosion.penalty_le_half _⟩

/-- The same paid transcript and residual error as in the original prefix
bound, with the one-cluster complete-movement credit. -/
theorem prefix_movement_deficit {K R J M w a : ℕ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M) (hw : 0 < w)
    (ha0 : G.a0 ≤ a) (ha : c * G.inputLength / (J + 1) ≤ (a : ℝ)) :
    max (1 - ∑ i ∈ Ico K J, O.variationProfile G.x G.inputLength i) 0 ^ 2 /
        (4 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
      G.prefixMeanMovement O J R M hM (fun z => AnchoredGapErosion.penalty (min z 1)) ≤
      G.relativeDeficit + G.prefixError O J R M w a := by
  let A := admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M
  let α := ∑ i ∈ Ico K J, O.variationProfile G.x G.inputLength i
  let C := max (1 - α) 0 ^ 2 / (4 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4))
  let move := fun ρ j => phaseMovement (G.core_coloring.mono (O.selectedPrefix_subset J))
    hM G.exceptions G.x G.inputLength ρ (columnFirst G.t (G.d * G.b) j)
  have hV := G.prefix_variation_le O hKJ
  have hτ := G.prefix_nonleaf_mass_le O hRJ
  have hpoint : ∀ ρ (hρ : ρ ∈ A), ∀ j < G.d,
      let S := rawBankValues (exactSourceBank (ρ := ρ)
        (G.core_coloring.mono (O.selectedPrefix_subset J)) hM G.exceptions) G.x
        (columnFirst G.t (G.d * G.b) j)
      C - AnchoredGapErosion.penalty (min (move ρ j) 1) ≤
        GapErosion.pointArea (range S.card) (CyclicSelection.gap G.inputLength S
          ⟨_, exactSourceBank_raw_root _ hM (admissiblePhase_lt hρ) G.exceptions G.x _⟩)
          G.inputLength := by
    intro ρ hρ j hj
    exact phaseMovement_gap _ hM (admissiblePhase_lt hρ) G.exceptions G.exceptions_card G.x
      (G.append_lt _ ((column_indices G.hd G.hb hj).1.trans_lt (column_indices G.hd G.hb hj).2))
      (fun u hu => G.raw_range u (by omega)) (O.subprefix J K) (O.subprefix_card_le J K) hV _
  have hp := paid_deficit_of_gap_credit (J := J) (G.core_coloring.mono (O.selectedPrefix_subset J))
    hM G.exceptions (O.subprefix J R)
    (by rw [O.selectedPrefix_card]; exact min_le_left _ _) G.exceptions_card
    (O.subprefix_card_le J R) hRM G.work_walk G.full_coloring (G.prefix_outside_small O ha0 ha)
    G.x G.t G.hd G.hb hw G.append_strict (fun z hz => by have := G.append_lt z hz; omega)
    G.raw_range G.raw_step G.C G.correct_nonempty G.record G.output G.capacity
    G.locally_determined G.correct hτ (fun ρ j => C - AnchoredGapErosion.penalty (min (move ρ j) 1))
    hpoint
  have hA : A.Nonempty := card_pos.mp ((Nat.sub_pos_of_lt hRM).trans_le
    (protected_phase_average _ _ (O.subprefix_card_le J R) hRM).1)
  have he : (∑ ρ ∈ A, ∑ j ∈ range G.d,
      (C - AnchoredGapErosion.penalty (min (move ρ j) 1))) / (A.card * G.d) =
      C - G.prefixMeanMovement O J R M hM (fun z => AnchoredGapErosion.penalty (min z 1)) := by
    have h : (𝔼 ρ ∈ A, 𝔼 j ∈ range G.d,
        (C - AnchoredGapErosion.penalty (min (move ρ j) 1))) =
        C - G.prefixMeanMovement O J R M hM (fun z => AnchoredGapErosion.penalty (min z 1)) := by
      simp only [expect_sub_distrib, expect_const (nonempty_range_iff.mpr G.hd.ne'), expect_const hA]
      rfl
    simpa only [expect_eq_sum_div_card, card_range, ← sum_div, div_div, mul_comm] using h
  rw [he] at hp
  have hp' : G.relativeDeficit ≥ C -
      G.prefixMeanMovement O J R M hM (fun z => AnchoredGapErosion.penalty (min z 1)) -
      G.prefixError O J R M w a := by
    simpa only [relativeDeficit, deficit, inputLength, prefixError, Nat.cast_mul] using hp
  linarith only [hp']

end
end SourceCovers.AdmissibleGeometry
