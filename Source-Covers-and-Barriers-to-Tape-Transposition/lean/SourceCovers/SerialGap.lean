import SourceCovers.SerialExactCover
import LeanMachine.CyclicGapUpper

set_option autoImplicit false

/-! Circular mesh bounds for the physical grid and the complete ordinary
raw orbit. They also hold for every set between these two raw sets. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset LeanMachine LeanMachine.CyclicSelection
noncomputable section

variable (P : Parameters)

theorem physicalGrid_nonempty : P.physicalGrid.Nonempty := ⟨0, mem_insert_self _ _⟩

theorem physicalGrid_subset_completeRaw : P.physicalGrid ⊆ P.completeRaw := by
  intro a ha
  rcases mem_insert.mp ha with rfl | ha
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (image_subset_image (erase_subset _ _) ha)

theorem completeRaw_subset_range : P.completeRaw ⊆ range P.length := by
  intro a ha
  rcases mem_insert.mp ha with rfl | ha
  · exact mem_range.mpr P.length_pos
  · obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    exact mem_range.mpr (P.coverTarget_bounds i).2

theorem coverTarget_mem_physicalGrid {i : Fin P.targets} (hi : i ≠ 0) :
    P.coverTarget i ∈ P.physicalGrid :=
  mem_insert_of_mem (mem_image_of_mem _ (mem_erase.mpr ⟨hi, mem_univ _⟩))

theorem mesh_pos : 0 < P.length ⌈/⌉ P.targets := by
  have hc : P.length ≤ P.targets * (P.length ⌈/⌉ P.targets) := le_smul_ceilDiv P.targets_pos
  have := P.length_pos
  by_contra hn
  have hz : P.length ⌈/⌉ P.targets = 0 := by omega
  rw [hz, Nat.mul_zero] at hc
  omega

theorem physical_next_zero :
    ∃ a ∈ P.physicalGrid, 0 < forward P.length 0 a ∧
      forward P.length 0 a ≤ P.length ⌈/⌉ P.targets := by
  have hQ : 1 < P.targets := by
    have hm : 3 ≤ P.m - 1 := by have := P.hm; omega
    unfold targets
    nlinarith
  let i : Fin P.targets := ⟨P.targets - 1, by omega⟩
  have hi : i ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change P.targets - 1 = 0 at hv
    omega
  have hij : i.val + 1 = P.targets := by dsimp only [i]; omega
  have hs := floor_step_le_ceilDiv P.length P.targets i.val P.targets_pos
  rw [hij] at hs
  have hdiv : P.targets * P.length / P.targets = P.length :=
    Nat.mul_div_cancel_left _ P.targets_pos
  rw [hdiv] at hs
  refine ⟨P.coverTarget i, P.coverTarget_mem_physicalGrid hi, ?_, ?_⟩
  · simpa [forward] using (P.coverTarget_bounds i).1
  · simp only [forward_of_le (Nat.zero_le _), Nat.sub_zero, coverTarget, ite_eq_right hi]
    omega

theorem physical_next_target (i : Fin P.targets) :
    ∃ a ∈ P.physicalGrid, 0 < forward P.length (P.coverTarget i) a ∧
      forward P.length (P.coverTarget i) a ≤ P.length ⌈/⌉ P.targets := by
  have hb := P.coverTarget_bounds i
  have hf := P.gridFloor_lt i
  by_cases hi : i = 0
  · refine ⟨0, mem_insert_self _ _, ?_, ?_⟩
    all_goals rw [forward_of_gt hb.1]
    all_goals simp only [coverTarget, ite_eq_left hi, Nat.add_zero]
    · have := P.length_pos
      omega
    · have := P.mesh_pos
      omega
  · by_cases hone : i.val = 1
    · have hs := floor_step_le_ceilDiv P.length P.targets 0 P.targets_pos
      simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.zero_div] at hs
      refine ⟨0, mem_insert_self _ _, ?_, ?_⟩
      all_goals rw [forward_of_gt hb.1]
      all_goals simp only [coverTarget, ite_eq_right hi, hone, Nat.one_mul, Nat.add_zero]
      · have hg := P.gridFloor_large hi
        rw [hone, Nat.one_mul] at hg
        rw [hone, Nat.one_mul] at hf
        omega
      · rw [hone, Nat.one_mul] at hf
        omega
    · have hip : 1 < i.val := by have := Fin.pos_iff_ne_zero.mpr hi; omega
      let j : Fin P.targets := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hj : j ≠ 0 := by
        intro he
        have hv := congrArg Fin.val he
        change i.val - 1 = 0 at hv
        omega
      have hji : j.val + 1 = i.val := by dsimp only [j]; omega
      have hlt : j < i := by change i.val - 1 < i.val; omega
      have hfloor := P.sparseDeparture_strictMono hlt
      dsimp only [sparseDeparture] at hfloor
      have hfj := P.gridFloor_lt j
      have hct : P.coverTarget i < P.coverTarget j := by
        simp only [coverTarget, ite_eq_right hi, ite_eq_right hj]
        omega
      have hs := floor_step_le_ceilDiv P.length P.targets j.val P.targets_pos
      rw [hji] at hs
      refine ⟨P.coverTarget j, P.coverTarget_mem_physicalGrid hj, ?_, ?_⟩
      · rw [forward_of_le hct.le]
        omega
      · rw [forward_of_le hct.le]
        simp only [coverTarget, ite_eq_right hi, ite_eq_right hj]
        omega

/-- Every complete-orbit source has a distinct clockwise physical-grid
successor within one mesh; no sorted-point computation is needed. -/
theorem serial_next {a : ℕ} (ha : a ∈ P.completeRaw) :
    ∃ b ∈ P.physicalGrid, 0 < forward P.length a b ∧
      forward P.length a b ≤ P.length ⌈/⌉ P.targets := by
  rcases mem_insert.mp ha with rfl | ha
  · exact P.physical_next_zero
  · obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    exact P.physical_next_target i

theorem serial_gap_le {S : Finset ℕ} (hRS : P.physicalGrid ⊆ S)
    (hSC : S ⊆ P.completeRaw) {i : ℕ} (hi : i < S.card) :
    gap P.length S (P.physicalGrid_nonempty.mono hRS) i ≤ P.length ⌈/⌉ P.targets := by
  apply gap_le_of_next _ (hSC.trans P.completeRaw_subset_range) ?_ hi
  intro a ha
  obtain ⟨b, hb, hp, hd⟩ := P.serial_next (hSC ha)
  exact ⟨b, hRS hb, hp, hd⟩

theorem serial_area_le {S : Finset ℕ} (hRS : P.physicalGrid ⊆ S)
    (hSC : S ⊆ P.completeRaw) :
    GapErosion.pointArea (range S.card)
      (gap P.length S (P.physicalGrid_nonempty.mono hRS)) P.length ≤
        1 / (2 * (P.targets : ℝ)) + 1 / (2 * (P.length : ℝ)) := by
  have hL : (0 : ℝ) < P.length := by exact_mod_cast P.length_pos
  have hQ : (0 : ℝ) < P.targets := by exact_mod_cast P.targets_pos
  calc
    _ ≤ ((P.length ⌈/⌉ P.targets : ℕ) : ℝ) / (2 * P.length) :=
      pointArea_le_of_gap_le P.length_pos _ (hSC.trans P.completeRaw_subset_range)
        (fun _ hi => P.serial_gap_le hRS hSC hi)
    _ ≤ ((P.length : ℝ) / P.targets + 1) / (2 * P.length) :=
      div_le_div_of_nonneg_right (ceilDiv_cast_le_div_add_one _ _ P.targets_pos) (by positivity)
    _ = _ := by field_simp

end
end SourceCovers.SerialGeometry.Parameters
