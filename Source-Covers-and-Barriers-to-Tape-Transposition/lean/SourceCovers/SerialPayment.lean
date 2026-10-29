import SourceCovers.SerialPhase
import SourceCovers.PaidSourceGeometry

set_option autoImplicit false

/-! The paid set uses the existing initialPayment: all selected outer
lowers and all actual lower endpoints of the deleted core families. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting LeanMachine
noncomputable section

variable (P : Parameters)

def payment : Finset ℕ := initialPayment P.coreFamilies P.exceptionalFamilies P.m 0

theorem bankCore_lowers (c : Fin 2) (j : Fin P.bankCount) :
    familyLowers (P.bankCore c j) =
      Ico (P.bankBase c + j.val * P.width) (P.bankBase c + (j.val + 1) * P.width) := by
  unfold familyLowers
  change (P.bankFamily c j).hops.image (fun η => η.2.1) = _
  rw [bankFamily_hops, image_image]
  have he : P.bankBase c + (j.val + 1) * P.width =
      P.bankBase c + j.val * P.width + P.width := by ring
  rw [he]
  ext u
  simp only [mem_image, mem_univ, true_and, mem_Ico, Function.comp_apply]
  constructor
  · rintro ⟨a, rfl⟩
    have := a.isLt
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨⟨P.bankBase c + j.val * P.width + P.width - u - 1, by omega⟩, ?_⟩
    dsimp only
    omega

theorem mem_outerPayment (u : ℕ) :
    u ∈ outerPayment (P.coreFamilies ∪ P.exceptionalFamilies) ↔
      (∃ c : Fin 2, ∃ j : Fin P.bankCount, u = P.bankBase c + j.val * P.width) ∨
      u = 0 ∨ u = 2 * P.length ∨ u = 5 * P.length ∨ u = 7 * P.length := by
  constructor
  · intro hu
    obtain ⟨F, _, he⟩ := mem_image.mp hu
    rcases P.actualFamily_exhaustive F with ⟨c, j, rfl⟩ | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨c, j, he.symm.trans (P.bankFamily_start c j)⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (he.symm.trans P.newerFamily_start))))
    · exact Or.inr (Or.inl (he.symm.trans P.earlyFamily_start))
    · exact Or.inr (Or.inr (Or.inl (he.symm.trans P.olderFamily_start)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (he.symm.trans P.bridgeFamily_start))))
  · intro hu
    rw [outerPayment, P.families_complete]
    rcases hu with ⟨c, j, rfl⟩ | rfl | rfl | rfl | rfl
    · exact mem_image.mpr ⟨P.bankFamily c j, mem_univ _, P.bankFamily_start c j⟩
    · exact mem_image.mpr ⟨P.earlyFamily, mem_univ _, P.earlyFamily_start⟩
    · exact mem_image.mpr ⟨P.olderFamily, mem_univ _, P.olderFamily_start⟩
    · exact mem_image.mpr ⟨P.bridgeFamily, mem_univ _, P.bridgeFamily_start⟩
    · exact mem_image.mpr ⟨P.newerFamily, mem_univ _, P.newerFamily_start⟩

theorem mem_phasePayment_iff (u : ℕ) :
    u ∈ phasePayment P.coreFamilies P.m 0 ↔
      ∃ F : CoreFamily P.coreFamilies, F ∉ P.serialPhase ∧ u ∈ familyLowers F := by
  simp only [phasePayment, PeriodicPhases.payment, mem_biUnion, mem_filter,
    serialPhase, phaseSurvivors, mem_univ, true_and, not_or, not_not]

theorem mem_phasePayment (u : ℕ) :
    u ∈ phasePayment P.coreFamilies P.m 0 ↔
      ∃ c : Fin 2, ∃ j : Fin P.bankCount, 0 < j.val ∧ j.val % P.m = 0 ∧
        P.bankBase c + j.val * P.width ≤ u ∧
        u < P.bankBase c + (j.val + 1) * P.width := by
  rw [P.mem_phasePayment_iff]
  constructor
  · rintro ⟨F, hF, hu⟩
    rcases P.core_cases F with ⟨c, j, rfl⟩ | rfl | rfl
    · have hj := (P.bankCore_deleted_iff c j).mp hF
      rw [P.bankCore_lowers, mem_Ico] at hu
      exact ⟨c, j, hj.1, hj.2, hu⟩
    · exact False.elim (hF P.earlyCore_survives)
    · exact False.elim (hF P.bridgeCore_survives)
  · rintro ⟨c, j, hj, hm, hu⟩
    exact ⟨P.bankCore c j, (P.bankCore_deleted_iff c j).mpr ⟨hj, hm⟩,
      by rwa [P.bankCore_lowers, mem_Ico]⟩

theorem mem_payment (u : ℕ) : u ∈ P.payment ↔
    ((∃ c : Fin 2, ∃ j : Fin P.bankCount, u = P.bankBase c + j.val * P.width) ∨
      u = 0 ∨ u = 2 * P.length ∨ u = 5 * P.length ∨ u = 7 * P.length) ∨
    ∃ c : Fin 2, ∃ j : Fin P.bankCount, 0 < j.val ∧ j.val % P.m = 0 ∧
      P.bankBase c + j.val * P.width ≤ u ∧ u < P.bankBase c + (j.val + 1) * P.width := by
  rw [payment, initialPayment, mem_union, P.mem_outerPayment, P.mem_phasePayment]

/-- Away from the two bank ranges only the four listed outer lowers can
be paid. This suffices for the exceptional and early parts of each path. -/
theorem payment_location {u : ℕ} (hu : u ∈ P.payment) :
    (u = 0 ∨ u = 2 * P.length ∨ u = 5 * P.length ∨ u = 7 * P.length) ∨
      (4 * P.length ≤ u ∧ u < 5 * P.length) ∨
      (11 * P.length ≤ u ∧ u < 12 * P.length) := by
  rw [P.mem_payment] at hu
  rcases hu with (⟨c, j, rfl⟩ | hu) | ⟨c, j, _, _, hl, hh⟩
  · have hj := Nat.mul_lt_mul_of_pos_right j.isLt P.width_pos
    change j.val * P.width < P.length at hj
    fin_cases c
    · right; left
      change 4 * P.length ≤ 4 * P.length + j.val * P.width ∧
        4 * P.length + j.val * P.width < 5 * P.length
      omega
    · right; right
      change 11 * P.length ≤ 11 * P.length + j.val * P.width ∧
        11 * P.length + j.val * P.width < 12 * P.length
      omega
  · exact Or.inl hu
  · have hj := Nat.mul_le_mul_right P.width (show j.val + 1 ≤ P.bankCount by have := j.isLt; omega)
    change (j.val + 1) * P.width ≤ P.length at hj
    fin_cases c
    · right; left
      change 4 * P.length + j.val * P.width ≤ u at hl
      change u < 4 * P.length + (j.val + 1) * P.width at hh
      omega
    · right; right
      change 11 * P.length + j.val * P.width ≤ u at hl
      change u < 11 * P.length + (j.val + 1) * P.width at hh
      omega

theorem unpaid_outside_banks {u : ℕ}
    (h0 : u ≠ 0) (h2 : u ≠ 2 * P.length) (h5 : u ≠ 5 * P.length) (h7 : u ≠ 7 * P.length)
    (he : u < 4 * P.length ∨ 5 * P.length ≤ u)
    (hl : u < 11 * P.length ∨ 12 * P.length ≤ u) : u ∉ P.payment := by
  intro hu
  have hp := P.payment_location hu
  omega

end
end SourceCovers.SerialGeometry.Parameters
