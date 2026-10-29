import SourceCovers.SerialRanks

set_option autoImplicit false

/-! The original period-m, residue-zero phase, with original leaves
retained. No replacement rank or manually prescribed deletion is used. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting
open scoped ENNReal
noncomputable section

variable (P : Parameters)

/-- A zero-residue bank cannot be the last bank: its successor would
have residue one, whereas the bank count is a multiple of m. -/
theorem bank_zero_residue_interior {j : Fin P.bankCount} (hj : j.val % P.m = 0) :
    j.val + 1 < P.bankCount := by
  have hm : 1 < P.m := by have := P.hm; omega
  have hs : (j.val + 1) % P.m = 1 := by simp [Nat.add_mod, hj, Nat.mod_eq_of_lt hm]
  have hn : P.bankCount % P.m = 0 := by simp [bankCount]
  have hb := j.isLt
  by_contra h
  have he : j.val + 1 = P.bankCount := by omega
  rw [he, hn] at hs
  omega

def serialPhase : Finset (CoreFamily P.coreFamilies) := phaseSurvivors P.coreFamilies P.m 0

def retainedCore : Finset (ActualFamily P.heads P.horizon) := P.serialPhase.image Subtype.val

/-- This is the exact deletion criterion in the original phase system. -/
theorem bankCore_deleted_iff (c : Fin 2) (j : Fin P.bankCount) :
    P.bankCore c j ∉ P.serialPhase ↔ 0 < j.val ∧ j.val % P.m = 0 := by
  simp only [serialPhase, phaseSurvivors, mem_filter, mem_univ, true_and, not_or, not_not,
    coreNonleaves]
  constructor
  · rintro ⟨hn, hp⟩
    have hj := ((P.bankCore_nonleaf_iff c j).mp hn).1
    exact ⟨hj, by rwa [P.bankCore_phase_of_pos c j hj] at hp⟩
  · rintro ⟨hj, hp⟩
    exact ⟨(P.bankCore_nonleaf_iff c j).mpr ⟨hj, Or.inl (P.bank_zero_residue_interior hp)⟩,
      by rwa [P.bankCore_phase_of_pos c j hj]⟩

theorem bankCore_survives_iff (c : Fin 2) (j : Fin P.bankCount) :
    P.bankCore c j ∈ P.serialPhase ↔ j.val = 0 ∨ j.val % P.m ≠ 0 := by
  constructor
  · intro h
    by_cases hj : j.val = 0
    · exact Or.inl hj
    · exact Or.inr (fun hm => (P.bankCore_deleted_iff c j).mpr ⟨by omega, hm⟩ h)
  · intro h
    by_contra hn
    have he := (P.bankCore_deleted_iff c j).mp hn
    rcases h with h | h
    · omega
    · exact h he.2

theorem earlyCore_survives : P.earlyCore ∈ P.serialPhase := by
  simp only [serialPhase, phaseSurvivors, mem_filter, mem_univ, true_and]
  left
  simpa only [coreNonleaves, mem_filter, mem_univ, true_and] using P.earlyCore_not_nonleaf

theorem bridgeCore_survives : P.bridgeCore ∈ P.serialPhase := by
  simp only [serialPhase, phaseSurvivors, mem_filter, mem_univ, true_and]
  left
  simpa only [coreNonleaves, mem_filter, mem_univ, true_and] using P.bridgeCore_not_nonleaf

theorem mem_retainedCore (F : ActualFamily P.heads P.horizon) :
    F ∈ P.retainedCore ↔
      (∃ c : Fin 2, ∃ j : Fin P.bankCount,
        F = P.bankFamily c j ∧ (j.val = 0 ∨ j.val % P.m ≠ 0)) ∨
      F = P.earlyFamily ∨ F = P.bridgeFamily := by
  constructor
  · intro hF
    obtain ⟨G, hG, rfl⟩ := mem_image.mp hF
    rcases P.core_cases G with ⟨c, j, rfl⟩ | rfl | rfl
    · exact Or.inl ⟨c, j, rfl, (P.bankCore_survives_iff c j).mp hG⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (⟨c, j, rfl, hj⟩ | rfl | rfl)
    · exact mem_image.mpr ⟨P.bankCore c j, (P.bankCore_survives_iff c j).mpr hj, rfl⟩
    · exact mem_image.mpr ⟨P.earlyCore, P.earlyCore_survives, rfl⟩
    · exact mem_image.mpr ⟨P.bridgeCore, P.bridgeCore_survives, rfl⟩

theorem retainedCore_subset : P.retainedCore ⊆ P.coreFamilies := by
  intro F hF
  obtain ⟨G, _, rfl⟩ := mem_image.mp hF
  exact G.property

theorem earlyFamily_retained : P.earlyFamily ∈ P.retainedCore :=
  mem_image.mpr ⟨P.earlyCore, P.earlyCore_survives, rfl⟩

theorem bridgeFamily_retained : P.bridgeFamily ∈ P.retainedCore :=
  mem_image.mpr ⟨P.bridgeCore, P.bridgeCore_survives, rfl⟩

/-- The actual phase attains the exact cover for the prescribed target
set. Identifying that set with the joint orbit is a separate obligation. -/
theorem serialPhase_cover : fractionalCoreCover P.serialPhase P.raw P.completeRaw =
    (P.targets : ℝ≥0∞) :=
  P.retained_serial_fractional_core_cover P.serialPhase P.earlyFamily_retained

/-- A division-free description of the deleted indices: precisely the
seven positive multiples m, 2m, ..., 7m in each of the two copies. -/
theorem bankCore_deleted_multiples (c : Fin 2) (j : Fin P.bankCount) :
    P.bankCore c j ∉ P.serialPhase ↔
      ∃ a : ℕ, 1 ≤ a ∧ a ≤ 7 ∧ j.val = a * P.m := by
  rw [P.bankCore_deleted_iff]
  have hm : 0 < P.m := by have := P.hm; omega
  constructor
  · rintro ⟨hj, hmod⟩
    refine ⟨j.val / P.m, ?_, ?_, ?_⟩
    · by_contra h
      have hq : j.val / P.m = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge h)
      have he := Nat.mod_add_div j.val P.m
      rw [hmod, hq, Nat.mul_zero, Nat.zero_add] at he
      omega
    · have hi : j.val / P.m < 8 := (Nat.div_lt_iff_lt_mul hm).mpr (by
        simpa only [bankCount, Nat.mul_comm] using j.isLt)
      omega
    · have he := Nat.mod_add_div j.val P.m
      nlinarith
  · rintro ⟨a, ha, _, he⟩
    rw [he]
    exact ⟨Nat.mul_pos (by omega) hm, by simp⟩

end
end SourceCovers.SerialGeometry.Parameters
