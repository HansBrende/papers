import SourceCovers.SerialOrbit

set_option autoImplicit false

/-! Both cover equalities for the actual output root and original paid
phase. The raw target is now the complete ordinary joint orbit. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset LeanMachine
open scoped ENNReal
noncomputable section

variable (P : Parameters)

def jointTimes : Finset ℕ := (range P.horizon).filter (fun t => t ∈ P.jointOrbit)

theorem jointTimes_eq : (P.jointTimes : Set ℕ) = P.jointOrbit := by
  ext t
  simp only [jointTimes, mem_coe, mem_filter, mem_range, and_iff_right_iff_imp]
  exact fun ht => (shadowOrbit_le ht).trans_lt P.root_lt_horizon

def jointRaw : Finset ℕ := P.jointTimes.image P.raw

theorem jointRaw_finset_eq : P.jointRaw = P.completeRaw := by
  apply Finset.coe_injective
  rw [jointRaw, coe_image, P.jointTimes_eq, P.jointRaw_eq]

/-- Every computation time is an allowed covering seed. -/
theorem serial_joint_cover_exact :
    fractionalCoreCover P.serialPhase P.raw P.jointRaw = (P.targets : ℝ≥0∞) := by
  rw [P.jointRaw_finset_eq]
  exact P.serialPhase_cover

/-- Restricting seeds to the original joint orbit leaves the optimum unchanged. -/
theorem serial_joint_cover_restricted :
    FractionalCover.number P.jointRaw
      (fun u : P.jointTimes => P.raw '' shadowOrbit P.retainedCore u.val) =
        (P.targets : ℝ≥0∞) := by
  rw [P.jointRaw_finset_eq]
  exact P.serial_cover_number_restrict 5 P.heads_early _ P.retainedCore
    P.earlyFamily_retained (fun _ h => P.core_start_separated (P.retainedCore_subset h))
    P.jointTimes (fun i => by
      change P.coverSeed i ∈ (P.jointTimes : Set ℕ)
      rw [P.jointTimes_eq]
      exact P.coverSeed_joint i)

end
end SourceCovers.SerialGeometry.Parameters
