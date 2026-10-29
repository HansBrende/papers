import SourceCovers.SerialGap

set_option autoImplicit false

/-! The complete native serial-exception counterexample. This certificate
bundles properties of the constructed walks, original actual families,
original paid phase, and complete physical and ordinary source relations. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting LeanMachine LeanMachine.CyclicSelection
open scoped ENNReal
noncomputable section

variable (P : Parameters)

theorem jointRaw_nonempty : P.jointRaw.Nonempty := by
  rw [P.jointRaw_finset_eq]
  exact P.physicalGrid_nonempty.mono P.physicalGrid_subset_completeRaw

theorem jointRaw_area_le :
    GapErosion.pointArea (range P.jointRaw.card)
      (gap P.length P.jointRaw P.jointRaw_nonempty) P.length ≤
        1 / (2 * (P.targets : ℝ)) + 1 / (2 * (P.length : ℝ)) := by
  exact P.serial_area_le
    (by rw [P.jointRaw_finset_eq]; exact P.physicalGrid_subset_completeRaw)
    (by rw [P.jointRaw_finset_eq])

/-- The full claim of the serial-cover proposition, for every admissible
pair of parameters. No geometric, payment, or orbit certificate is assumed. -/
structure SerialCertificate : Prop where
  dimension : P.dimension = 16 * P.m
  input_length : P.length = P.dimension ^ 2 * P.b
  time_bound : P.horizon < 13 * P.length
  work_walks : ∀ q : Fin 8, IsWalk (P.heads q)
  work_initial : ∀ q : Fin 8, P.heads q 0 = 0
  work_entries : ∀ (q : Fin 8) (c : ℤ) (T : ℕ), (entries (P.heads q) c T).card ≤ 3
  input_initial : P.raw 0 = 0
  input_steps : ∀ t, |(P.raw (t + 1) : ℤ) - P.raw t| ≤ 1
  input_range : ∀ t, P.raw t < P.length
  outputs_increasing : StrictMono P.output
  outputs_before_end : ∀ i < P.length, P.output i < P.horizon
  output_root : ∃ i : Fin P.length, P.root = P.output i
  complete_partition : P.coreFamilies ∪ P.exceptionalFamilies = univ
  partition_disjoint : Disjoint P.coreFamilies P.exceptionalFamilies
  core_two_colors : HasSpanColoring P.coreFamilies 2
  two_exceptions : P.exceptionalFamilies.card = 2
  exceptional_spans : Disjoint P.olderFamily.edges P.newerFamily.edges
  original_phase : P.serialPhase = phaseSurvivors P.coreFamilies P.m 0
  original_payment : P.payment = initialPayment P.coreFamilies P.exceptionalFamilies P.m 0
  exact_raw_orbit : (P.jointRaw : Set ℕ) = P.raw '' shadowOrbit P.jointFamilies P.root
  arbitrary_seed_cover : fractionalCoreCover P.serialPhase P.raw P.jointRaw = (P.targets : ℝ≥0∞)
  joint_seed_cover : FractionalCover.number P.jointRaw
    (fun u : P.jointTimes => P.raw '' shadowOrbit P.retainedCore u.val) = (P.targets : ℝ≥0∞)
  physical_card : P.physicalGrid.card = P.targets
  physical_sources : (P.physicalGrid : Set ℕ) ⊆ P.physicalCone
  physical_gaps : ∀ i < P.physicalGrid.card,
    gap P.length P.physicalGrid P.physicalGrid_nonempty i ≤ P.length ⌈/⌉ P.targets
  ordinary_area : GapErosion.pointArea (range P.jointRaw.card)
    (gap P.length P.jointRaw P.jointRaw_nonempty) P.length ≤
      1 / (2 * (P.targets : ℝ)) + 1 / (2 * (P.length : ℝ))
  distinguished_core : P.earlyFamily ∈ P.coreFamilies
  zero_profiles : ∀ F ∈ P.coreFamilies, F ≠ P.earlyFamily →
    ∀ w : List (ActualFamily P.heads P.horizon), (∀ G ∈ w, G ∈ P.exceptionalFamilies) →
      ∀ t, F.start ≤ t ∧ t ≤ F.stop → P.raw (shadowEndpoint w t) = 0

/-- Eight explicit legal heads witness the entire proposition, with
Q=(m-1)^2 for every m≥4 and b≥1 encoded in `Parameters`. -/
theorem serial_quadratic_cover : P.SerialCertificate where
  dimension := P.dimension_eq
  input_length := P.length_eq_dimension_sq
  time_bound := P.horizon_lt
  work_walks := P.heads_isWalk
  work_initial := P.heads_zero
  work_entries := P.heads_entries
  input_initial := P.raw_zero
  input_steps := P.raw_step
  input_range := P.raw_range
  outputs_increasing := P.output_strictMono
  outputs_before_end := fun _ hi => P.output_lt hi
  output_root := P.root_is_output
  complete_partition := P.families_complete
  partition_disjoint := P.core_exceptional_disjoint
  core_two_colors := P.core_span_coloring
  two_exceptions := P.exceptionalFamilies_card
  exceptional_spans := P.exceptional_spans_disjoint
  original_phase := rfl
  original_payment := rfl
  exact_raw_orbit := by rw [jointRaw, coe_image, P.jointTimes_eq]; rfl
  arbitrary_seed_cover := P.serial_joint_cover_exact
  joint_seed_cover := P.serial_joint_cover_restricted
  physical_card := P.physicalGrid_card
  physical_sources := P.physicalGrid_subset_cone
  physical_gaps := fun _ hi =>
    P.serial_gap_le (Subset.refl P.physicalGrid) P.physicalGrid_subset_completeRaw hi
  ordinary_area := P.jointRaw_area_le
  distinguished_core := (P.mem_coreFamilies _).mpr (Or.inr (Or.inl rfl))
  zero_profiles := fun _ hF hne w hw _ ht => P.serial_exceptional_profile_zero hF hne w hw ht

end
end SourceCovers.SerialGeometry.Parameters
