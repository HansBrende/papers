import SourceCovers.SerialPartition
import SourceCovers.SerialCoverNumber

set_option autoImplicit false

/-! The actual family partition discharges the geometric premises of the
cover and zero-profile certificates. SerialOrbit separately identifies
the prescribed target set with a root's complete joint orbit. -/

namespace SourceCovers.SerialGeometry.Parameters

open Finset LeanMachine
open scoped ENNReal
noncomputable section

variable (P : Parameters)

theorem core_start_separated {F : ActualFamily P.heads P.horizon}
    (hF : F ∈ P.coreFamilies) : F = P.earlyFamily ∨ 3 * P.length ≤ F.start := by
  rw [mem_coreFamilies] at hF
  rcases hF with ⟨c, j, rfl⟩ | rfl | rfl
  · right
    have hs := (P.bankFamily_span_bounds c j).1
    unfold bankBase at hs
    split_ifs at hs <;> omega
  · exact Or.inl rfl
  · right
    rw [bridgeFamily_start]
    omega

theorem exceptional_start_separated {F : ActualFamily P.heads P.horizon}
    (hF : F ∈ P.exceptionalFamilies) : 2 * P.length ≤ F.start := by
  rw [mem_exceptionalFamilies] at hF
  rcases hF with rfl | rfl
  · rw [newerFamily_start]
    omega
  · exact P.olderFamily_start.ge

/-- The zero-profile assertion applies to every word, including the
empty word, on every nondistinguished original core span. -/
theorem serial_exceptional_profile_zero {F : ActualFamily P.heads P.horizon}
    (hF : F ∈ P.coreFamilies) (hne : F ≠ P.earlyFamily)
    (w : List (ActualFamily P.heads P.horizon))
    (hw : ∀ G ∈ w, G ∈ P.exceptionalFamilies) {t : ℕ}
    (ht : F.start ≤ t ∧ t ≤ F.stop) : P.raw (shadowEndpoint w t) = 0 := by
  have hs := (P.core_start_separated hF).resolve_left hne
  exact P.exceptional_profile_zero P.exceptionalFamilies
    (fun _ h => P.exceptional_start_separated h) F (by omega) w hw ht

/-- No further selection rule can reduce the exact cover of the
prescribed target set, as long as the early family is retained. -/
theorem retained_serial_cover (K : Finset (ActualFamily P.heads P.horizon))
    (hK : K ⊆ P.coreFamilies) (hH : P.earlyFamily ∈ K) :
    FractionalCover.number P.completeRaw (fun u : Fin P.horizon => P.raw '' shadowOrbit K u.val) =
      (P.targets : ℝ≥0∞) := by
  exact P.serial_cover_number_all 5 P.heads_early _ K hH
    (fun _ h => P.core_start_separated (hK h))

theorem retained_serial_fractional_core_cover (I : Finset (CoreFamily P.coreFamilies))
    (hH : P.earlyFamily ∈ I.image Subtype.val) :
    fractionalCoreCover I P.raw P.completeRaw = (P.targets : ℝ≥0∞) := by
  apply P.serial_fractional_core_cover 5 P.heads_early _ I hH
  intro F hF
  obtain ⟨G, _, rfl⟩ := mem_image.mp hF
  exact P.core_start_separated G.property

end
end SourceCovers.SerialGeometry.Parameters
