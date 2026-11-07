import TapeStorageRates.MajorityPartitions
import TapeStorageRates.AllLengthPartitions

/-! # The seed supplies common partitions at every sufficiently large length -/

namespace TapeStorageRates

open Filter Finset DirectedRecovery MotionDepthCodes
set_option autoImplicit false
noncomputable section

open Classical in
/-- The complete all-length interface: original coordinates, one fixed
encoder, all source subsets and confidence levels, bounded degrees and
diverging minimum paired distance. No tape realization is included. -/
def AllLengthPartitionTarget (Δ : ℕ) (ε : ℝ) : Prop :=
  ∃ (Y : ℕ → Type) (N : (M : ℕ) → Fin M → Finset (Fin M))
    (f : (M : ℕ) → (Fin M → Bool) → Y M),
    (∀ M, IsIndexCode (N M) (f M)) ∧
    (∀ M (G : Finset (Fin M → Bool)) z,
      IsStorageCode (N M) (G.filter fun x => f M x = z)) ∧
    (∀ M v, (pairedIncidenceGraph (N M)).degree v ≤ Δ) ∧
    (∀ r : ℕ, ∀ᶠ M in atTop, ∀ q,
      ¬ (pairedIncidenceGraph (N M)).edist (Sum.inl q) (Sum.inr q) ≤ r) ∧
    ∀ᶠ M : ℕ in atTop,
      ((univ.image (f M)).card : ℝ) ≤ (2 : ℝ) ^ (ε * M + Real.sqrt M) ∧
      ∀ G : Finset (Fin M → Bool), G.Nonempty → ∀ u : ℝ,
        ((G.filter fun x => Real.logb 2 (G.filter fun y => f M y = f M x).card / M <
          Real.logb 2 G.card / M - (ε + Real.sqrt M / M) - u).card : ℝ) / G.card ≤
            (2 : ℝ) ^ (-u * M)

/-- Repetition converts a tower partition into the full all-length target,
with the explicit square-root overhead and the same incidence cap. -/
theorem BinaryPartitionFamily.all_lengths {Δ : ℕ} {ε : ℝ}
    (F : BinaryPartitionFamily Δ ε) (hε : 0 ≤ ε) : AllLengthPartitionTarget Δ ε := by
  classical
  refine ⟨AllLengthPartitions.Labels F.size F.Label,
    AllLengthPartitions.relation F.recovery, AllLengthPartitions.encoder F.encoder,
    AllLengthPartitions.isIndexCode F.recovery F.encoder F.indexCode,
    ?_,
    AllLengthPartitions.degree_le F.recovery F.degree_le,
    AllLengthPartitions.paired_far F.size_pos F.recovery F.paired_far, ?_⟩
  · intro M G z
    simpa only [IsStorageCode, mem_filter] using
      AllLengthPartitions.fibre_storage F.recovery F.encoder F.indexCode M G z
  · filter_upwards
      [AllLengthPartitions.encoder_image_card_le_rpow F.size_pos F.encoder hε F.label_count,
       AllLengthPartitions.rate_tail F.size_pos F.encoder hε F.label_count] with M hcount htail
    constructor
    · convert hcount using 1
      congr 2
      ext z
      simp
    · intro G hG u
      convert htail G hG u using 1
      congr 10
      funext x
      congr 10

namespace OddGirthLinearSeed

variable {K : Type} [Field K] [Fintype K] {D : ℕ} {ρ : ℝ}
variable (S : OddGirthLinearSeed K D ρ)

include S

/-- The all-length partitions are built from the actual amplified seed
matrices, with the same polynomial degree error as the tower construction. -/
theorem all_length_partitions (h2 : (2 : K) ≠ 0)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) {Δ : ℕ} (hΔ : D + 1 ≤ Δ) :
    AllLengthPartitionTarget Δ
      ((Real.logb 2 (Fintype.card K) * Real.exp (2 * LeanMachine.BinomialTail.decay ρ)) *
        (Δ : ℝ) ^ (-LeanMachine.BinomialTail.decay ρ / Real.log (D + 1 : ℕ))) := by
  obtain ⟨F⟩ := S.exists_partition_family_at_cap h2 hρ hρ1 hΔ
  apply F.all_lengths
  exact mul_nonneg
    (mul_nonneg (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast Fintype.card_pos : (1 : ℝ) ≤ Fintype.card K)) (Real.exp_pos _).le)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end OddGirthLinearSeed

end
end TapeStorageRates
