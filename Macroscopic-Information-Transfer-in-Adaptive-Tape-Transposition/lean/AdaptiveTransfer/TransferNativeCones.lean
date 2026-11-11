import AdaptiveTransfer.TransferNativeProjection
import AdaptiveTransfer.TransferNativeRoots
import AdaptiveTransfer.TransferInputGeometry
import AdaptiveTransfer.TransferInputCone

/-! Actual raw-cone transport. The guard and FIFO correspondence come from
the native aligned compiler. Interior roots need no final-output surcharge;
a separate terminal guard gives the all-root version. -/

namespace AdaptiveTransfer.TransferCones
open Finset Transpose Transpose.Tape MergeDepth BoundedNesting
open TapeStorageRates TapeStorageRates.Native
open AdaptiveTransfer.TransferClock AdaptiveTransfer.TransferFIFO
open AdaptiveTransfer.TransferRoots AdaptiveTransfer.TransferGuards
attribute [local instance] Classical.propDecidable

def guardCoefficient (k s : ℕ) : ℕ := 4 * (10 * s + 1) + k * (6 * s + 1) + 2 * s + 1

/-- Before charging terminal roots, every existing look-ahead ordinal has
the literal native cone inclusion. The raw length and output prefix length
are independent, and no correctness or shared source trace is assumed. -/
theorem native_cone_transport_interior {M : TM} {s t L P : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t)
    (hP : P ≤ outputCount M w t) (B : Finset ℕ) (hB : ∀ b ∈ B, b < t) :
    ∃ Γ : Finset ℕ, Γ.card ≤ guardCoefficient M.k s * B.card ∧
      (∀ u ∈ Γ, u < alignedTime s t) ∧
      ∀ i : Fin P, i.val + 2 * s < P → simulatorOrdinal M hs w t P i ∉ Γ →
        nativeInputCone (trace (machine M hs) w) L (alignedTime s t) Γ
            (simulatorOrdinal M hs w t P i) ⊆
          inputDilation (nativeInputCone (trace M w) L t B
            (sourceRoot M w t (i.val + 2 * s))) (3 * s) ∪ inputBoundary L (3 * s) := by
  obtain ⟨E, hE, hElive, hproject, hshadow⟩ := native_guarded_projection hs ht H B hB
  let Γ := E ∪ forwardGuard M hs w t P B
  refine ⟨Γ, ?_, ?_, ?_⟩
  · calc
      Γ.card ≤ E.card + (forwardGuard M hs w t P B).card := card_union_le _ _
      _ ≤ (4 * (10 * s + 1) + M.k * (6 * s + 1)) * B.card + B.card * (2 * s + 1) :=
        Nat.add_le_add hE (forwardGuard_card_le hs hP B)
      _ = guardCoefficient M.k s * B.card := by unfold guardCoefficient; ring
  · intro u hu
    rcases mem_union.mp hu with hu | hu
    · exact hElive u hu
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hu
      exact (actual_sourceRoot_le_clock hs ht H (i.isLt.trans_le hP)).1
  · intro i hfuture hroot p hp
    obtain ⟨ρ, hpath, hfree, hread⟩ := mem_nativeInputCone_iff_position.mp hp
    have hui : simulatorOrdinal M hs w t P i < alignedTime s t :=
      (actual_sourceRoot_le_clock hs ht H (i.isLt.trans_le hP)).1
    have hlast := (getLastD_le hpath).trans_lt hui
    have hgE : ∀ v ∈ simulatorOrdinal M hs w t P i :: ρ, v ∉ E := by
      intro v hv hvE
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hroot (mem_union_left _ hvE)
      · exact hfree v hv (mem_union_left _ hvE)
    have hroute := hproject _ ρ hui hpath hgE
    have hαq : sourceOrdinal M w t P i ≤ sourceClock s t (simulatorOrdinal M hs w t P i) :=
      (actual_sourceRoot_le_clock hs ht H (i.isLt.trans_le hP)).2
    have hqfuture : sourceClock s t (simulatorOrdinal M hs w t P i) <
        sourceRoot M w t (i.val + 2 * s) :=
      actual_clock_lt_future_root hs H (hfuture.trans_le hP)
    have hfutureT := (sourceRoot_counts M w (hfuture.trans_le hP)).1
    have hclosed := forwardGuard_interval_free hfuture
      (fun hg => hroot (mem_union_right _ hg))
    have hspine : Route (trace M w).work t B (sourceRoot M w t (i.val + 2 * s))
        (sourceClock s t (simulatorOrdinal M hs w t P i)) :=
      spine_route hqfuture.le hfutureT (fun r hlo hhi =>
        hclosed r (mem_Icc.mpr ⟨hαq.trans hlo, hhi⟩))
    have hh := hshadow _ hlast none
    change |(trace (machine M hs) w).input ((simulatorOrdinal M hs w t P i :: ρ).getLastD
        (simulatorOrdinal M hs w t P i)) - (trace M w).input
        (sourceClock s t ((simulatorOrdinal M hs w t P i :: ρ).getLastD
          (simulatorOrdinal M hs w t P i)))| ≤ 3 * (s : ℤ) at hh
    rw [hread] at hh
    apply shadow_in_dilation_or_boundary (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh)
    intro j hj
    obtain ⟨σ, hσ, hσlast, hσfree⟩ := hspine.trans hroute
    apply mem_nativeInputCone_iff_position.mpr
    refine ⟨σ, hσ, ?_, ?_⟩
    · exact fun v hv => hσfree v (List.mem_cons_of_mem _ hv)
    · rw [hσlast]
      exact hj

/-- Charging at most 2s terminal append roots makes the same cone inclusion
hold for every unguarded output ordinal. -/
theorem native_cone_transport {M : TM} {s t L P : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t)
    (hP : P ≤ outputCount M w t) (B : Finset ℕ) (hB : ∀ b ∈ B, b < t) :
    ∃ Γ : Finset ℕ, Γ.card ≤ guardCoefficient M.k s * B.card + 2 * s ∧
      (∀ u ∈ Γ, u < alignedTime s t) ∧
      ∀ i : Fin P, simulatorOrdinal M hs w t P i ∉ Γ →
        i.val + 2 * s < P ∧
        nativeInputCone (trace (machine M hs) w) L (alignedTime s t) Γ
            (simulatorOrdinal M hs w t P i) ⊆
          inputDilation (nativeInputCone (trace M w) L t B
            (sourceRoot M w t (i.val + 2 * s))) (3 * s) ∪ inputBoundary L (3 * s) := by
  obtain ⟨Γ₀, hΓ₀, hΓlive, hcone⟩ := native_cone_transport_interior (L := L) hs ht H hP B hB
  refine ⟨Γ₀ ∪ terminalGuard M hs w t P, ?_, ?_, ?_⟩
  · exact (card_union_le _ _).trans (Nat.add_le_add hΓ₀ (terminalGuard_card_le M hs w t P))
  · intro u hu
    rcases mem_union.mp hu with hu | hu
    · exact hΓlive u hu
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hu
      exact (actual_sourceRoot_le_clock hs ht H (i.isLt.trans_le hP)).1
  · intro i hi
    have htail : simulatorOrdinal M hs w t P i ∉ terminalGuard M hs w t P :=
      fun hg => hi (mem_union_right _ hg)
    have hfuture := future_defined_of_not_terminal htail
    refine ⟨hfuture, fun p hp => hcone i hfuture (fun hg => hi (mem_union_left _ hg)) ?_⟩
    obtain ⟨ρ, hpath, hfree, hread⟩ := mem_nativeInputCone.mp hp
    exact mem_nativeInputCone.mpr ⟨ρ, hpath,
      fun v hv hg => hfree v hv (mem_union_left _ hg), hread⟩

end AdaptiveTransfer.TransferCones
