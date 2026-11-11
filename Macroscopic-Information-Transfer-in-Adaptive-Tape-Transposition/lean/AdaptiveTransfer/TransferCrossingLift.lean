import AdaptiveTransfer.TransferNativeProjection
import AdaptiveTransfer.TransferNativeRoots

/-! Finite cut assembly for the actual native simulator. The geometric
connector is isolated as an internal interface; the crossing specialization
constructs that connector and all additional guards from literal traces. -/

namespace AdaptiveTransfer.TransferCrossing
open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth NativeRelations
open TapeStorageRates TapeStorageRates.Native
open AdaptiveTransfer.TransferClock AdaptiveTransfer.TransferFIFO
open AdaptiveTransfer.TransferRoots AdaptiveTransfer.TransferGuards

/-- The exact coefficient of the original cut in crossing-target transport. -/
def crossingCutFactor (k s U H : ℕ) : ℕ :=
  4 * (10 * s + 1) + k * (6 * s + 1) +
    k * (6 * s + 3) * ((U - 1) / (4 * H + 2)) + (2 * s - 1)

/-- The canonical-label discard and the final activation's ordinal bill. -/
def crossingCutError (k s K₀ h : ℕ) : ℕ :=
  4 * k * K₀ ^ 2 * (2 * h + 6 * s + 3) + (2 * s - 1)

/-- Internal cut assembly. Only the target connector is abstract here;
clock, path projection, and delayed-root guards come from the actual native
compiler and the actual source execution. -/
theorem native_target_route_cut_lift_pos {M : TM} {s t P : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t)
    (hP : P ≤ outputCount M w t) (I : Finset (Fin P))
    (targets simulatorTargets extra B : Finset ℕ) (hB : ∀ b ∈ B, b < t)
    (hextra : ∀ v ∈ extra, v < alignedTime s t)
    (hconnect : ∀ v ∈ simulatorTargets, v ∉ extra →
      ∃ p ∈ targets, Route (trace M w).work t B (sourceClock s t v) p)
    (hcut : IsMengerVertexCut (trace M w).work t
      (I.image (sourceOrdinal M w t P)) targets B) :
    ∃ Γ : Finset ℕ,
      Γ.card ≤ (4 * (10 * s + 1) + M.k * (6 * s + 1)) * B.card +
        (B.card + 1) * (2 * s - 1) + extra.card ∧
      (∀ u ∈ Γ, u < alignedTime s t) ∧
      IsMengerVertexCut (trace (machine M hs) w).work (alignedTime s t)
        (I.image (simulatorOrdinal M hs w t P)) simulatorTargets Γ := by
  classical
  obtain ⟨E, hEcard, hEtime, hproject, _hshadow⟩ :=
    native_guarded_projection hs ht H B hB
  let A := delayedGuard M hs w t P B targets
  let Γ := (E ∪ A) ∪ extra
  refine ⟨Γ, ?_, ?_, ?_⟩
  · have hA : A.card ≤ (B.card + 1) * (2 * s - 1) :=
      delayedGuard_card_le hs H hP B targets
    calc
      Γ.card ≤ (E.card + A.card) + extra.card :=
        (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add hEcard hA) _
  · intro u hu
    rcases mem_union.mp hu with hu | hu
    · rcases mem_union.mp hu with hu | hu
      · exact hEtime u hu
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hu
        exact (actual_sourceRoot_le_clock hs ht H (i.isLt.trans_le hP)).1
    · exact hextra u hu
  · intro ρ u hu hpath hend
    by_contra hn
    have hfree : ∀ v ∈ u :: ρ, v ∉ Γ := by
      intro v hv hvΓ
      exact hn ⟨v, hv, hvΓ⟩
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
    have huT := (actual_sourceRoot_le_clock hs ht H (i.isLt.trans_le hP)).1
    have hEfree : ∀ v ∈ simulatorOrdinal M hs w t P i :: ρ, v ∉ E :=
      fun v hv hve => hfree v hv (mem_union_left _ (mem_union_left _ hve))
    have hroute := hproject _ ρ huT hpath hEfree
    have hendfree : (simulatorOrdinal M hs w t P i :: ρ).getLastD
        (simulatorOrdinal M hs w t P i) ∉ extra := by
      intro he
      apply hfree _ (by simpa only [List.getLastD_cons] using
        (List.getLastD_mem_cons (l := ρ) (a := simulatorOrdinal M hs w t P i)))
      exact mem_union_right _ (by simpa only [List.getLastD_cons] using he)
    obtain ⟨p, hp, hconnector⟩ := hconnect _ hend hendfree
    obtain ⟨π, hπ, hlast, hπfree⟩ := hroute.trans hconnector
    have hreach : shadowOrdinal M hs w t P i ∈
        TransferReachability.reaches (trace M w).work t B targets := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (sourceClock_lt ht _), π, hπ, ?_, hπfree⟩
      change (sourceClock s t (simulatorRoot M hs w t i.val) :: π).getLastD
        (sourceClock s t (simulatorRoot M hs w t i.val)) ∈ targets
      rw [hlast]
      exact hp
    exact unguarded_shadow_not_reaches hs ht H hP hcut (mem_image_of_mem _ hi)
      (fun hA => hfree _ (List.mem_cons_self ..)
        (mem_union_left _ (mem_union_right _ hA))) hreach

end AdaptiveTransfer.TransferCrossing
