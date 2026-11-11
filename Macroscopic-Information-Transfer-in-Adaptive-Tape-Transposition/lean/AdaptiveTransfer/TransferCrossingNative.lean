import AdaptiveTransfer.TransferCrossingDiscard
import AdaptiveTransfer.TransferCrossingPacking
import AdaptiveTransfer.TransferCrossingLift
import AdaptiveTransfer.TransferCrossingConnector

/-! Complete finite crossing-target transport for the actual native compiler.
Canonical boundary discards, long-hop target guards, original crossing
connectors, and ordinal guards give the exact separator budget. -/

namespace AdaptiveTransfer.TransferCrossing
open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth NativeRelations
open TapeStorageRates TapeStorageRates.Native
open AdaptiveTransfer.TransferClock AdaptiveTransfer.TransferFIFO
open AdaptiveTransfer.TransferRoots AdaptiveTransfer.TransferGuards

/-- An unconditional epoch bound for every actual simulator work head. -/
theorem native_crossing_epoch_bound (M : TM) {s : ℕ} (hs : 0 < s)
    (w : List Bool) (t H : ℕ) (hH : 1 ≤ H) (j : Fin M.k) :
    (tapeSkeleton ((trace (machine M hs) w).work j) (alignedTime s t) H).length + 1 ≤
      alignedTime s t / H + 1 := by
  apply Nat.add_le_add_right
  apply (Nat.le_div_iff_mul_le (by omega : 0 < H)).mpr
  exact tapeSkeleton_length_mul_le ((trace (machine M hs) w).work_isWalk j)
    ((trace (machine M hs) w).work_zero j) _ hH

noncomputable def nativeCrossingExtra (M : TM) {s : ℕ} (hs : 0 < s)
    (w : List Bool) (t H h : ℕ) (hH : 1 ≤ H) (B : Finset ℕ) : Finset ℕ :=
  globalDiscarded (trace (machine M hs) w).work
    (trace (machine M hs) w).work_isWalk (trace (machine M hs) w).work_zero
    (U := alignedTime s t) hH (2 * h + 6 * s + 2) ∪
  crossingTargetGuard (trace (machine M hs) w).work (trace M w).work
    (alignedTime s t) H (3 * s) B

theorem nativeCrossingExtra_live {M : TM} {s t H h v : ℕ} {w : List Bool}
    {hs : 0 < s} {hH : 1 ≤ H} {B : Finset ℕ}
    (hv : v ∈ nativeCrossingExtra M hs w t H h hH B) : v < alignedTime s t := by
  classical
  rcases mem_union.mp hv with hv | hv
  · exact globalDiscarded_live _ _ _ _ _ _ hv
  · exact crossingTargetGuard_live hv

theorem nativeCrossingExtra_card_le {M : TM} {s t H h K₀ : ℕ} {w : List Bool}
    (hs : 0 < s) (hH : 1 ≤ H)
    (hK : ∀ j, (tapeSkeleton ((trace (machine M hs) w).work j)
      (alignedTime s t) H).length + 1 ≤ K₀) (B : Finset ℕ) :
    (nativeCrossingExtra M hs w t H h hH B).card ≤
      4 * M.k * K₀ ^ 2 * (2 * h + 6 * s + 3) +
        M.k * (6 * s + 3) * ((alignedTime s t - 1) / (4 * H + 2)) * B.card := by
  classical
  apply (card_union_le _ _).trans
  exact Nat.add_le_add
    (globalDiscarded_shadow_card_le _ (trace (machine M hs) w).work_isWalk
      (trace (machine M hs) w).work_zero hH hK h s)
    (crossingTargetGuard_card_three_scale (trace (machine M hs) w).work_isWalk _ _ _ _)

/-- Every surviving literal simulator crossing target connects to a literal
source crossing target. The canonical frame and both strict margins are
derived here, so no assignment or source-target certificate is assumed. -/
theorem native_surviving_crossing_connector {M : TM} {s t H h v : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (halt : HaltsAt M w t) (hH : 1 ≤ H)
    (B : Finset ℕ)
    (hv : v ∈ crossingLowerEtaSteps (trace (machine M hs) w) (alignedTime s t) H 1 (alignedTime s t))
    (hgood : v ∉ nativeCrossingExtra M hs w t H h hH B) :
    ∃ p ∈ crossingLowerEtaSteps (trace M w) t h 1 t,
      Route (trace M w).work t B (sourceClock s t v) p := by
  classical
  have hdiscard : v ∉ globalDiscarded (trace (machine M hs) w).work
      (trace (machine M hs) w).work_isWalk (trace (machine M hs) w).work_zero
      (U := alignedTime s t) hH (2 * h + 6 * s + 2) :=
    fun hv => hgood (mem_union_left _ hv)
  have hguard : v ∉ crossingTargetGuard (trace (machine M hs) w).work (trace M w).work
      (alignedTime s t) H (3 * s) B := fun hv => hgood (mem_union_right _ hv)
  obtain ⟨j, hj, _hvU, hlo, hhi⟩ := surviving_crossing_frame (trace (machine M hs) w) hH hv hdiscard
  let F := chosenFrame ((trace (machine M hs) w).work_isWalk j)
    ((trace (machine M hs) w).work_zero j) hH ⟨v, hj⟩
  have heq : 2 * h + 2 * (3 * s) + 2 = 2 * h + 6 * s + 2 := by omega
  obtain ⟨p, hp, hroute⟩ := native_frame_cut_connector (h := h) hs ht halt j F
    (by simpa only [heq] using hlo) (by simpa only [heq] using hhi) B hguard
  refine ⟨p, ?_, hroute⟩
  rw [crossingLowerEtaSteps_eq_biUnion_tapeCrossingLowers]
  exact mem_biUnion.mpr ⟨j, mem_univ _, hp⟩

/-- Finite crossing-target transport on actual source and compiled runs.
The only original cut assumption is the stated source separator. Every
simulator guard, target connector, and ordinal discrepancy is constructed. -/
theorem native_crossing_cut_lift_pos {M : TM} {s t P H h K₀ : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (halt : HaltsAt M w t)
    (hP : P ≤ outputCount M w t) (hH : 1 ≤ H)
    (hK : ∀ j, (tapeSkeleton ((trace (machine M hs) w).work j)
      (alignedTime s t) H).length + 1 ≤ K₀)
    (I : Finset (Fin P)) (B : Finset ℕ) (hB : ∀ b ∈ B, b < t)
    (hcut : IsMengerVertexCut (trace M w).work t (I.image (sourceOrdinal M w t P))
      (crossingLowerEtaSteps (trace M w) t h 1 t) B) :
    ∃ Γ : Finset ℕ,
      Γ.card ≤ crossingCutFactor M.k s (alignedTime s t) H * B.card + crossingCutError M.k s K₀ h ∧
      (∀ u ∈ Γ, u < alignedTime s t) ∧
      IsMengerVertexCut (trace (machine M hs) w).work (alignedTime s t)
        (I.image (simulatorOrdinal M hs w t P))
        (crossingLowerEtaSteps (trace (machine M hs) w) (alignedTime s t) H 1 (alignedTime s t)) Γ := by
  classical
  obtain ⟨Γ, hΓ, hΓtime, hΓcut⟩ := native_target_route_cut_lift_pos hs ht halt hP I
    (crossingLowerEtaSteps (trace M w) t h 1 t)
    (crossingLowerEtaSteps (trace (machine M hs) w) (alignedTime s t) H 1 (alignedTime s t))
    (nativeCrossingExtra M hs w t H h hH B) B hB
    (fun _ hv => nativeCrossingExtra_live hv)
    (fun _ hv hgood => native_surviving_crossing_connector hs ht halt hH B hv hgood) hcut
  refine ⟨Γ, hΓ.trans ?_, hΓtime, hΓcut⟩
  calc
    _ ≤ (4 * (10 * s + 1) + M.k * (6 * s + 1)) * B.card +
        (B.card + 1) * (2 * s - 1) +
        (4 * M.k * K₀ ^ 2 * (2 * h + 6 * s + 3) +
          M.k * (6 * s + 3) * ((alignedTime s t - 1) / (4 * H + 2)) * B.card) :=
      Nat.add_le_add_left (nativeCrossingExtra_card_le hs hH hK B) _
    _ = _ := by unfold crossingCutFactor crossingCutError; ring

/-- Complete native finite lift, including immediate halting. In that case
the existing-output assumption forces the ordinal set to be empty. -/
theorem native_crossing_cut_lift {M : TM} {s t P H h K₀ : ℕ} {w : List Bool}
    (hs : 0 < s) (halt : HaltsAt M w t)
    (hP : P ≤ outputCount M w t) (hH : 1 ≤ H)
    (hK : ∀ j, (tapeSkeleton ((trace (machine M hs) w).work j)
      (alignedTime s t) H).length + 1 ≤ K₀)
    (I : Finset (Fin P)) (B : Finset ℕ) (hB : ∀ b ∈ B, b < t)
    (hcut : IsMengerVertexCut (trace M w).work t (I.image (sourceOrdinal M w t P))
      (crossingLowerEtaSteps (trace M w) t h 1 t) B) :
    ∃ Γ : Finset ℕ,
      Γ.card ≤ crossingCutFactor M.k s (alignedTime s t) H * B.card + crossingCutError M.k s K₀ h ∧
      (∀ u ∈ Γ, u < alignedTime s t) ∧
      IsMengerVertexCut (trace (machine M hs) w).work (alignedTime s t)
        (I.image (simulatorOrdinal M hs w t P))
        (crossingLowerEtaSteps (trace (machine M hs) w) (alignedTime s t) H 1 (alignedTime s t)) Γ := by
  by_cases ht : t = 0
  · subst t
    have hzero : P = 0 := by change P ≤ 0 at hP; omega
    subst P
    have hI : I = ∅ := eq_empty_of_isEmpty I
    refine ⟨∅, by simp, by simp, ?_⟩
    intro ρ u hu _ _
    simp only [hI, image_empty, notMem_empty] at hu
  · exact native_crossing_cut_lift_pos hs (by omega) halt hP hH hK I B hB hcut

/-- The finite native lift without a supplied epoch count: its value is
computed from the actual simulator horizon and the chosen grid width. -/
theorem native_crossing_cut_lift_auto_epochs {M : TM} {s t P H h : ℕ} {w : List Bool}
    (hs : 0 < s) (halt : HaltsAt M w t)
    (hP : P ≤ outputCount M w t) (hH : 1 ≤ H)
    (I : Finset (Fin P)) (B : Finset ℕ) (hB : ∀ b ∈ B, b < t)
    (hcut : IsMengerVertexCut (trace M w).work t (I.image (sourceOrdinal M w t P))
      (crossingLowerEtaSteps (trace M w) t h 1 t) B) :
    ∃ Γ : Finset ℕ,
      Γ.card ≤ crossingCutFactor M.k s (alignedTime s t) H * B.card +
        crossingCutError M.k s (alignedTime s t / H + 1) h ∧
      (∀ u ∈ Γ, u < alignedTime s t) ∧
      IsMengerVertexCut (trace (machine M hs) w).work (alignedTime s t)
        (I.image (simulatorOrdinal M hs w t P))
        (crossingLowerEtaSteps (trace (machine M hs) w) (alignedTime s t) H 1 (alignedTime s t)) Γ :=
  native_crossing_cut_lift hs halt hP hH (native_crossing_epoch_bound M hs w t H hH) I B hB hcut

end AdaptiveTransfer.TransferCrossing
