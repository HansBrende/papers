import AdaptiveTransfer.TransferNativeProjection
import AdaptiveTransfer.TransferNativeRoots
import AdaptiveTransfer.TransferInputGeometry

/-! Actual finite eroded-read separator lifting. The source cut is given;
the simulator cut is constructed from the checked native edge guard and
actual delayed-root activations, with the exact 2s-1 ordinal bill. -/
namespace AdaptiveTransfer.TransferEroded
open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth NativeRelations
open TapeStorageRates TapeStorageRates.Native
open AdaptiveTransfer.TransferClock AdaptiveTransfer.TransferFIFO
open AdaptiveTransfer.TransferRoots AdaptiveTransfer.TransferGuards

/-- Written as a sum of nonnegative bills; for s≥1 this is exactly the
manuscript's 4B0+k(6s+1)+2s−1. -/
def erodedCutFactor (k s : ℕ) : ℕ := 4 * (10 * s + 1) + k * (6 * s + 1) + (2 * s - 1)

theorem erodedCutFactor_eq {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    erodedCutFactor k s = 4 * (10 * s + 1) + k * (6 * s + 1) + 2 * s - 1 := by
  unfold erodedCutFactor
  omega

/-- Positive-time version. Every ordinal in I is an actual existing append;
no correctness or common execution trace is required. -/
theorem native_eroded_cut_lift_pos {M : TM} {s t P : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t)
    (hP : P ≤ outputCount M w t) (I : Finset (Fin P)) (U : Finset ℤ)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b < t)
    (hcut : IsMengerVertexCut (trace M w).work t
      (I.image (sourceOrdinal M w t P)) (inputReadSteps (trace M w) t U) B) :
    ∃ Γ : Finset ℕ,
      Γ.card ≤ erodedCutFactor M.k s * B.card + (2 * s - 1) ∧
      (∀ u ∈ Γ, u < alignedTime s t) ∧
      IsMengerVertexCut (trace (machine M hs) w).work (alignedTime s t)
        (I.image (simulatorOrdinal M hs w t P))
        (inputReadSteps (trace (machine M hs) w) (alignedTime s t) (inputErosion U (3 * s))) Γ := by
  classical
  obtain ⟨E, hEcard, hEtime, hproject, _hshadow⟩ := native_guarded_projection hs ht H B hB
  let A := delayedGuard M hs w t P B (inputReadSteps (trace M w) t U)
  let Γ := E ∪ A
  refine ⟨Γ, ?_, ?_, ?_⟩
  · have hA : A.card ≤ (B.card + 1) * (2 * s - 1) := delayedGuard_card_le hs H hP B _
    calc
      Γ.card ≤ E.card + A.card := card_union_le _ _
      _ ≤ (4 * (10 * s + 1) + M.k * (6 * s + 1)) * B.card +
          (B.card + 1) * (2 * s - 1) := Nat.add_le_add hEcard hA
      _ = _ := by unfold erodedCutFactor; ring
  · intro u hu
    rcases mem_union.mp hu with hu | hu
    · exact hEtime u hu
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hu
      exact (actual_sourceRoot_le_clock hs ht H (i.isLt.trans_le hP)).1
  · intro ρ u hu hpath hend
    by_contra hn
    have hfree : ∀ v ∈ u :: ρ, v ∉ Γ := by
      intro v hv hvΓ
      exact hn ⟨v, hv, hvΓ⟩
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
    have huT := (actual_sourceRoot_le_clock hs ht H (i.isLt.trans_le hP)).1
    have hEfree : ∀ v ∈ simulatorOrdinal M hs w t P i :: ρ, v ∉ E :=
      fun v hv hve => hfree v hv (mem_union_left _ hve)
    obtain ⟨π, hπ, hlast, hπfree⟩ := hproject _ ρ huT hpath hEfree
    have hreach : shadowOrdinal M hs w t P i ∈
        TransferReachability.reaches (trace M w).work t B (inputReadSteps (trace M w) t U) := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (sourceClock_lt ht _), π, hπ, ?_, hπfree⟩
      change (sourceClock s t (simulatorRoot M hs w t i.val) :: π).getLastD
        (sourceClock s t (simulatorRoot M hs w t i.val)) ∈ _
      rw [hlast]
      exact actual_eroded_read_projects hs ht H hend
    exact unguarded_shadow_not_reaches hs ht H hP hcut (mem_image_of_mem _ hi)
      (fun hA => hfree _ (List.mem_cons_self ..) (mem_union_right _ hA)) hreach

/-- Complete finite lift, including a source that halts immediately. In that
case there are no existing append ordinals and the empty separator suffices. -/
theorem native_eroded_cut_lift {M : TM} {s t P : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t)
    (hP : P ≤ outputCount M w t) (I : Finset (Fin P)) (U : Finset ℤ)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b < t)
    (hcut : IsMengerVertexCut (trace M w).work t
      (I.image (sourceOrdinal M w t P)) (inputReadSteps (trace M w) t U) B) :
    ∃ Γ : Finset ℕ,
      Γ.card ≤ erodedCutFactor M.k s * B.card + (2 * s - 1) ∧
      (∀ u ∈ Γ, u < alignedTime s t) ∧
      IsMengerVertexCut (trace (machine M hs) w).work (alignedTime s t)
        (I.image (simulatorOrdinal M hs w t P))
        (inputReadSteps (trace (machine M hs) w) (alignedTime s t) (inputErosion U (3 * s))) Γ := by
  by_cases ht : t = 0
  · subst t
    have hzero : P = 0 := by change P ≤ 0 at hP; omega
    subst P
    have hI : I = ∅ := eq_empty_of_isEmpty I
    refine ⟨∅, by simp, by simp, ?_⟩
    intro ρ u hu _ _
    simp only [hI, image_empty, notMem_empty] at hu
  · exact native_eroded_cut_lift_pos hs (by omega) H hP I U B hB hcut

end AdaptiveTransfer.TransferEroded
