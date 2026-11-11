import AdaptiveTransfer.TransferGuardedProjection

/-! The guarded projection for the actual published aligned native machine.
The finite graph construction is instantiated with proved table-level shadow
and exact clock facts, with no supplied projected-path or shadow certificate. -/
namespace AdaptiveTransfer.TransferGuards
open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth Finset
open TapeStorageRates TapeStorageRates.Native AdaptiveTransfer.TransferClock

/-- The complete guarded-path lemma on an actual halting source execution.
Both ends are included in cut avoidance, every guard is a real simulator
vertex, and the input-head shadow is asserted without any input-revisit edge. -/
theorem native_guarded_projection {M : TM} {s t : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b < t) :
    ∃ E : Finset ℕ,
      E.card ≤ (4 * (10 * s + 1) + M.k * (6 * s + 1)) * B.card ∧
      (∀ u ∈ E, u < alignedTime s t) ∧
      (∀ (u : ℕ) (ρ : List ℕ), u < alignedTime s t →
        IsDepPath (trace (machine M hs) w).work (alignedTime s t) (u :: ρ) →
        (∀ v ∈ u :: ρ, v ∉ E) →
        Route (trace M w).work t B (sourceClock s t u)
          (sourceClock s t ((u :: ρ).getLastD u))) ∧
      (∀ (u : ℕ), u < alignedTime s t → ∀ h : Option (Fin M.k),
        |headPosition (trace (machine M hs) w) h u -
          headPosition (trace M w) h (sourceClock s t u)| ≤ 3 * s) := by
  let E := projectionGuard s t (trace M w).work (trace (machine M hs) w).work (3 * s) B
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · have hh := projectionGuard_card_le (trace M w).work (trace (machine M hs) w).work
      (R := 3 * s) hs B hB
    convert hh using 1
    unfold batchLength
    ring
  · exact fun _u hu => projectionGuard_time hu
  · intro u ρ hu hpath hgood
    apply project_path ht (trace M w).work_isWalk _ u ρ hu hpath hgood
    intro h v hv
    exact actual_head_shadow hs ht H hv (some h)
  · exact fun u hu h => actual_head_shadow hs ht H hu h

end AdaptiveTransfer.TransferGuards
