import AdaptiveTransfer.TransferActivationGuards
import AdaptiveTransfer.TransferFIFO

/-! Actual delayed and look-ahead root guards for the aligned native
simulator. All output-order and look-ahead estimates are derived from its
execution, not supplied as a root-correspondence certificate. -/

namespace AdaptiveTransfer.TransferRoots
open Finset Transpose Transpose.Tape MergeDepth NativeRelations
open TapeStorageRates TapeStorageRates.Native
open AdaptiveTransfer.TransferClock AdaptiveTransfer.TransferFIFO
open AdaptiveTransfer.TransferReachability LeanMachine.FiniteOrdinalGuards
attribute [local instance] Classical.propDecidable

noncomputable def sourceOrdinal (M : TM) (w : List Bool) (t P : ℕ) : Fin P → ℕ :=
  fun i => sourceRoot M w t i.val

noncomputable def simulatorOrdinal (M : TM) {s : ℕ} (hs : 0 < s)
    (w : List Bool) (t P : ℕ) : Fin P → ℕ := fun i => simulatorRoot M hs w t i.val

noncomputable def shadowOrdinal (M : TM) {s : ℕ} (hs : 0 < s)
    (w : List Bool) (t P : ℕ) : Fin P → ℕ :=
  fun i => sourceClock s t (simulatorOrdinal M hs w t P i)

theorem sourceOrdinal_strictMono {M : TM} {w : List Bool} {t P : ℕ}
    (hP : P ≤ outputCount M w t) : StrictMono (sourceOrdinal M w t P) := by
  intro i j hij
  apply (sourceRoot_lt_iff_count M w (i.isLt.trans_le hP)).mpr
  change i.val < outputCount M w (sourceRoot M w t j.val)
  rw [(sourceRoot_counts M w (j.isLt.trans_le hP)).2.1]
  exact hij

noncomputable def delayedGuard (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool)
    (t P : ℕ) (B targets : Finset ℕ) : Finset ℕ :=
  (activationGuard (trace M w).work t B targets
    (sourceOrdinal M w t P) (shadowOrdinal M hs w t P)).image (simulatorOrdinal M hs w t P)

theorem delayedGuard_card_le {M : TM} {s t P : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (hP : P ≤ outputCount M w t)
    (B targets : Finset ℕ) :
    (delayedGuard M hs w t P B targets).card ≤ (B.card + 1) * (2 * s - 1) := by
  apply card_image_le.trans
  apply activationGuard_card_le (trace M w).work B targets (outputCount_mono M w)
  · intro i c hc
    exact (sourceRoot_lt_iff_count M w (i.isLt.trans_le hP)).mp hc
  · intro i
    exact (actual_ordinal_lookahead hs H (i.isLt.trans_le hP)).1

/-- A source separator still excludes every projected matched root after
the explicitly counted delayed-root guard is removed. -/
theorem unguarded_shadow_not_reaches {M : TM} {s t P : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t) (hP : P ≤ outputCount M w t)
    {B targets roots : Finset ℕ} {i : Fin P}
    (hcut : IsMengerVertexCut (trace M w).work t roots targets B)
    (hi : sourceOrdinal M w t P i ∈ roots)
    (hg : simulatorOrdinal M hs w t P i ∉ delayedGuard M hs w t P B targets) :
    shadowOrdinal M hs w t P i ∉ reaches (trace M w).work t B targets := by
  apply TransferReachability.unguarded_shadow_not_reaches hcut hi
    (actual_sourceRoot_le_clock hs ht H (i.isLt.trans_le hP)).2
  intro hguard
  exact hg (mem_image_of_mem _ hguard)

noncomputable def forwardGuard (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool)
    (t P : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (lookaheadUnion (sourceOrdinal M w t P) (2 * s) B).image (simulatorOrdinal M hs w t P)

noncomputable def terminalGuard (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool)
    (t P : ℕ) : Finset ℕ :=
  (terminal P (2 * s)).image (simulatorOrdinal M hs w t P)

theorem forwardGuard_card_le {M : TM} {s t P : ℕ} {w : List Bool}
    (hs : 0 < s) (hP : P ≤ outputCount M w t) (B : Finset ℕ) :
    (forwardGuard M hs w t P B).card ≤ B.card * (2 * s + 1) :=
  card_image_le.trans (lookaheadUnion_card_le (sourceOrdinal_strictMono hP) B)

theorem terminalGuard_card_le (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool) (t P : ℕ) :
    (terminalGuard M hs w t P).card ≤ 2 * s :=
  card_image_le.trans (terminal_card_le P (2 * s))

theorem future_defined_of_not_terminal {M : TM} {s t P : ℕ} {w : List Bool}
    {hs : 0 < s} {i : Fin P}
    (hg : simulatorOrdinal M hs w t P i ∉ terminalGuard M hs w t P) :
    i.val + 2 * s < P := by
  by_contra hn
  exact hg (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, by omega⟩))

/-- The closed source-root interval is free of the original cut, including
both ordinal endpoints. No bound on physical output waiting time is needed. -/
theorem forwardGuard_interval_free {M : TM} {s t P : ℕ} {w : List Bool}
    {hs : 0 < s} {i : Fin P} {B : Finset ℕ}
    (hfuture : i.val + 2 * s < P)
    (hg : simulatorOrdinal M hs w t P i ∉ forwardGuard M hs w t P B) :
    ∀ c ∈ Icc (sourceOrdinal M w t P i) (sourceRoot M w t (i.val + 2 * s)), c ∉ B := by
  intro c hc hB
  apply hg
  apply mem_image_of_mem
  apply mem_biUnion.mpr
  refine ⟨c, hB, mem_filter.mpr ⟨mem_univ _, ⟨i.val + 2 * s, hfuture⟩, rfl, ?_⟩⟩
  exact mem_Icc.mp hc

end AdaptiveTransfer.TransferRoots
