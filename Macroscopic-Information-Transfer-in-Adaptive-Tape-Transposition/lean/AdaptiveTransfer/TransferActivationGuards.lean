import AdaptiveTransfer.TransferReachability
import LeanMachine.FiniteOrdinalGuards

/-! Delayed-root guards for literal cut-avoiding dependency reachability.
The source activation bound and ordinal count are combined before any
particular simulator is substituted. -/

namespace AdaptiveTransfer.TransferReachability
open Finset MergeDepth NativeRelations LeanMachine.FiniteOrdinalGuards
attribute [local instance] Classical.propDecidable

noncomputable def activationGuard {k P : ℕ} (xs : Fin k → ℕ → ℤ)
    (T : ℕ) (B targets : Finset ℕ) (root shadow : Fin P → ℕ) : Finset (Fin P) :=
  delayedUnion root shadow (runStarts (reaches xs T B targets))

theorem activationGuard_card_le {k P T K : ℕ} (xs : Fin k → ℕ → ℤ)
    (B targets : Finset ℕ) {root shadow : Fin P → ℕ} {O : ℕ → ℕ}
    (hO : Monotone O) (hroot : ∀ i c, root i < c → i.val < O c)
    (hpre : ∀ i, O (shadow i) ≤ i.val + K) :
    (activationGuard xs T B targets root shadow).card ≤ (B.card + 1) * K :=
  (delayedUnion_card_le hO hroot hpre _).trans
    (Nat.mul_le_mul_right K (reaches_activations xs B targets))

/-- If an actual source root is separated but its projected root reaches
the target, that ordinal belongs to the explicitly defined activation guard. -/
theorem mem_activationGuard {k P T : ℕ} {xs : Fin k → ℕ → ℤ}
    {B targets : Finset ℕ} {root shadow : Fin P → ℕ} {i : Fin P}
    (hle : root i ≤ shadow i) (hroot : root i ∉ reaches xs T B targets)
    (hshadow : shadow i ∈ reaches xs T B targets) :
    i ∈ activationGuard xs T B targets root shadow := by
  obtain ⟨c, hc, hr, hs⟩ := activation_between
    (fun _ ht => reaches_before ht) hle hroot hshadow
  exact mem_biUnion.mpr ⟨c, hc, mem_filter.mpr ⟨mem_univ _, hr, hs⟩⟩

theorem unguarded_shadow_not_reaches {k P T : ℕ} {xs : Fin k → ℕ → ℤ}
    {B targets roots : Finset ℕ} {root shadow : Fin P → ℕ} {i : Fin P}
    (hcut : IsMengerVertexCut xs T roots targets B) (hi : root i ∈ roots)
    (hle : root i ≤ shadow i)
    (hguard : i ∉ activationGuard xs T B targets root shadow) :
    shadow i ∉ reaches xs T B targets :=
  fun hs => hguard (mem_activationGuard hle (cut_excludes_reaches hcut hi) hs)

end AdaptiveTransfer.TransferReachability
