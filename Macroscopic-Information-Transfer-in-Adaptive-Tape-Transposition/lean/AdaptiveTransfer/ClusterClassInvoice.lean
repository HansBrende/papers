import AdaptiveTransfer.NativeClusterEvents
import AdaptiveTransfer.CoreRecordCounts

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting Finset NativeRelations LeanMachine
open scoped BigOperators

section Classes
variable {M : TM} {d b T W N H J j : ℕ} {c error : ℝ}
  (D : Finset (Fin (d * d * b) → Bool))
  (correct : ∀ X : D, TransposesInput M d b c X.val)
  (charts : ∀ X : D, ClusterChart (trace M (List.ofFn X.val)).work
    (trace M (List.ofFn X.val)).haltTime error)
  (obs : ∀ X : D, ClusterObservation (charts X) T W N j)
  (returns : ∀ X : D, (offClusterReturns (trace M (List.ofFn X.val)).work
    (charts X).included (trace M (List.ofFn X.val)).haltTime H).card ≤ J)
  (X₀ : D) (same : ∀ X : D, (obs X).encode = (obs X₀).encode)

theorem constantClusterClass_snapshot_le :
    (Fintype.card (constantClusterClass D correct charts obs returns X₀ same).SnapshotDomain : ℝ) ≤
      if (obs X₀).start = 0 then 0 else (W : ℝ) + M.k := by
  rw [CoreReplayClass.snapshotDomain_card]
  change ((if (obs X₀).start = 0 then 0 else
    ∑ h : Fin M.k, ((charts X₀).core (obs X₀).ell W j h).card : ℕ) : ℝ) ≤ _
  split_ifs
  · simp only [Nat.cast_zero, le_refl]
  · exact_mod_cast (charts X₀).sum_core_card_le (obs X₀).ell W j

theorem constantClusterClass_saving (a : ℕ) (saving : ℝ)
    (margin : saving ≤ ((obs X₀).omittedGeometry (tposOf d b)).card -
      (a : ℝ) * (if (obs X₀).start = 0 then 0 else (W : ℝ) + M.k)) :
    saving ≤ ((constantClusterClass D correct charts obs returns X₀ same).omitted.card : ℝ) -
      (a : ℝ) * Fintype.card (constantClusterClass D correct charts obs returns X₀ same).SnapshotDomain := by
  rw [constantClusterClass_omitted]
  exact margin.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left
    (constantClusterClass_snapshot_le D correct charts obs returns X₀ same) (Nat.cast_nonneg a)) _)

end Classes
end AdaptiveTransfer
