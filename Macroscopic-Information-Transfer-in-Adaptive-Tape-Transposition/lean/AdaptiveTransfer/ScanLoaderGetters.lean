import AdaptiveTransfer.ScanLoaderInvariant
import AdaptiveTransfer.ScanLoaderCheckpoints
import AdaptiveTransfer.GetterNativeGeometry

/-! Actual checkpoint getters for the entire paid preparation and consumer
execution. Virtual ports follow archive-head moves with a one-element observer.
Every old archive read is reconstructed, so every whole-run discrepancy set is
empty. Neither of these conclusions is supplied as a hypothesis.
-/

namespace AdaptiveTransfer.ScanLoader

open Transpose

variable {r : ℕ} {S A : Fin r → Type*} {Q B : Type*}
variable (F : (j : Fin r) → S j → Bool → S j)
  (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S) (q₀ : Q)
  (C : Consumer Q A B)
variable [Fintype Q] [∀ j, Fintype (S j)] [∀ j, Fintype (A j)] [Fintype B]

/-- No scan history is kept by the observer. Its ports follow the actual
native archive-head moves, and its finite auxiliary state is `Unit`. -/
noncomputable def archiveObserver (R : ℕ) :
    Getter.Observer (nativeProducer F D s₀ q₀ C) Unit r R where
  initial := ()
  origins := fun _ => 0
  update _ instruction := ((), fun j => (instruction.2.2.1 j.succ).2)

theorem archiveObserver_tracks (R : ℕ) (w : List Bool) (t : ℕ) (j : Fin r) :
    ((archiveObserver F D s₀ q₀ C R).run w t).2 j =
      (Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w t).workPos j.succ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Getter.Observer.run]
    apply Eq.trans ?_ (Transpose.Tape.Impl.run_succ_workPos
      (M := nativeProducer F D s₀ q₀ C) (w := w) t j.succ).symm
    cases ht : Transpose.Tape.transAt (nativeProducer F D s₀ q₀ C) w t with
    | none => exact ih
    | some instruction =>
      change (instruction.2.2.1 j.succ).2.shift _ = (instruction.2.2.1 j.succ).2.shift _
      rw [ih]

theorem archiveObserver_windows (R : ℕ) (w : List Bool) (t : ℕ) (j : Fin r) :
    (archiveObserver F D s₀ q₀ C R).rawWindows w t j.succ =
      rawWindow R w ((Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w t).workPos j.succ) := by
  funext i
  simp only [Getter.Observer.rawWindows, Getter.Observer.allPorts_succ,
    archiveObserver_tracks, rawWindow]

/-- The public getter receives only the previously declared context. During
START/MARK/LOAD it returns blank; afterward it evaluates the completed code.
The carrier's own prediction is immaterial and simply repeats its known value. -/
noncomputable def nativeArchiveGetters (P R K : ℕ) :
    Getter.Getters (nativeProducer F D s₀ q₀ C) Unit (SpatialLabel S K) r R :=
  fun h context => Fin.cases context.carrier (fun j =>
    pointCode (blank (A := A) (B := B))
      (if completedPhase ((pointCode (start (Q := Q) (S := S))).symm context.sourceState)
      then archiveGetter F D s₀ P R K context.label j (context.workPos j.succ) (context.raw j.succ)
      else blank)) h

/-- Correctness is derived for every old archive read on every actual run,
including all preparation steps and arbitrary read-only consumer reversals. -/
theorem nativeArchiveGetters_correct (hC : PreservesArchives C)
    {P R K : ℕ} (hcover : P ≤ (R + 1) * K) (w : List Bool) (hw : w.length = P)
    (t : ℕ) (j : Fin r) :
    Getter.prediction (archiveObserver F D s₀ q₀ C R) (nativeArchiveGetters F D s₀ q₀ C P R K)
      (0 : Fin (r + 1)) (spatialLabel F s₀ R K w) w t j.succ =
      (Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w t).work j.succ
        ((Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w t).workPos j.succ) := by
  rw [native_old_archive F D s₀ q₀ C hC]
  unfold Getter.prediction nativeArchiveGetters Getter.getterContext
  change pointCode (blank (A := A) (B := B))
      (if completedPhase ((pointCode (start (Q := Q) (S := S))).symm
        (Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w t).state)
      then archiveGetter F D s₀ P R K (spatialLabel F s₀ R K w) j
        ((Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w t).workPos j.succ)
        ((archiveObserver F D s₀ q₀ C R).rawWindows w t j.succ)
      else blank) = _
  rw [archiveObserver_windows, archiveGetter_correct F D s₀ hcover w hw]

/-- The original whole-run discrepancy statistic is identically zero, for
every horizon and excursion threshold. The proof uses no getter premise. -/
theorem nativeArchiveGetters_zero_errors (hC : PreservesArchives C)
    {P R K : ℕ} (hcover : P ≤ (R + 1) * K) (w : List Bool) (hw : w.length = P)
    (T H : ℕ) :
    Getter.nativeErrors (archiveObserver F D s₀ q₀ C R) (nativeArchiveGetters F D s₀ q₀ C P R K)
      (0 : Fin (r + 1)) (spatialLabel F s₀ R K w) w T H = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hret, herr⟩ := Finset.mem_filter.mp he
  simp only [offCarrierReturns, Finset.mem_filter] at hret
  have hne : e.1 ≠ (0 : Fin (r + 1)) := hret.2.1
  have hcorrect : ∀ h : Fin (r + 1), h ≠ 0 →
      (Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w e.2.2).work h
          ((Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w e.2.2).workPos h) =
        Getter.prediction (archiveObserver F D s₀ q₀ C R) (nativeArchiveGetters F D s₀ q₀ C P R K)
          (0 : Fin (r + 1)) (spatialLabel F s₀ R K w) w e.2.2 h := by
    intro h
    refine Fin.cases ?_ (fun j _ => ?_) h
    · exact fun hn => False.elim (hn rfl)
    · exact (nativeArchiveGetters_correct F D s₀ q₀ C hC hcover w hw e.2.2 j).symm
  exact herr (hcorrect e.1 hne)

end AdaptiveTransfer.ScanLoader
