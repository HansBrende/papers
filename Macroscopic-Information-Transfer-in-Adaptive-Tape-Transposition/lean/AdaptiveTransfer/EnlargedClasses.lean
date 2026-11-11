import AdaptiveTransfer.EnlargedGeometry
import AdaptiveTransfer.GetterNativeClasses

/-! Entire enlarged rules grouped by their computed bounded metadata.
These are actual runs, not supplied decoder or simulation certificates.
-/

namespace AdaptiveTransfer.Enlarged
open Transpose MergeDepth BoundedNesting NativeRelations Finset Getter

section Classes
variable {Q Γ Λ : Type*} {p R d b T W N : ℕ}
  (M : System Q Γ Λ 1 p R) (D : Finset (Fin (d * d * b) → Bool))
  (labels : D → Λ) (finish : D → ℕ)
  (successful : ∀ X : D, ∀ t < finish X, M.instruction (labels X) (List.ofFn X.val) t ≠ none)
  (output : ∀ X : D, (M.run (labels X) (List.ofFn X.val) (finish X)).outRev.reverse =
    List.ofFn (fun j => X.val (tposOf d b j)))
  (obs : ∀ X : D, SlabObservation (M.motionTrace (labels X) (List.ofFn X.val)) T W N)
  (finish_le : ∀ X : D, (obs X).finish ≤ finish X)
  (X₀ : D)
  (same : ∀ X : D,
    Observation.encode (obs X) (M.portPaths (labels X) (List.ofFn X.val)) M.origins
      (M.portPaths_walk _ _) (M.portPaths_zero _ _) =
    Observation.encode (obs X₀) (M.portPaths (labels X₀) (List.ofFn X₀.val)) M.origins
      (M.portPaths_walk _ _) (M.portPaths_zero _ _))

include same in
private theorem times_same (X : D) : (obs X).times = (obs X₀).times :=
  Observation.times_eq_of_encode_eq _ _ _ _ _ (same X)

/-- A whole-rule replay class obtained from the computed records. -/
noncomputable def constantClass : ReplayClass M (d * d * b) (tposOf d b) where
  inputs := D
  labels := labels
  finish := finish
  start := (obs X₀).start
  stop := (obs X₀).finish
  times := (obs X₀).times
  cells := Ico (obs X₀).ell ((obs X₀).ell + (W : ℤ))
  times_before := fun _t ht => (obs X₀).time_finish ht
  times_after := fun _t ht => (obs X₀).time_start ht
  finish_after X := by rw [← Observation.finish_eq _ _ _ _ _ (same X)]; exact finish_le X
  carrier X t ha ht := by
    rw [← times_same M D labels obs X₀ same X]
    have hf : (obs X).free = 0 := Subsingleton.elim _ _
    simp only [SlabObservation.times, selectedSlab, mem_filter, mem_Ico, hf, M.trace_work,
      Observation.start_eq _ _ _ _ _ (same X), Observation.finish_eq _ _ _ _ _ (same X),
      Observation.ell_eq _ _ _ _ _ (same X), ha, ht, true_and]
  live X t ht := by
    have ht' : t < (obs X).finish := by
      simpa only [Observation.finish_eq _ _ _ _ _ (same X)] using (obs X₀).time_finish ht
    exact M.live_of_instruction (successful X t (ht'.trans_le (finish_le X)))
  workEntry r := (M.motionTrace (labels X₀) (List.ofFn X₀.val)).work 0 r
  portEntry r j := M.portPaths (labels X₀) (List.ofFn X₀.val) j r
  portLo r j := runRawLo (M.portPaths (labels X₀) (List.ofFn X₀.val) j) (obs X₀).times (obs X₀).finish r
  portHi r j := runRawHi (M.portPaths (labels X₀) (List.ofFn X₀.val) j) (obs X₀).times (obs X₀).finish r
  outLo r := (appendList (M.motionTrace (labels X₀) (List.ofFn X₀.val)) r).length
  outHi r := (appendList (M.motionTrace (labels X₀) (List.ofFn X₀.val))
    (runEnd (obs X₀).times (obs X₀).finish r)).length
  work_entry X r hr := by
    rw [← M.trace_work]
    exact Observation.work_eq _ _ _ _ _ (same X) (by rwa [times_same M D labels obs X₀ same X]) 0
  port_entry X r hr := by
    funext j
    exact Observation.ports_eq _ _ _ _ _ (same X) (by rwa [times_same M D labels obs X₀ same X]) j
  output_entry X r hr := by
    rw [← M.trace_output_count]
    exact Observation.outLo_eq _ _ _ _ _ (same X) (by rwa [times_same M D labels obs X₀ same X])
  output_exit X r hr := by
    rw [← M.trace_output_count]
    have hh := Observation.outHi_eq _ _ _ _ _ (same X) (by rwa [times_same M D labels obs X₀ same X])
    simpa only [times_same M D labels obs X₀ same X, Observation.finish_eq _ _ _ _ _ (same X)] using hh
  extrema X r hr t ht j := by
    have hlo := Observation.portLo_eq _ _ _ _ _ (same X) (by rwa [times_same M D labels obs X₀ same X]) j
    have hhi := Observation.portHi_eq _ _ _ _ _ (same X) (by rwa [times_same M D labels obs X₀ same X]) j
    have hh := runRaw_extrema (x := M.portPaths (labels X) (List.ofFn X.val) j)
      (C := (obs X).times) (T := (obs X).finish)
      (by simpa only [times_same M D labels obs X₀ same X, Observation.finish_eq _ _ _ _ _ (same X)] using ht)
    exact ⟨hlo ▸ hh.1, hhi ▸ hh.2⟩
  correct := output

theorem constantClass_omitted :
    (constantClass M D labels finish successful output obs finish_le X₀ same).omitted =
      omittedPortBits (d := d) (b := b) (M.portPaths (labels X₀) (List.ofFn X₀.val))
        (fun j => appendTime (M.motionTrace (labels X₀) (List.ofFn X₀.val)) (finish X₀) j.val)
        (obs X₀).times (obs X₀).finish R := by
  have happ : d * d * b =
      (appendList (M.motionTrace (labels X₀) (List.ofFn X₀.val)) (finish X₀)).length := by
    rw [M.trace_output_count, ← List.length_reverse, output X₀, List.length_ofFn]
  exact omittedByExtent_eq_portBits _ happ.le _ (fun _t ht => (obs X₀).time_finish ht)
    (fun _t ht => ((obs X₀).time_finish ht).trans_le (finish_le X₀))

variable [Fintype Q] [Fintype Γ] [Fintype Λ]

include successful output finish_le same in
theorem class_saving_bound (q z a : ℕ)
    (hq : Fintype.card Q ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (ha : Fintype.card Γ ≤ 2 ^ a) (saving : ℝ)
    (hsaving : saving ≤
      ((omittedPortBits (d := d) (b := b) (M.portPaths (labels X₀) (List.ofFn X₀.val))
        (fun j => appendTime (M.motionTrace (labels X₀) (List.ofFn X₀.val)) (finish X₀) j.val)
        (obs X₀).times (obs X₀).finish R).card : ℝ) -
      (a : ℝ) * (if (obs X₀).start = 0 then 0 else (W : ℝ))) :
    (D.card : ℝ) ≤ (2 : ℝ) ^ ((d * d * b : ℕ) - saving + z + (N : ℝ) * q) := by
  let g := constantClass M D labels finish successful output obs finish_le X₀ same
  apply g.saving_card_bound (Function.Involutive.injective (tposOf_tposOf d b)) q z a N hq hz ha
    (obs X₀).run_cap saving
  rw [constantClass_omitted]
  simpa only [g, constantClass, integerSlab_card] using hsaving

end Classes
end AdaptiveTransfer.Enlarged
