import AdaptiveTransfer.EnlargedCounting
import AdaptiveTransfer.GetterNativeGeometry

/-! Motion and append geometry extracted from actual enlarged-rule runs.
The synthetic trace is only a projection of literal instructions; all of its
coordinates and append counts are proved to agree with the original run.
-/

namespace AdaptiveTransfer.Enlarged
open Transpose Finset MergeDepth BoundedNesting NativeRelations

variable {Q Γ Λ : Type*} {k p R : ℕ}

namespace System
variable (M : System Q Γ Λ k p R)

def motionTrace (label : Λ) (w : List Bool) : Trace k := fun t =>
  (M.instruction label w t).map fun i => (Dir.stay, fun h => (i.work h).2, i.append.isSome)

theorem trace_work (label : Λ) (w : List Bool) (h : Fin k) (t : ℕ) :
    (M.motionTrace label w).work h t = (M.run label w t).workPos h := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Trace.work_succ, ih, M.run_succ]
    simp only [Trace.workStep, motionTrace]
    cases hi : M.instruction label w t with
    | none => simp
    | some i => simp only [Option.map_some, Option.elim_some, applyInstruction, shift_eq_add_moveInt]

theorem trace_appends (label : Λ) (w : List Bool) (t : ℕ) :
    (M.motionTrace label w).appends t = (M.emitted label w t).isSome := by
  simp only [Trace.appends, motionTrace, emitted]
  cases M.instruction label w t <;> simp

theorem trace_output_count (label : Λ) (w : List Bool) (t : ℕ) :
    (appendList (M.motionTrace label w) t).length = (M.run label w t).outRev.length := by
  rw [M.count_eq_word]
  simp only [PrefixOutput.word, List.length_filterMap_eq_countP, List.countP_eq_length_filter, appendList]
  congr 1
  apply List.filter_congr
  intro u _
  exact M.trace_appends label w u

def portPaths (label : Λ) (w : List Bool) : Fin p → ℕ → ℤ := fun j t => (M.run label w t).ports j

theorem portPaths_walk (label : Λ) (w : List Bool) (j : Fin p) : IsWalk (M.portPaths label w j) :=
  M.port_unit label w j

theorem portPaths_zero (label : Λ) (w : List Bool) (j : Fin p) : M.portPaths label w j 0 = M.origins j := rfl

theorem live_of_instruction {label : Λ} {w : List Bool} {t : ℕ}
    (hi : M.instruction label w t ≠ none) : M.live label w t = true := by
  unfold instruction at hi
  split at hi
  · assumption
  · contradiction

/-- An actual successful prefix has completed exactly the demanded output by
the cap. This includes every halted correct run and slightly enlarges its set. -/
def OutputBy {P : ℕ} (π : Fin P → Fin P) (T : ℕ) (X : Fin P → Bool) (label : Λ) : Prop :=
  ∃ F ≤ T, (∀ t < F, M.instruction label (List.ofFn X) t ≠ none) ∧
    (M.run label (List.ofFn X) F).outRev.reverse = List.ofFn (fun j => X (π j))

end System

namespace System
variable (M : System Q Γ Λ 1 p R)

/-- Positive saving chooses an actual literal slab of the enlarged execution.
No native simulation or reconstructed-prefix premise is used. -/
theorem port_observation {d b a : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hp : 1 ≤ p)
    (hP : 4 * p ≤ d * d * b) (hc : 1 ≤ c)
    (hR : R ≤ (d * d * b) / (8 * p * Getter.portRunCap a p c))
    {X : Fin (d * d * b) → Bool} {label : Λ} {F : ℕ}
    (hF : F ≤ returnTime (d * d * b) c)
    (hout : (M.run label (List.ofFn X) F).outRev.reverse = List.ofFn (fun j => X (tposOf d b j)))
    (hsaving : 0 < Getter.portSaving d b a p c) :
    ∃ g : SlabObservation (M.motionTrace label (List.ofFn X)) (returnTime (d * d * b) c)
      (Getter.portSlabWidth (d * d * b) a p c) (Getter.portRunCap a p c),
      g.finish ≤ F ∧ Getter.portSaving d b a p c ≤
        ((Getter.omittedPortBits (d := d) (b := b) (M.portPaths label (List.ofFn X))
          (fun j => appendTime (M.motionTrace label (List.ofFn X)) F j.val)
          g.times g.finish R).card : ℝ) -
        (a : ℝ) * (if g.start = 0 then 0 else (Getter.portSlabWidth (d * d * b) a p c : ℝ)) := by
  classical
  let τ := M.motionTrace label (List.ofFn X)
  have happ : (appendList τ F).length = d * d * b := by
    rw [M.trace_output_count, ← List.length_reverse, hout, List.length_ofFn]
  have hPpos : 0 < d * d * b := by nlinarith
  have htime : (F : ℝ) ≤ 2 * c * (d * d * b : ℕ) := by
    have hh : (returnTime (d * d * b) c : ℝ) ≤ c * ((d * d * b : ℕ) + 1) := Nat.floor_le (by positivity)
    have hf : (F : ℝ) ≤ returnTime (d * d * b) c := by exact_mod_cast hF
    have hp' : (1 : ℝ) ≤ (d * d * b : ℕ) := by exact_mod_cast hPpos
    nlinarith
  have hot : StrictMono (fun j : Fin (d * d * b) => appendTime τ F j.val) := by
    intro i j hij
    exact appendTime_strictMonoOn τ F
      (by simpa only [Set.mem_Iio, happ] using i.isLt)
      (by simpa only [Set.mem_Iio, happ] using j.isLt) hij
  obtain ⟨ell, s, e, hse, he, _, hruns, hmargin⟩ := Getter.exists_port_slab_geometry
    hd hb ha hp hP hc hR (M.portPaths_walk label (List.ofFn X)) (τ.work_isWalk 0) hot
    (fun j => appendTime_lt τ F (by simpa only [happ] using j.isLt)) htime
  let C := selectedSlab (τ.work 0) (Getter.portSlabWidth (d * d * b) a p c) ell s e
  have hne : C.Nonempty := by
    by_contra hn
    have hemp := not_nonempty_iff_eq_empty.mp hn
    have hU : Getter.omittedPortBits (d := d) (b := b) (M.portPaths label (List.ofFn X))
        (fun j => appendTime τ F j.val) C F R = ∅ := by
      simp [Getter.omittedPortBits, outIn, hemp]
    change Getter.portSaving d b a p c ≤ ((Getter.omittedPortBits _ _ C _ _).card : ℝ) - _ at hmargin
    rw [hU, card_empty, Nat.cast_zero] at hmargin
    have hcost : 0 ≤ (a : ℝ) * (if s = 0 then 0 else (Getter.portSlabWidth (d * d * b) a p c : ℝ)) := by
      split_ifs <;> positivity
    linarith
  let g : SlabObservation τ (returnTime (d * d * b) c)
      (Getter.portSlabWidth (d * d * b) a p c) (Getter.portRunCap a p c) :=
    ⟨0, ell, s, e, hse, he.trans hF, hne, hruns⟩
  refine ⟨g, he, ?_⟩
  have heq : Getter.portBits (d * d * b) (M.portPaths label (List.ofFn X)) g.times g.finish R =
      Getter.portBits (d * d * b) (M.portPaths label (List.ofFn X)) g.times F R :=
    Getter.portBits_eq_of_caps _ (fun _t ht => g.time_finish ht) (fun _t ht => (g.time_finish ht).trans_le he)
  simp only [Getter.omittedPortBits, heq]
  exact hmargin

end System
end AdaptiveTransfer.Enlarged
