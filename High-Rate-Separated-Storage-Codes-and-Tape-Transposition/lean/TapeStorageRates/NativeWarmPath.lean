import TapeStorageRates.NativeWindow

/-! The same frozen step, now based at an arbitrary configuration. The default
origin is definitionally the series' usual zero-origin run and motion trace. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

abbrev runAt (M : TM) (w : List Bool) (o : Option (Config M)) (t : ℕ) : Config M :=
  match o with | none => run M w t | some c => (next M w)^[t] c

abbrev inputAt (M : TM) (w : List Bool) (o : Option (Config M)) (t : ℕ) :=
  readInput w (runAt M w o t).inPos

abbrev workAt (M : TM) (w : List Bool) (o : Option (Config M)) (t : ℕ) (j : Fin M.k) :=
  (runAt M w o t).work j ((runAt M w o t).workPos j)

abbrev transFrom (M : TM) (w : List Bool) (o : Option (Config M)) (t : ℕ) :=
  lookup M (readInput w) (runAt M w o t)

abbrev traceFrom (M : TM) (w : List Bool) (o : Option (Config M)) : Trace M.k := fun t =>
  (transFrom M w o t).map fun z => (z.2.1, fun j => (z.2.2.1 j).2, z.2.2.2.isSome)

theorem traceFrom_none (M : TM) (w : List Bool) : traceFrom M w none = trace M w := rfl

theorem runAt_succ (M : TM) (w : List Bool) (o : Option (Config M)) (t : ℕ) :
    runAt M w o (t+1) = next M w (runAt M w o t) := by
  cases o with
  | none => rfl
  | some c => exact Function.iterate_succ_apply' ..

theorem after_from_action {M : TM} {w : List Bool} {o : Option (Config M)} {t : ℕ} {z : Action M}
    (h : transFrom M w o t = some z) :
    runAt M w o (t+1) = commit (runAt M w o t) z := by
  rw [runAt_succ,next,step_eq_lookup,show lookup M (readInput w) (runAt M w o t) = some z from h]
  rfl

theorem traceFrom_none_iff (M : TM) (w : List Bool) (o : Option (Config M)) (t : ℕ) :
    traceFrom M w o t = none ↔ transFrom M w o t = none := Option.map_eq_none_iff

theorem step_runAt_none_iff (M : TM) (w : List Bool) (o : Option (Config M)) (t : ℕ) :
    step M w (runAt M w o t) = none ↔ transFrom M w o t = none := by
  rw [step_eq_lookup]
  exact Option.map_eq_none_iff

theorem transFrom_frozen {M : TM} {w : List Bool} {o : Option (Config M)} {t u : ℕ}
    (dead : transFrom M w o t = none) (hu : t ≤ u) : transFrom M w o u = none := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hu
  have f (n : ℕ) : runAt M w o (t+n) = runAt M w o t := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [← Nat.add_assoc,runAt_succ,ih,next,step_eq_lookup]
      change (Option.map _ (transFrom M w o t)).getD _ = _
      rw [dead]
      rfl
  change lookup M (readInput w) (runAt M w o (t+q)) = none
  rw [f]
  exact dead

theorem stepsFrom_alive {M : TM} {w : List Bool} {o : Option (Config M)} (a n : ℕ)
    (alive : ∀ i<n, transFrom M w o (a+i) ≠ none) :
    stepN M w n (runAt M w o a) = some (runAt M w o (a+n)) := by
  have it (i : ℕ) : (next M w)^[i] (runAt M w o a) = runAt M w o (a+i) := by
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply',ih,← runAt_succ,Nat.add_assoc]
  apply (stepN_eq_some_iff ..).2
  refine ⟨?_,it n⟩
  intro i hi
  rw [it,step_eq_lookup]
  exact fun h => alive _ hi (Option.map_eq_none_iff.mp h)

theorem haltsFrom_iff {M : TM} {w : List Bool} {c : Config M} {n : ℕ} :
    (traceFrom M w (some c)).HaltsAt n ↔
      ∃ d, stepN M w n c = some d ∧ step M w d = none := by
  constructor
  · rintro ⟨live,stop⟩
    refine ⟨runAt M w (some c) n,?_,?_⟩
    · have go := stepsFrom_alive (M := M) (w := w) (o := some c) 0 n (by
        intro i hi
        rw [Nat.zero_add]
        exact fun h => live i hi ((traceFrom_none_iff ..).mpr h))
      rwa [show runAt M w (some c) 0 = c from rfl, Nat.zero_add] at go
    · rw [step_eq_lookup]
      exact Option.map_eq_none_iff.mpr ((traceFrom_none_iff ..).mp stop)
  · rintro ⟨d,hn,stop⟩
    obtain ⟨alive,endAt⟩ := (stepN_eq_some_iff ..).mp hn
    refine ⟨?_,?_⟩
    · intro i hi e
      apply alive i hi
      rw [step_eq_lookup]
      exact Option.map_eq_none_iff.mpr ((traceFrom_none_iff ..).mp e)
    · apply (traceFrom_none_iff ..).mpr
      rw [step_eq_lookup] at stop
      have eq' : runAt M w (some c) n = d := endAt
      simpa [transFrom,eq'] using Option.map_eq_none_iff.mp stop

end TapeStorageRates.Native
