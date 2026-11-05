import TapeStorageRates.PrefixCompiler
import TapeStorageRates.NativeWarm

/-! # Uniform slowdown on all halting inputs -/

namespace TapeStorageRates.Prefix

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

set_option autoImplicit false

def time (s t : ℕ) : ℕ :=
  if t < 2*s then t else 2*s + ((10*s+1)*((t-2*s)/s+1)+s)

theorem time_le_eleven {s : ℕ} (hs : 0 < s) (t : ℕ) : time s t ≤ 11*t := by
  unfold time
  split
  · omega
  · rename_i h
    let n := (t-2*s)/s
    have hmul : n*s ≤ t-2*s := Nat.div_mul_le_self _ _
    have hn : n ≤ n*s := Nat.le_mul_of_pos_right _ hs
    have ht : n*s + 2*s ≤ t := by omega
    change 2*s+((10*s+1)*(n+1)+s) ≤ 11*t
    nlinarith

private theorem complete {N : TM} {w : List Bool} {t : ℕ} {f : Config N}
    (h : stepN N w t (init N) = some f) (hstop : step N w f = none) :
    HaltsAt N w t ∧ run N w t = f := by
  obtain ⟨ha, he⟩ := (stepN_init_eq_some_iff t f).mp h
  exact ⟨⟨ha, (step_run_eq_none_iff _).mp (he ▸ hstop)⟩, he⟩

/-- The switched machine halts with the correct output at the stated exact time, including
inputs that halt inside the direct prefix or exactly at the switch. -/
theorem simulates_halt (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool) {t : ℕ}
    (hh : HaltsAt M w t) :
    HaltsAt (machine M hs) w (time s t) ∧
      (run (machine M hs) w (time s t)).outRev = (run M w t).outRev := by
  have hh' := (step_run_eq_none_iff (M := M) (w := w) t).mpr hh.2
  have hsour := (stepN_init_eq_some_iff t (run M w t)).mpr ⟨hh.1, rfl⟩
  by_cases ht : t < 2*s
  · have hc := direct_prefix hs w ht.le hsour
    simp [ht] at hc
    have hstop := step_direct hs w (⟨t,ht⟩ : Fin (2*s)) (run M w t)
    rw [hh'] at hstop
    obtain ⟨hhalt, hr⟩ := complete hc hstop
    simpa [time, ht, hr] using (show HaltsAt (machine M hs) w t ∧
      (run (machine M hs) w t).outRev = (run M w t).outRev from ⟨hhalt, congrArg Config.outRev hr⟩)
  · let c := run M w (2*s)
    have hp : stepN M w (2*s) (init M) = some c := (stepN_init_eq_some_iff _ _).mpr
      ⟨fun j hj => hh.1 j (by omega), rfl⟩
    have hn : 2*s + (t-2*s) = t := by omega
    have htail : stepN M w (t-2*s) c = some (run M w t) := by
      have h := TransposeFollowup.SequentialFive.stepN_add M w (2*s) (t-2*s) (init M)
      rw [hn, hp, hsour] at h
      exact h.symm
    obtain ⟨f, hf, hstop, hout⟩ := Native.warm_simulates_halt M hs w c (run M w t) (t-2*s) htail hh'
    have hp' := direct_prefix hs w le_rfl hp
    simp only [lt_self_iff_false, dite_false] at hp'
    have full : stepN (machine M hs) w (time s t) (init (machine M hs)) = some (core hs f) := by
      simp only [time, ht, ↓reduceIte]
      rw [TransposeFollowup.SequentialFive.stepN_add, hp']
      simp only [Option.bind_some, stepN_core, hf, Option.map_some]
    obtain ⟨ha, he⟩ := complete full (by rw [step_core, hstop]; rfl)
    exact ⟨ha, (congrArg Config.outRev he).trans hout⟩

/-- The direct prefix does not create halting runs. -/
theorem halts_iff (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool) :
    (∃ t, HaltsAt (machine M hs) w t) ↔ ∃ t, HaltsAt M w t := by
  constructor
  · rintro ⟨T, hT⟩
    by_contra bad
    have all (i : ℕ) : transAt M w i ≠ none := by
      intro h
      have E : ∃ t, (trace M w) t = none := ⟨i, (trace_eq_none_iff _).mpr h⟩
      exact bad ⟨_, (haltsAt_iff_trace _).mpr ((trace M w).haltsAt_haltTime E)⟩
    let f := run (machine M hs) w T
    have haltP : step (machine M hs) w f = none := (step_run_eq_none_iff _).mpr hT.2
    have runP := (stepN_init_eq_some_iff T f).mpr ⟨hT.1, rfl⟩
    by_cases ht : T < 2*s
    · have src := (stepN_init_eq_some_iff T (run M w T)).mpr ⟨fun i _ => all i, rfl⟩
      have hs' := direct_prefix hs w ht.le src
      rw [runP] at hs'
      simp [ht] at hs'
      rw [hs', step_direct] at haltP
      exact all T ((step_run_eq_none_iff _).mp (Option.map_eq_none_iff.mp haltP))
    · let c := run M w (2*s)
      have src : stepN M w (2*s) (init M) = some c :=
        (stepN_init_eq_some_iff _ _).mpr ⟨fun i _ => all i, rfl⟩
      have hp := direct_prefix hs w le_rfl src
      simp only [lt_self_iff_false, dite_false] at hp
      have htail := TransposeFollowup.SequentialFive.stepN_add (machine M hs) w (2*s) (T-2*s)
        (init (machine M hs))
      rw [show 2*s+(T-2*s) = T by omega, runP, hp, Option.bind_some, stepN_core] at htail
      cases he : stepN (Native.machine M hs) w (T-2*s) (Native.warmSeed M hs c) with
      | none => simp [he] at htail
      | some z =>
        simp [he] at htail
        rw [htail, step_core] at haltP
        obtain ⟨n, d, hd, hdead⟩ := (Native.warm_halts_iff M hs w c).mp
          ⟨T-2*s, z, he, Option.map_eq_none_iff.mp haltP⟩
        have hsour : stepN M w (2*s+n) (init M) = some d := by
          rw [TransposeFollowup.SequentialFive.stepN_add, src]
          exact hd
        exact bad ⟨_, (complete hsour hdead).1⟩
  · rintro ⟨t, ht⟩
    exact ⟨_, (simulates_halt M hs w ht).1⟩

end TapeStorageRates.Prefix
