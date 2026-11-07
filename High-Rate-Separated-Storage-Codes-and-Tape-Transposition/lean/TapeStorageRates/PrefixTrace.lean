import TapeStorageRates.PrefixTime

/-! # Full trace support after a direct prefix -/

namespace TapeStorageRates.Prefix

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

set_option autoImplicit false

private def dirCode : Dir → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2

private theorem decode_dir (d : Dir) : Native.direction (dirCode d) = d := by cases d <;> rfl

private def encodeMotion {k : ℕ} (m : Motion k) : Native.Descriptor k :=
  ((dirCode m.1, fun j => dirCode (m.2.1 j)), m.2.2)

private def decodeMotion {k : ℕ} (v : Native.Descriptor k) : Motion k :=
  (Native.direction v.1.1, fun j => Native.direction (v.1.2 j), v.2)

private def prepend {k n : ℕ} (p : Fin n → Option (Native.Descriptor k)) (tail : Trace k) :
    Trace k := fun t => if ht : t < n then (p ⟨t,ht⟩).map decodeMotion else tail (t-n)

/-- Equality on the tail includes every native movement and the time at which the trace first
reports halt. The proof allows an arbitrary starting configuration of the aligned machine. -/
theorem trace_core_after {M : TM} {s : ℕ} (hs : 0 < s) (w : List Bool) (t : ℕ)
    {c : Config (Native.machine M hs)} (ht : run (machine M hs) w t = core hs c) (i : ℕ) :
    trace (machine M hs) w (t+i) = Native.traceFrom (Native.machine M hs) w (some c) i := by
  have eqrun (j : ℕ) : run (machine M hs) w (t+j) =
      core hs (Native.runAt (Native.machine M hs) w (some c) j) := by
    induction j with
    | zero => exact ht
    | succ j ih =>
      rw [← Nat.add_assoc, run_succ, Native.runAt_succ, ih]
      unfold next
      rw [step_core]
      cases step (Native.machine M hs) w (Native.runAt (Native.machine M hs) w (some c) j) <;> rfl
  change (Native.lookup (machine M hs) (readInput w) (run (machine M hs) w (t+i))).map _ = _
  rw [eqrun]
  exact motion_core hs w _

/-- The entire direct prefix adds at most a factor exponential in s. The containing set works
for variable output lengths as well as a fixed length. -/
theorem source_support (M : TM) {s : ℕ} (hs : 0 < s) (U : ℕ) :
    ∃ S : Finset (Trace M.k),
      S.card ≤ (1+2*3^(M.k+1))^(2*s) * (s*(1+2*3^(M.k+1))^(U/s+1)+1) ∧
      ∀ w t, HaltsAt M w t → t ≤ U → trace (machine M hs) w ∈ S := by
  classical
  obtain ⟨tails, hsize, hmem⟩ := Native.replay_support_variable (k := M.k) s (U/s+1)
  let empty : Trace M.k := fun _ => none
  let tails' := insert empty tails
  let choices := (univ : Finset (Fin (2*s) → Option (Native.Descriptor M.k))) ×ˢ tails'
  refine ⟨choices.image (fun z => prepend z.1 z.2), ?_, ?_⟩
  · apply card_image_le.trans
    rw [show choices.card = Fintype.card (Fin (2*s) → Option (Native.Descriptor M.k)) *
      tails'.card by simp [choices]]
    apply Nat.mul_le_mul _ ((card_insert_le empty tails).trans (Nat.add_le_add_right hsize 1))
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_option, Native.card_descriptor, Nat.add_comm _ 1]
  · intro w t hh hU
    let tr := trace (machine M hs) w
    let p := fun j : Fin (2*s) => (tr j).map encodeMotion
    have pre (j : Fin (2*s)) : (p j).map decodeMotion = tr j := by
      dsimp only [p]
      cases h : tr j with
      | none => rfl
      | some v => simp [encodeMotion, decodeMotion, decode_dir]
    suffices h : ∃ tail ∈ tails', ∀ i, tr (2*s+i) = tail i by
      obtain ⟨tail, hin, heq⟩ := h
      refine mem_image.mpr ⟨(p,tail), mem_product.mpr ⟨mem_univ _,hin⟩, ?_⟩
      funext l
      by_cases hl : l < 2*s
      · simpa only [prepend, hl, ↓reduceDIte] using pre ⟨l,hl⟩
      · change (if hh' : l < 2*s then _ else tail (l-2*s)) = tr l
        simp only [hl, ↓reduceDIte]
        simpa only [Nat.add_sub_of_le (Nat.le_of_not_gt hl)] using (heq (l-2*s)).symm
    by_cases ht : t < 2*s
    · refine ⟨empty, mem_insert_self _ _, fun i => ?_⟩
      have hsim := (simulates_halt M hs w hh).1
      have e : time s t = t := by simp [time, ht]
      rw [e] at hsim
      exact (trace_eq_none_iff _).mpr (transAt_of_le_of_none hsim.2 (by omega))
    · let c := run M w (2*s)
      have hsour : stepN M w t (init M) = some (run M w t) :=
        (stepN_init_eq_some_iff t _).mpr ⟨hh.1, rfl⟩
      have hp : stepN M w (2*s) (init M) = some c :=
        (stepN_init_eq_some_iff _ _).mpr ⟨fun j hj => hh.1 j (by omega),rfl⟩
      have htail : stepN M w (t-2*s) c = some (run M w t) := by
        have h := TransposeFollowup.SequentialFive.stepN_add M w (2*s) (t-2*s) (init M)
        rw [Nat.add_sub_of_le (Nat.le_of_not_gt ht), hp, hsour] at h
        exact h.symm
      obtain ⟨as, r, hlen, _, he⟩ := Native.warm_trace_of_halt M hs w c (run M w t) (t-2*s)
        htail ((step_run_eq_none_iff _).mpr hh.2)
      refine ⟨Native.replay r as, mem_insert_of_mem (hmem r as ?_), ?_⟩
      · rw [hlen]
        exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) _
      · have h' := direct_prefix hs w le_rfl hp
        simp only [lt_self_iff_false, dite_false] at h'
        have hstart := ((stepN_init_eq_some_iff _ _).mp h').2
        intro i
        exact (trace_core_after hs w (2*s) hstart i).trans (congrFun he i)

end TapeStorageRates.Prefix
