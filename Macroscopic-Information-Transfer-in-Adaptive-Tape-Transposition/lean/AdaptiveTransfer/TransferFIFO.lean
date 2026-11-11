import AdaptiveTransfer.TransferClockShadow
import TapeStorageRates.TraceCriterion
import MergeDepth.HCStarQ91

/-! Actual output-count and append-ordinal transport for the aligned native
compiler. Repeated bit values cause no ambiguity: roots are indexed by
append ordinal. Pending output occupies fewer than s entries in control.
-/

namespace AdaptiveTransfer.TransferFIFO
open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth
open TapeStorageRates TapeStorageRates.Native AdaptiveTransfer.TransferClock

def outputCount (M : TM) (w : List Bool) (u : ℕ) : ℕ := (run M w u).outRev.length

noncomputable def sourceRoot (M : TM) (w : List Bool) (t i : ℕ) : ℕ :=
  appendTime (trace M w) t i

noncomputable def simulatorRoot (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool) (t i : ℕ) : ℕ :=
  sourceRoot (machine M hs) w (alignedTime s t) i

theorem outputCount_mono (M : TM) (w : List Bool) : Monotone (outputCount M w) :=
  fun _ _ h => outRev_length_mono w h

theorem outputCount_add_le (M : TM) (w : List Bool) (u n : ℕ) :
    outputCount M w (u + n) ≤ outputCount M w u + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change (run M w (u + (n + 1))).outRev.length ≤ _
    rw [← Nat.add_assoc, outRev_length_succ]
    change outputCount M w (u + n) + _ ≤ _
    split_ifs <;> omega

theorem outputCount_le_add_of_time_le (M : TM) (w : List Bool) {r u n : ℕ}
    (hr : r ≤ u + n) : outputCount M w r ≤ outputCount M w u + n :=
  (outputCount_mono M w hr).trans (outputCount_add_le M w u n)

/-- The literal pending word gives the complete boundary discrepancy. -/
theorem boundary_output_counts {M : TM} {s u : ℕ} {w : List Bool}
    (hs : 0 < s) {c : Config M} {draining : Bool} (hb : Boundary hs w u c draining) :
    outputCount (machine M hs) w u ≤ c.outRev.length ∧
      c.outRev.length < outputCount (machine M hs) w u + s := by
  obtain ⟨r, ai, aw, out, hrun, _, _, _, ho⟩ := hb
  have hh := congrArg List.length ho
  simp only [List.length_append, List.length_reverse, length_offsetWord] at hh
  have he : outputCount (machine M hs) w u = out.length := by
    unfold outputCount
    change run (machine M hs) w u = _ at hrun
    rw [hrun]
    rfl
  have hr := r.pendingLen.isLt
  omega

/-- Counts at every completed physical boundary, including the boundary
after the extra complete terminal batch. -/
theorem actual_boundary_output_counts {M : TM} {s t j : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (hj : j ≤ t / s + 1) :
    outputCount (machine M hs) w (batchLength s * j) ≤ outputCount M w (min (j * s) t) ∧
      outputCount M w (min (j * s) t) < outputCount (machine M hs) w (batchLength s * j) + s := by
  by_cases hj' : j ≤ t / s
  · have hjs : j * s ≤ t := (Nat.mul_le_mul_right s hj').trans (Nat.div_mul_le_self t s)
    simpa only [min_eq_left hjs, outputCount] using
      boundary_output_counts hs (actual_batch_boundary hs H hj')
  · have he : j = t / s + 1 := by omega
    have hts : t ≤ (t / s + 1) * s := by
      have hm := Nat.mod_lt t hs
      have hd := Nat.div_add_mod' t s
      nlinarith
    rw [he, min_eq_right hts]
    exact boundary_output_counts hs (actual_terminal_boundary hs H)

theorem actual_final_output_count {M : TM} {s t : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) :
    outputCount (machine M hs) w (alignedTime s t) = outputCount M w t :=
  congrArg List.length (simulates_halt M hs w H).2

/-- By any physical step, all emitted ordinals have already been generated
by the source through its projected step, inclusive. -/
theorem actual_output_no_future {M : TM} {s t u : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t) (hu : u < alignedTime s t) :
    outputCount (machine M hs) w (u + 1) ≤ outputCount M w (sourceClock s t u + 1) := by
  by_cases hb : u < batchLength s * (t / s + 1)
  · let j := u / batchLength s
    have hj : j ≤ t / s := by
      have hh := (Nat.div_lt_iff_lt_mul (batchLength_pos s)).mpr
        (by simpa only [Nat.mul_comm] using hb)
      dsimp [j]
      omega
    have huend : u + 1 ≤ batchLength s * (j + 1) := by
      have hm := Nat.mod_lt u (batchLength_pos s)
      have he := Nat.div_add_mod u (batchLength s)
      dsimp [j]
      nlinarith
    have hend := (actual_boundary_output_counts hs H (j := j + 1) (by omega)).1
    have htime : min ((j + 1) * s) t ≤ sourceClock s t u + 1 := by
      unfold sourceClock
      change min ((j + 1) * s) t ≤ min ((j + 1) * s) (t - 1) + 1
      omega
    exact (outputCount_mono _ _ huend).trans (hend.trans (outputCount_mono M w htime))
  · rw [sourceClock_drain hs (by omega), Nat.sub_add_cancel ht]
    rw [← actual_final_output_count hs H]
    exact outputCount_mono _ _ (by omega)

/-- The exact pre-step and inclusive look-ahead bounds. The first is the
2s-1 bill used by activation guards; it is stronger than the inclusive one. -/
theorem actual_output_lookahead {M : TM} {s t u : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (_hu : u < alignedTime s t) :
    outputCount M w (sourceClock s t u) ≤ outputCount (machine M hs) w u + (2 * s - 1) ∧
      outputCount M w (sourceClock s t u + 1) ≤ outputCount (machine M hs) w u + 2 * s := by
  have hpre : outputCount M w (sourceClock s t u) ≤
      outputCount (machine M hs) w u + (2 * s - 1) := by
    by_cases hb : u < batchLength s * (t / s + 1)
    · let j := u / batchLength s
      have hj : j ≤ t / s := by
        have hh := (Nat.div_lt_iff_lt_mul (batchLength_pos s)).mpr
          (by simpa only [Nat.mul_comm] using hb)
        dsimp [j]
        omega
      have hjs : j * s ≤ t := (Nat.mul_le_mul_right s hj).trans (Nat.div_mul_le_self t s)
      have hstart := (actual_boundary_output_counts hs H (j := j) (by omega)).2
      rw [min_eq_left hjs] at hstart
      have hmono := outputCount_mono (machine M hs) w
        (show batchLength s * j ≤ u from Nat.mul_div_le u (batchLength s))
      have htime : sourceClock s t u ≤ j * s + s := by
        have hh : sourceClock s t u ≤ (j + 1) * s := min_le_left _ _
        nlinarith
      have hgrowth := outputCount_le_add_of_time_le M w htime
      omega
    · have hb' : batchLength s * (t / s + 1) ≤ u := by omega
      have hstart := (actual_boundary_output_counts hs H (j := t / s + 1) le_rfl).2
      have hts : t ≤ (t / s + 1) * s := by
        have hm := Nat.mod_lt t hs
        have hd := Nat.div_add_mod' t s
        nlinarith
      rw [min_eq_right hts] at hstart
      have hmono := outputCount_mono (machine M hs) w hb'
      have hsrc := outputCount_mono M w (show sourceClock s t u ≤ t from (min_le_right _ _).trans (Nat.sub_le _ _))
      omega
  refine ⟨hpre, ?_⟩
  have hgrowth := outputCount_add_le M w (sourceClock s t u) 1
  omega

/-- Existing roots are literal appends with exact before/after counts. -/
theorem sourceRoot_counts (M : TM) (w : List Bool) {t i : ℕ} (hi : i < outputCount M w t) :
    sourceRoot M w t i < t ∧ outputCount M w (sourceRoot M w t i) = i ∧
      outputCount M w (sourceRoot M w t i + 1) = i + 1 := by
  have hi' : i < (appendList (trace M w) t).length := by
    simpa only [outputCount, outRev_length_eq_appendList] using hi
  have hlt := appendTime_lt (trace M w) t hi'
  have hcount := appendCount_appendTime (trace M w) t hi'
  have hpre : outputCount M w (sourceRoot M w t i) = i := by
    unfold outputCount
    rw [outRev_length_eq_appendList]
    change ((appendList (trace M w) (sourceRoot M w t i)).length : ℤ) = i at hcount
    exact_mod_cast hcount
  have hmem : sourceRoot M w t i ∈ appendList (trace M w) t := by
    rw [sourceRoot, appendTime_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  have hflag : (trace M w).appends (sourceRoot M w t i) = true := (List.mem_filter.mp hmem).2
  refine ⟨hlt, hpre, ?_⟩
  unfold outputCount
  rw [outRev_length_succ, outBit_isSome_eq, hflag]
  simpa only [ite_true, outputCount] using congrArg (· + 1) hpre

/-- The source append order is exactly the order of the actual output counter. -/
theorem sourceRoot_lt_iff_count (M : TM) (w : List Bool) {t i c : ℕ}
    (hi : i < outputCount M w t) :
    sourceRoot M w t i < c ↔ i < outputCount M w c := by
  have hh := sourceRoot_counts M w hi
  constructor
  · intro hc
    have hm := outputCount_mono M w (show sourceRoot M w t i + 1 ≤ c by omega)
    rw [hh.2.2] at hm
    omega
  · intro hc
    by_contra hbad
    have hm := outputCount_mono M w (show c ≤ sourceRoot M w t i by omega)
    rw [hh.2.1] at hm
    omega

theorem sourceRoot_strictMono (M : TM) (w : List Bool) (t : ℕ) :
    StrictMono (fun i : Fin (outputCount M w t) => sourceRoot M w t i.val) := by
  intro i j hij
  apply (sourceRoot_lt_iff_count M w i.isLt).mpr
  rw [(sourceRoot_counts M w j.isLt).2.1]
  exact hij

/-- The same ordinal is defined in the actual simulator, and its source
root lies no later than the projected simulator root. -/
theorem actual_sourceRoot_le_clock {M : TM} {s t i : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t) (hi : i < outputCount M w t) :
    simulatorRoot M hs w t i < alignedTime s t ∧
      sourceRoot M w t i ≤ sourceClock s t (simulatorRoot M hs w t i) := by
  have hisim : i < outputCount (machine M hs) w (alignedTime s t) := by
    rw [actual_final_output_count hs H]
    exact hi
  obtain ⟨hu, hbefore, hafter⟩ := sourceRoot_counts (machine M hs) w hisim
  have hsrc := sourceRoot_counts M w hi
  refine ⟨hu, ?_⟩
  have hgenerated := actual_output_no_future hs ht H hu
  change outputCount (machine M hs) w (sourceRoot (machine M hs) w (alignedTime s t) i + 1) ≤ _ at hgenerated
  rw [hafter] at hgenerated
  change i + 1 ≤ outputCount M w (sourceClock s t (simulatorRoot M hs w t i) + 1) at hgenerated
  by_contra hbad
  have htime : sourceClock s t (simulatorRoot M hs w t i) + 1 ≤ sourceRoot M w t i := by omega
  have hh := outputCount_mono M w htime
  rw [hsrc.2.1] at hh
  omega

/-- Literal append-ordinal look-ahead, including the sharper pre-step
bound required to pay at most 2s-1 roots at a source activation. -/
theorem actual_ordinal_lookahead {M : TM} {s t i : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (hi : i < outputCount M w t) :
    outputCount M w (sourceClock s t (simulatorRoot M hs w t i)) ≤ i + (2 * s - 1) ∧
      outputCount M w (sourceClock s t (simulatorRoot M hs w t i) + 1) ≤ i + 2 * s := by
  have hisim : i < outputCount (machine M hs) w (alignedTime s t) := by
    rw [actual_final_output_count hs H]
    exact hi
  have hh := sourceRoot_counts (machine M hs) w hisim
  have hb := actual_output_lookahead hs H hh.1
  rw [hh.2.1] at hb
  exact hb

theorem actual_clock_lt_future_root {M : TM} {s t i : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (hfuture : i + 2 * s < outputCount M w t) :
    sourceClock s t (simulatorRoot M hs w t i) < sourceRoot M w t (i + 2 * s) := by
  have hi : i < outputCount M w t := by omega
  have hlook := (actual_ordinal_lookahead hs H hi).2
  have hroot := sourceRoot_counts M w hfuture
  by_contra hbad
  have htime : sourceRoot M w t (i + 2 * s) + 1 ≤
      sourceClock s t (simulatorRoot M hs w t i) + 1 := by omega
  have hh := outputCount_mono M w htime
  rw [hroot.2.2] at hh
  omega

end AdaptiveTransfer.TransferFIFO
