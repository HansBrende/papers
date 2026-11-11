import TapeStorageRates.NativeTypicalResources
import TapeStorageRates.NativeCoarseGeometry
import Mathlib

/-! The clock and head geometry of the actual aligned native compiler.
The terminal complete batch and the stationary drain are retained. Input
and work heads share one interface; no shadow estimate is assumed.
-/

namespace AdaptiveTransfer.TransferClock
open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting
open TapeStorageRates TapeStorageRates.Native

def batchLength (s : ℕ) : ℕ := 10 * s + 1

def sourceClock (s t u : ℕ) : ℕ := min ((u / batchLength s + 1) * s) (t - 1)

theorem batchLength_pos (s : ℕ) : 0 < batchLength s := by unfold batchLength; omega

theorem sourceClock_mono (s t : ℕ) : Monotone (sourceClock s t) := by
  intro u v huv
  exact min_le_min (Nat.mul_le_mul_right s (Nat.add_le_add_right
    (Nat.div_le_div_right huv) 1)) le_rfl

theorem sourceClock_lt {s t : ℕ} (ht : 1 ≤ t) (u : ℕ) : sourceClock s t u < t := by
  exact (min_le_right _ _).trans_lt (by omega)

theorem sourceClock_batch {s j i t : ℕ} (hi : i < batchLength s) :
    sourceClock s t (batchLength s * j + i) = min ((j + 1) * s) (t - 1) := by
  simp only [sourceClock, Nat.mul_add_div (batchLength_pos s), Nat.div_eq_of_lt hi,
    Nat.add_zero]

def configHead {M : TM} (c : Config M) : Option (Fin M.k) → ℤ
  | none => c.inPos
  | some h => c.workPos h

theorem headPosition_eq_config (M : TM) (w : List Bool) (h : Option (Fin M.k)) (u : ℕ) :
    headPosition (trace M w) h u = configHead (run M w u) h := by
  cases h with
  | none => exact (inPos_eq_input (M := M) (w := w) u).symm
  | some h => exact (workPos_eq_work (M := M) (w := w) h u).symm

theorem headPosition_isWalk {k : ℕ} (τ : Trace k) (h : Option (Fin k)) :
    IsWalk (headPosition τ h) := by
  cases h with
  | none => exact τ.abs_input_succ_sub_le
  | some h => exact τ.work_isWalk h

/-- Every actual boundary records the source head in the block beginning
at its corresponding physical head. -/
theorem boundary_head_offset {M : TM} {s u : ℕ} {w : List Bool}
    (hs : 0 < s) {c : Config M} {draining : Bool}
    (hb : Boundary hs w u c draining) (h : Option (Fin M.k)) :
    headPosition (trace (machine M hs) w) h u ≤ configHead c h ∧
      configHead c h < headPosition (trace (machine M hs) w) h u + s := by
  obtain ⟨r, ai, aw, out, hrun, _, hi, hw, _⟩ := hb
  rw [headPosition_eq_config]
  change run (machine M hs) w u = _ at hrun
  rw [hrun]
  cases h with
  | none =>
    simp only [configHead, Frame.native, anchored, add_zero]
    rw [hi]
    have hh := r.oi.isLt
    omega
  | some h =>
    simp only [configHead, Frame.native, anchored, add_zero]
    rw [hw h]
    have hh := (r.ow h).isLt
    omega

theorem actual_batch_boundary {M : TM} {s t j : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (hj : j ≤ t / s) :
    Boundary hs w (batchLength s * j) (run M w (j * s)) false := by
  apply full_blocks M hs w j
  intro i hi
  apply H.1 i
  have hjs : j * s ≤ t := (Nat.mul_le_mul_right s hj).trans (Nat.div_mul_le_self t s)
  omega

/-- The extra terminal batch ends at the actual halted source configuration,
even when the source time is divisible by s. -/
theorem actual_terminal_boundary {M : TM} {s t : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) :
    Boundary hs w (batchLength s * (t / s + 1)) (run M w t) true := by
  let j := t / s
  let u := t % s
  have split : j * s + u = t := Nat.div_add_mod' _ _
  have hu : u < s := Nat.mod_lt _ hs
  have start := actual_batch_boundary hs H (j := j) le_rfl
  have z := advance_of_halt (stepsFrom_alive (M := M) (w := w) (o := none) (j * s) u
    (fun i hi => H.1 _ (by omega)))
    (by rw [split, step_runAt_none_iff]; exact H.2) (s - (u + 1))
  rw [show u + (s - (u + 1)) + 1 = s by omega, split] at z
  simpa only [batchLength, Nat.mul_succ, z] using boundary_step_from hs w none _ _ start

/-- The existing compiler's actual halting trace has exactly floor(t/s)+1
complete batches followed by its s-step drain. -/
theorem actual_trace_factor {M : TM} {s t : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) :
    ∃ (as : List (Descriptor M.k)) (r : Fin s), as.length = t / s + 1 ∧
      trace (machine M hs) w = replay r as := by
  have hh := (haltsAt_iff_trace _).mp (simulates_halt M hs w H).1
  obtain ⟨as, r, hlen, he⟩ := halting_trace hs w hh
  refine ⟨as, r, ?_, he⟩
  apply Nat.eq_of_mul_eq_mul_left (batchLength_pos s)
  change (10 * s + 1) * as.length = (10 * s + 1) * (t / s + 1)
  omega

/-- Every physical point in a genuine complete batch lies in its anchor's
three-block window. This includes the final complete batch. -/
theorem actual_batch_window {M : TM} {s t j i : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (hj : j ≤ t / s) (hi : i < batchLength s)
    (h : Option (Fin M.k)) :
    let anchor := headPosition (trace (machine M hs) w) h (batchLength s * j)
    anchor - s ≤ headPosition (trace (machine M hs) w) h (batchLength s * j + i) ∧
      headPosition (trace (machine M hs) w) h (batchLength s * j + i) < anchor + 2 * s := by
  obtain ⟨as, r, hlen, he⟩ := actual_trace_factor hs H
  have hj' : j < as.length := by omega
  have hb := replay_head_batch hs r as h j hj' i hi.le
  have hzero := replay_head_batch hs r as h j hj' 0 (Nat.zero_le _)
  simp only [fineOffset_zero hs, add_zero] at hzero
  dsimp only
  rw [he, show batchLength s = 10 * s + 1 from rfl, hb, hzero]
  have hw := fineOffset_window hs (headCarry as[j] h) i hi
  omega

theorem actual_batch_source_offset {M : TM} {s t j : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (hj : j ≤ t / s) (h : Option (Fin M.k)) :
    headPosition (trace (machine M hs) w) h (batchLength s * j) ≤
      headPosition (trace M w) h (j * s) ∧
    headPosition (trace M w) h (j * s) <
      headPosition (trace (machine M hs) w) h (batchLength s * j) + s := by
  simpa only [headPosition_eq_config] using
    boundary_head_offset hs (actual_batch_boundary hs H hj) h

/-- The final drain is physically stationary at the boundary reached after
the extra complete terminal batch. -/
theorem actual_drain_stationary {M : TM} {s t : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (h : Option (Fin M.k)) (i : ℕ) :
    headPosition (trace (machine M hs) w) h (batchLength s * (t / s + 1) + i) =
      headPosition (trace (machine M hs) w) h (batchLength s * (t / s + 1)) := by
  obtain ⟨as, r, hlen, he⟩ := actual_trace_factor hs H
  rw [he, ← hlen]
  have hh := replay_head_drain hs r as h i
  have hzero := replay_head_drain hs r as h 0
  simpa only [batchLength, Nat.add_zero] using hh.trans hzero.symm

end AdaptiveTransfer.TransferClock
