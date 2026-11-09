import CascadeObstruction.C5Completion
import CascadeObstruction.C5Regularity

/-! The concrete canonical-width C5 exclusion. All clock, simulation and
regularity obligations are discharged by the preceding constructive modules.
The only premises of the final theorem describe a data completion and its
nonempty correctness set. -/

namespace CascadeObstruction.C5

open Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
open TransposeFollowup.RegularMotion

set_option autoImplicit false

noncomputable def CorrectCompletion.nativeClock {g d : ℕ} (x : CorrectCompletion g d) :
    DyadicClock 18 (Transpose.inputLength d) (trace x.levels (entryBits d)).length :=
  { clock x.levels (entryBits d) (canonical_width_pos d) with
    root := by
      simpa only [canonical_length_eq x.dimension] using
        (clock x.levels (entryBits d) (canonical_width_pos d)).root }

noncomputable def CorrectCompletion.native {g d : ℕ} (x : CorrectCompletion g d) :
    NativeDyadicInstance 2 (max 1 (Nat.clog 2 (g + 1))) 18 d where
  machine := x.machine
  tape_count := rfl
  cell_bits := rfl
  correctSet := x.correctSet
  deficit := Transpose.inputLength d
  count := by
    simpa using Nat.mul_le_mul_left (2 ^ Transpose.inputLength d)
      (Nat.succ_le_of_lt x.card_bounds.1)
  correct := fun w hw =>
    ⟨(trace x.levels (entryBits d)).length, Compiler.haltsAt x.program w,
      x.correct_native w hw, ⟨x.nativeClock⟩⟩

theorem CorrectCompletion.time_bound {g d : ℕ} (x : CorrectCompletion g d) :
    ((trace x.levels (entryBits d)).length : ℝ) ≤ 36 * Transpose.inputLength d := by
  simpa only [canonical_length_eq x.dimension] using
    trace_time_bound x.levels (entryBits d) (canonical_width_pos d)

theorem CorrectCompletion.inputLength_pos {g d : ℕ} (x : CorrectCompletion g d) :
    0 < Transpose.inputLength d := by
  rw [← canonical_length_eq x.dimension]
  exact CascadeObstruction.C5.inputLength_pos _ (canonical_width_pos d)

/-- Every chosen family of concrete C5 completions has the complete native
regular-clock property. Correct-input and halting quantifiers are retained. -/
theorem completion_family_regular {g : ℕ} {ns : ℕ → ℕ}
    (xs : ∀ i, CorrectCompletion g (ns i)) :
    HasRegularRecursiveExecutions 1 2 (1 / 2) 18 1 ns
      (fun i => (xs i).machine) (fun i => (xs i).correctSet) (fun _ => rfl) := by
  refine ⟨0, ?_⟩
  intro φ _hφ _hN ws T _hmem hhalt _hP
  have hT : T = fun i => (trace (xs (φ i)).levels (entryBits (ns (φ i)))).length := by
    funext i
    exact ((xs (φ i)).haltsAt_iff (ws i) (T i)).mp (hhalt i)
  subst T
  refine ⟨fun i => (xs (φ i)).nativeClock, ?_⟩
  intro h
  have hc := clock_regular (K := fun i => (xs (φ i)).levels)
    (b := fun i => entryBits (ns (φ i))) (fun i => canonical_width_pos _) (workHead h)
  have he : (fun i m => workTraj (xs (φ i)).machine (ws i) m
      (Fin.cast (show 2 = (xs (φ i)).machine.k from rfl) h)) =
      fun i m => position (trace (xs (φ i)).levels (entryBits (ns (φ i)))) (workHead h) m := by
    funext i m
    change workTraj (xs (φ i)).machine (ws i) m h = _
    exact (xs (φ i)).work_trajectory (ws i) m h
  rw [he]
  exact hc

/-- A bound depending only on input size, uniformly over all source controllers
and local rules. Its only purpose is paying for the finite public clock. -/
def clockOverhead (d : ℕ) : ℝ := Nat.clog 2 (36 * Transpose.inputLength d + 1)

theorem clockOverhead_sublinear :
    Tendsto (fun d => clockOverhead d / Transpose.inputLength d) atTop (𝓝 0) := by
  apply clock_bits_div_inputLength_tendsto (c := 36) tendsto_id
  exact Filter.Eventually.of_forall fun d => by simp

theorem CorrectCompletion.native_state_bound {g d : ℕ} (x : CorrectCompletion g d) :
    (Nat.clog 2 (x.native.machine.q + 1) : ℝ) ≤
      (Nat.clog 2 (x.controller + 1) : ℝ) + clockOverhead d := by
  have ht : (trace x.levels (entryBits d)).length ≤ 36 * Transpose.inputLength d := by
    exact_mod_cast x.time_bound
  have hb := Compiler.state_bits_le x.program
  have hc := Nat.clog_mono_right 2 (Nat.add_le_add_right ht 1)
  have h : Nat.clog 2 ((Compiler.machine x.program).q + 1) ≤
      Nat.clog 2 (x.controller + 1) + Nat.clog 2 (36 * Transpose.inputLength d + 1) := by
    omega
  change (Nat.clog 2 ((Compiler.machine x.program).q + 1) : ℝ) ≤
    (Nat.clog 2 (x.controller + 1) : ℝ) + (Nat.clog 2 (36 * Transpose.inputLength d + 1) : ℝ)
  exact_mod_cast h

/-- Uniform positive controller-plus-real-deficit gap for the concrete C5
schedule, at canonical logarithmic width and every sufficiently large legal
dyadic dimension. No numerical value for the gap or threshold is asserted. -/
theorem uniform_c5_gap (g : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ x : CorrectCompletion g d,
      δ * Transpose.inputLength d ≤ (Nat.clog 2 (x.controller + 1) : ℝ) +
        realDeficit (Transpose.inputLength d) x.correctSet.ncard := by
  obtain ⟨δ, hδ, d₀, hgap⟩ := uniform_native_real_deficit_gap
    (fun d (x : CorrectCompletion g d) => x.native)
    (fun _ x => (Nat.clog 2 (x.controller + 1) : ℝ)) clockOverhead
    (by norm_num)
    (fun _ xs _ => completion_family_regular xs)
    (fun _ x => x.native_state_bound) clockOverhead_sublinear
  refine ⟨δ, hδ, d₀, fun d hd x => ?_⟩
  have hp : (0 : ℝ) < Transpose.inputLength d := by exact_mod_cast x.inputLength_pos
  exact (le_div_iff₀ hp).mp (hgap d hd x)

end CascadeObstruction.C5
