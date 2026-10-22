import TransposeFollowup.NativeCounter

/-! Counted native loops with a physical binary counter. The body must have
an actual active trace, including its return/branch instructions. Counter
loading and final cleanup are separate explicit obligations. -/

namespace TransposeFollowup.NativeCountedLoop

open FixedTapeCompiler
open Microcode.DecrementFamily (Label program)
set_option autoImplicit false
variable {U J S C : Type*}

theorem trace_trans {step : C → C} {active : C → Prop} {n m : ℕ} {a b c : C}
    (h : OperationalTrace.Trace step active n a b)
    (g : OperationalTrace.Trace step active m b c) :
    OperationalTrace.Trace step active (n + m) a c := by
  induction h with
  | refl => simpa using g
  | cons ha tr ih => simpa [Nat.succ_add] using OperationalTrace.Trace.cons ha (ih g)

def resultState (update : List Bool → S → S) : ℕ → List Bool → S → S
  | 0, _, s => s
  | n + 1, xs, s => resultState update n (Counter.decrement xs)
      (update (Counter.decrement xs) s)

noncomputable def state (ports : Fin 1 ↪ U) (labels : Label → J)
    (frame : S → MicrocodeEmbedding.Frame U) (pos : Fin 1 → ℤ)
    (pc : Label) (xs : List Bool) (s : S) : NativeMicrocode.Config U J :=
  MicrocodeEmbedding.embed ports labels (NativeCounter.cfg pc xs pos).denote (frame s)

theorem terminal_word (n : ℕ) (xs : List Bool) (h : Counter.value xs = n) :
    Counter.wordAfter (n + 1) xs = List.replicate xs.length true := by
  induction n generalizing xs with
  | zero =>
    have hz := Counter.zero_replicate xs ((Counter.value_zero_iff xs).mp h)
    change Counter.decrement xs = _
    conv_lhs => rw [hz]
    exact (Counter.zero_functions xs.length).1
  | succ n ih =>
    have hn : Counter.isZero xs = false := by
      cases he : Counter.isZero xs
      · rfl
      · have hv := (Counter.value_zero_iff xs).mpr he
        omega
    have hv : Counter.value (Counter.decrement xs) = n := by
      have hd := Counter.decrement_value xs hn
      omega
    simpa only [Counter.wordAfter, Counter.length_decrement] using ih (Counter.decrement xs) hv

/-- Each nonzero counter check invokes the supplied native body once.
The final zero check reports underflow and leaves the word wrapped to all
ones. Its cost is included; no body runs after that final check. -/
theorem counted_trace
    (ports : Fin 1 ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (frame : S → MicrocodeEmbedding.Frame U) (pos : Fin 1 → ℤ)
    (update : List Bool → S → S) (width bodyBudget : ℕ)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (body : ∀ xs, xs.length = width → ∀ s,
      ∃ t ≤ bodyBudget,
        OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) t
          (state ports labels frame pos 11 xs s)
          (state ports labels frame pos 0 xs (update xs s)))
    (n : ℕ) (xs : List Bool) (s : S) (hv : Counter.value xs = n)
    (hw : xs.length = width) :
    ∃ t ≤ 2 * Counter.totalCost (n + 1) xs + n * bodyBudget,
      OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) t
        (state ports labels frame pos 0 xs s)
        (state ports labels frame pos 12 (Counter.wordAfter (n + 1) xs)
          (resultState update n xs s)) := by
  induction n generalizing xs s with
  | zero =>
    have hz : Counter.isZero xs = true := (Counter.value_zero_iff xs).mp hv
    obtain ⟨t, ht, htr⟩ := NativeCounter.decrement_trace xs pos
    have lifted := MicrocodeEmbedding.trace_embed ports labels program target (frame s) hc htr
    refine ⟨t, ?_, ?_⟩
    · simpa [Counter.totalCost] using ht
    · simpa [state, NativeCounter.returnLabel, hz, Counter.wordAfter, resultState] using lifted
  | succ n ih =>
    have hz : Counter.isZero xs = false := by
      cases h : Counter.isZero xs
      · rfl
      · have hzero := (Counter.value_zero_iff xs).mpr h
        omega
    have hv' : Counter.value (Counter.decrement xs) = n := by
      have hdec := Counter.decrement_value xs hz
      omega
    have hw' : (Counter.decrement xs).length = width :=
      (Counter.length_decrement xs).trans hw
    obtain ⟨a, ha, ta⟩ := NativeCounter.decrement_trace xs pos
    have tc : OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) a
        (state ports labels frame pos 0 xs s)
        (state ports labels frame pos 11 (Counter.decrement xs) s) := by
      simpa [state, NativeCounter.returnLabel, hz] using
        MicrocodeEmbedding.trace_embed ports labels program target (frame s) hc ta
    obtain ⟨b, hb, tb⟩ := body (Counter.decrement xs) hw' s
    obtain ⟨c, hc', tr⟩ := ih (Counter.decrement xs) (update (Counter.decrement xs) s) hv' hw'
    refine ⟨a + (b + c), ?_, ?_⟩
    · change a + (b + c) ≤ 2 * (Counter.stepCost xs +
        Counter.totalCost (n + 1) (Counter.decrement xs)) + (n + 1) * bodyBudget
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [Counter.wordAfter, resultState] using trace_trans tc (trace_trans tb tr)

theorem native_loop {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 1 ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (frame : S → MicrocodeEmbedding.Frame U) (pos : Fin 1 → ℤ)
    (update : List Bool → S → S) (width bodyBudget : ℕ)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (body : ∀ xs, xs.length = width → ∀ s,
      ∃ t ≤ bodyBudget,
        OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) t
          (state ports labels frame pos 11 xs s)
          (state ports labels frame pos 0 xs (update xs s)))
    (xs : List Bool) (s : S) (hw : xs.length = width)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ (Counter.value xs) * bodyBudget + 8 * (Counter.value xs + 1) + 4 * width,
      Transpose.stepN (NativeMicrocode.machine encoding target) w t
        ((state ports labels frame pos 0 xs s).denote encoding target inputPos outRev) =
        some ((state ports labels frame pos 12 (Counter.wordAfter (Counter.value xs + 1) xs)
          (resultState update (Counter.value xs) xs s)).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := counted_trace ports labels target frame pos update width bodyBudget
    hc body (Counter.value xs) xs s rfl hw
  have hcost := NativeCounter.native_sequence_budget (Counter.value xs + 1) xs
  refine ⟨t, by omega, NativeMicrocode.trace_stepN encoding target w inputPos outRev htr⟩

end TransposeFollowup.NativeCountedLoop
