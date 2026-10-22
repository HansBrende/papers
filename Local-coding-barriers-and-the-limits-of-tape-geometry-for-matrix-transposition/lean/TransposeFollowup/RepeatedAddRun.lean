import TransposeFollowup.RepeatedAddBody

/-! The assembled finite machine performs the specified number of additions,
with an explicit native bound and no unimplemented body hypothesis. Input
loading and final removal of the preserved work words remain separate. -/

namespace TransposeFollowup.RepeatedAdd

open FixedTapeCompiler
open BinaryCompare (value)
set_option autoImplicit false

abbrev Word (x : List Bool) := {a : List Bool // a.length = x.length}

def update (x : List Bool) (_ : List Bool) (a : Word x) : Word x :=
  ⟨addWord a.val x, addWord_length a.val x a.property⟩

def loopFrame (x : List Bool) (pos : Port → ℤ) (a : Word x) :
    MicrocodeEmbedding.Frame Port := frame (ready [] a.val x) pos

theorem loop_state (x : List Bool) (pos : Port → ℤ)
    (pc : Microcode.DecrementFamily.Label) (fuel : List Bool) (a : Word x) :
    NativeCountedLoop.state (singleBinding .fuel).ports Label.counter (loopFrame x pos)
      (fun _ => pos .fuel) pc fuel a = cfg (.counter pc) (ready fuel a.val x) pos := by
  simp only [NativeCountedLoop.state, loopFrame, embed_counter]
  rfl

theorem resultState_word (x : List Bool) (n : ℕ) (fuel : List Bool) (a : Word x) :
    (NativeCountedLoop.resultState (update x) n fuel a).val = repeatWord x n a.val := by
  induction n generalizing fuel a with
  | zero => rfl
  | succ n ih =>
    simpa only [NativeCountedLoop.resultState, repeatWord, update] using
      ih (Counter.decrement fuel) (update x (Counter.decrement fuel) a)

theorem assembled_body (x : List Bool) (pos : Port → ℤ)
    (fuel : List Bool) (a : Word x) :
    ∃ t ≤ 18 * x.length + 31,
      Trace t
        (NativeCountedLoop.state (singleBinding .fuel).ports Label.counter (loopFrame x pos)
          (fun _ => pos .fuel) 11 fuel a)
        (NativeCountedLoop.state (singleBinding .fuel).ports Label.counter (loopFrame x pos)
          (fun _ => pos .fuel) 0 fuel (update x fuel a)) := by
  simpa only [loop_state, update] using body_trace fuel a.val x a.property pos

def budget (fuel x : List Bool) : ℕ :=
  Counter.value fuel * (18 * x.length + 31) + 8 * (Counter.value fuel + 1) + 4 * fuel.length

theorem repeated_add_trace (fuel a x : List Bool) (h : a.length = x.length)
    (pos : Port → ℤ) :
    ∃ t ≤ budget fuel x,
      Trace t (cfg (.counter 0) (ready fuel a x) pos)
        (cfg (.counter 12)
          (ready (List.replicate fuel.length true) (repeatWord x (Counter.value fuel) a) x) pos) := by
  obtain ⟨t, ht, htr⟩ := NativeCountedLoop.counted_trace (singleBinding .fuel).ports
    Label.counter program (loopFrame x pos) (fun _ => pos .fuel) (update x)
    fuel.length (18 * x.length + 31) counter_code (fun ys _ s => assembled_body x pos ys s)
    (Counter.value fuel) fuel (⟨a, h⟩ : Word x) rfl rfl
  have hcost := NativeCounter.native_sequence_budget (Counter.value fuel + 1) fuel
  refine ⟨t, ?_, ?_⟩
  · unfold budget
    omega
  · simpa only [loop_state, resultState_word,
      NativeCountedLoop.terminal_word (Counter.value fuel) fuel rfl] using htr

theorem native_repeated_add (fuel a x : List Bool) (h : a.length = x.length)
    (pos : Port → ℤ) (w : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget fuel x,
      Transpose.stepN nativeMachine w t
        ((cfg (.counter 0) (ready fuel a x) pos).denote nativeEncoding program inputPos outRev) =
        some ((cfg (.counter 12)
          (ready (List.replicate fuel.length true) (repeatWord x (Counter.value fuel) a) x) pos).denote
            nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine w
        ((cfg (.counter 12)
          (ready (List.replicate fuel.length true) (repeatWord x (Counter.value fuel) a) x) pos).denote
            nativeEncoding program inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := repeated_add_trace fuel a x h pos
  refine ⟨t, ht, ?_, ?_⟩
  · exact NativeMicrocode.trace_stepN nativeEncoding program w inputPos outRev htr
  · apply (NativeMicrocode.step_none_iff nativeEncoding program w inputPos outRev _).mpr
    simp [NativeMicrocode.Active, cfg, program, Microcode.DecrementFamily.program,
      Microcode.DecrementFamily.instruction, FinitePortBinding.instruction]

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U)
    (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (fuel a x : List Bool) (h : a.length = x.length) (pos : Port → ℤ)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget fuel x,
      Transpose.stepN (NativeMicrocode.machine encoding target) w t
        ((MicrocodeEmbedding.embed ports labels (cfg (.counter 0) (ready fuel a x) pos)
          outerFrame).denote encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.counter 12)
            (ready (List.replicate fuel.length true) (repeatWord x (Counter.value fuel) a) x) pos)
          outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := repeated_add_trace fuel a x h pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame w inputPos outRev hc htr⟩

theorem output_value (fuel a x : List Bool) (h : a.length = x.length) :
    value (repeatWord x (Counter.value fuel) a) =
      (value a + value fuel * value x) % 2 ^ x.length := by
  rw [repeatWord_value x _ a h, NativeCounter.word_value]

theorem output_value_exact (fuel a x : List Bool) (h : a.length = x.length)
    (hfit : value a + value fuel * value x < 2 ^ x.length) :
    value (repeatWord x (Counter.value fuel) a) = value a + value fuel * value x := by
  rw [output_value fuel a x h, Nat.mod_eq_of_lt hfit]

theorem zero_value (m : ℕ) : value (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, BinaryCompare.value_cons, ih]

/-- Connect the implemented nonnegative product to the existing signed
reference repeated-addition loop under a sufficient-width condition. -/
theorem reference_product (fuel x : List Bool)
    (hfit : value fuel * value x < 2 ^ x.length) :
    (value (repeatWord x (Counter.value fuel) (List.replicate x.length false)) : ℤ) =
      repeatedAdd (value x : ℤ) (value fuel) := by
  have hv := output_value_exact fuel (List.replicate x.length false) x (by simp)
    (by simpa only [zero_value, Nat.zero_add] using hfit)
  rw [hv, zero_value, Nat.zero_add, repeatedAdd_eq]
  norm_cast

end TransposeFollowup.RepeatedAdd
