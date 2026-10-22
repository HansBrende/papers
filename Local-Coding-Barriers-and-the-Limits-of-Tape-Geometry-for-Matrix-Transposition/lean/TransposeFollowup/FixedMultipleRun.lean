import TransposeFollowup.FixedMultipleMachine

/-! K charged calls to the existing in-place adder, with one charged
transfer per call and one final transfer. Fuel [true] is reused unchanged. -/

namespace TransposeFollowup.FixedMultiple

open FixedTapeCompiler
open RepeatedAdd (Port Bank ready repeatWord addWord)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem embed_call (K : ℕ) (i : Fin (K+1)) (pc : RepeatedAdd.Label) (b : Bank)
    (pos : Port → ℤ) (frame : MicrocodeEmbedding.Frame Port) :
    MicrocodeEmbedding.embed binding.ports (Label.call i) (RepeatedAdd.cfg pc b pos) frame =
      cfg (.call i pc) b pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg
  simp only [← binding.values_eq_extend]
  rfl

abbrev Trace (K : ℕ) :=
  OperationalTrace.Trace (NativeMicrocode.step (program K)) (NativeMicrocode.Active (program K))

theorem jump_trace (K : ℕ) (pc next : Label K) (b : Bank) (pos : Port → ℤ)
    (h : program K pc = .jump next) : Trace K 1 (cfg pc b pos) (cfg next b pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem single_call (K : ℕ) (i : Fin (K+1)) (hi : 0 < i.val)
    (a x : List Bool) (h : a.length = x.length) (pos : Port → ℤ) :
    ∃ t ≤ 18*x.length+51,
      Trace K t (cfg (.call i (.counter 0)) (ready [true] a x) pos)
        (cfg (.call i (.counter 12)) (ready [true] (addWord a x) x) pos) := by
  obtain ⟨t, ht, htr⟩ := RepeatedAdd.single_add_trace a x h pos
  have he := MicrocodeEmbedding.trace_embed binding.ports (Label.call i)
    RepeatedAdd.program (program K) (RepeatedAdd.frame (ready [true] a x) pos)
    (call_code K i hi) htr
  exact ⟨t, ht, by simpa only [embed_call] using he⟩

def budget (K m : ℕ) : ℕ := K*(18*m+52)+1

theorem iterate_trace (K k : ℕ) (hk : k ≤ K) (a x : List Bool)
    (h : a.length = x.length) (pos : Port → ℤ) :
    ∃ t ≤ budget k x.length,
      Trace K t (cfg (.call ⟨k, by omega⟩ (.counter 0)) (ready [true] a x) pos)
        (cfg .done (ready [true] (repeatWord x k a) x) pos) := by
  induction k generalizing a with
  | zero =>
    refine ⟨1, by simp [budget], ?_⟩
    exact jump_trace K _ _ _ _ (by simp [program])
  | succ k ih =>
    obtain ⟨t, ht, hc⟩ := single_call K ⟨k+1, by omega⟩ (by simp) a x h pos
    have hj := jump_trace K (.call ⟨k+1, by omega⟩ (.counter 12))
      (.call ⟨k, by omega⟩ (.counter 0)) (ready [true] (addWord a x) x) pos
      (by simp [program])
    obtain ⟨u, hu, hr⟩ := ih (by omega) (addWord a x) (RepeatedAdd.addWord_length a x h)
    refine ⟨t+(1+u), ?_, trace_trans hc (trace_trans hj hr)⟩
    dsimp [budget] at *
    nlinarith

theorem multiple_trace (K : ℕ) (a x : List Bool) (h : a.length = x.length) (pos : Port → ℤ) :
    ∃ t ≤ budget K x.length,
      Trace K t (cfg (start K) (ready [true] a x) pos)
        (cfg .done (ready [true] (repeatWord x K a) x) pos) :=
  iterate_trace K K le_rfl a x h pos

theorem native_multiple (K : ℕ) (a x : List Bool) (h : a.length = x.length)
    (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget K x.length,
      Transpose.stepN (nativeMachine K) input t
        ((cfg (start K) (ready [true] a x) pos).denote (nativeEncoding K) (program K) inputPos outRev) =
        some ((cfg .done (ready [true] (repeatWord x K a) x) pos).denote
          (nativeEncoding K) (program K) inputPos outRev) ∧
      Transpose.step (nativeMachine K) input
        ((cfg .done (ready [true] (repeatWord x K a) x) pos).denote
          (nativeEncoding K) (program K) inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := multiple_trace K a x h pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN (nativeEncoding K) (program K) input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding K) (program K) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (K : ℕ)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label K → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program K pc ≠ .halt → program K pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program K pc))
    (a x : List Bool) (h : a.length = x.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget K x.length,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start K) (ready [true] a x) pos) frame).denote
          encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (ready [true] (repeatWord x K a) x) pos) frame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := multiple_trace K a x h pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program K) target
    frame input inputPos outRev hc htr⟩

end TransposeFollowup.FixedMultiple
