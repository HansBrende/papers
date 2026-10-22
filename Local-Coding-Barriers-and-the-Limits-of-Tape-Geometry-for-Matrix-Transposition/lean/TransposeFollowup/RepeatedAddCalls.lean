import TransposeFollowup.RepeatedAddMachine

/-! Concrete call interfaces for the fixed repeated-addition controller. -/

namespace TransposeFollowup.RepeatedAdd

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

theorem embed_add (pc : BinaryCarry.Label) (a x r : Tape Bool) (b : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed addBinding.ports (Label.arithmetic false)
      (BinaryCarry.cfg pc a x r (fun i => pos (addBinding.ports i))).denote (frame b pos) =
      cfg (.arithmetic false pc) {b with acc := a, factor := x, scratch := r} pos := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    BinaryCarry.cfg cfg frame
  simp only [← addBinding.values_eq_extend]
  congr 2 <;> funext t <;> cases t <;> rfl

theorem embed_copy (pc : BinaryCarry.Label) (r z a : Tape Bool) (b : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports (Label.arithmetic true)
      (BinaryCarry.cfg pc r z a (fun i => pos (copyBinding.ports i))).denote (frame b pos) =
      cfg (.arithmetic true pc) {b with scratch := r, zero := z, acc := a} pos := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    BinaryCarry.cfg cfg frame
  simp only [← copyBinding.values_eq_extend]
  congr 2 <;> funext t <;> cases t <;> rfl

theorem embed_buffer (port : Port) (labels : NativeBuffer.Label → Label)
    (pc : NativeBuffer.Label) (word : Tape Bool) (b : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding port).ports labels
      (NativeBuffer.cfg pc word (fun _ => pos port)).denote (frame b pos) =
      cfg (labels pc) (b.set port word) pos := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    NativeBuffer.cfg Microcode.focus cfg frame
  simp only [← (singleBinding port).values_eq_extend]
  congr 2 <;> funext t <;> cases port <;> cases t <;> rfl

theorem embed_counter (pc : Microcode.DecrementFamily.Label) (fuel : List Bool)
    (b : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding .fuel).ports Label.counter
      (NativeCounter.cfg pc fuel (fun _ => pos .fuel)).denote (frame b pos) =
      cfg (.counter pc) {b with fuel := Counter.marked fuel} pos := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    NativeCounter.cfg Microcode.focus cfg frame
  simp only [← (singleBinding .fuel).values_eq_extend]
  congr 2 <;> funext t <;> cases t <;> rfl

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem jump_trace_to (target : Microcode.Program Port Label) (pc next : Label) (b : Bank) (pos : Port → ℤ)
    (h : target pc = .jump next) : OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) 1 (cfg pc b pos) (cfg next b pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem jump_trace (pc next : Label) (b : Bank) (pos : Port → ℤ)
    (h : program pc = .jump next) : Trace 1 (cfg pc b pos) (cfg next b pos) :=
  jump_trace_to program pc next b pos h

theorem arithmetic_call_to (target : Microcode.Program Port Label)
    (hc : ∀ pc, BinaryCarry.program pc ≠ .halt → BinaryCarry.program pc ≠ .reject →
      target (.arithmetic false pc) = MicrocodeEmbedding.instruction addBinding.ports
        (Label.arithmetic false) (BinaryCarry.program pc))
    (sub : Bool) (a x : List Bool) (h : a.length = x.length) (b : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 5 * x.length + 7,
      OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) t
        (cfg (.arithmetic false (.scan sub sub))
          {b with acc := BinaryCarry.marked a, factor := BinaryCarry.marked x, scratch := BinaryCarry.preparedOutput} pos)
        (cfg (.arithmetic false (.done (BinaryCarry.result sub sub a x).2))
          {b with acc := BinaryCarry.marked a, factor := BinaryCarry.marked x, scratch := BinaryCarry.marked ((BinaryCarry.result sub sub a x).1)} pos) := by
  obtain ⟨t, ht, htr⟩ := BinaryCarry.arithmetic_trace sub sub a x h
    (fun i => pos (addBinding.ports i))
  have he := MicrocodeEmbedding.trace_embed addBinding.ports (Label.arithmetic false)
    BinaryCarry.program target (frame b pos) hc htr
  refine ⟨t, by simpa [h] using ht, ?_⟩
  simpa only [embed_add] using he

theorem addition_call (a x : List Bool) (h : a.length = x.length) (b : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 5 * x.length + 7,
      Trace t
        (cfg (.arithmetic false (.scan false false))
          {b with acc := BinaryCarry.marked a, factor := BinaryCarry.marked x, scratch := BinaryCarry.preparedOutput} pos)
        (cfg (.arithmetic false (.done (BinaryCarry.result false false a x).2))
          {b with acc := BinaryCarry.marked a, factor := BinaryCarry.marked x, scratch := BinaryCarry.marked (addWord a x)} pos) :=
  arithmetic_call_to program (arithmetic_code false) false a x h b pos

theorem copy_call_to (target : Microcode.Program Port Label)
    (hc : ∀ pc, BinaryCarry.program pc ≠ .halt → BinaryCarry.program pc ≠ .reject →
      target (.arithmetic true pc) = MicrocodeEmbedding.instruction copyBinding.ports
        (Label.arithmetic true) (BinaryCarry.program pc))
    (r : List Bool) (b : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 5 * r.length + 7,
      OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) t
        (cfg (.arithmetic true (.scan false false))
          {b with scratch := BinaryCarry.marked r, zero := BinaryCarry.marked (List.replicate r.length false), acc := BinaryCarry.preparedOutput} pos)
        (cfg (.arithmetic true (.done false))
          {b with scratch := BinaryCarry.marked r, zero := BinaryCarry.marked (List.replicate r.length false), acc := BinaryCarry.marked r} pos) := by
  obtain ⟨t, ht, htr⟩ := BinaryCarry.arithmetic_trace false false r
    (List.replicate r.length false) (by simp) (fun i => pos (copyBinding.ports i))
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports (Label.arithmetic true)
    BinaryCarry.program target (frame b pos) hc htr
  refine ⟨t, ht, ?_⟩
  simpa only [embed_copy, copy_with_zero] using he

theorem copy_call (r : List Bool) (b : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 5 * r.length + 7,
      Trace t
        (cfg (.arithmetic true (.scan false false))
          {b with scratch := BinaryCarry.marked r, zero := BinaryCarry.marked (List.replicate r.length false), acc := BinaryCarry.preparedOutput} pos)
        (cfg (.arithmetic true (.done false))
          {b with scratch := BinaryCarry.marked r, zero := BinaryCarry.marked (List.replicate r.length false), acc := BinaryCarry.marked r} pos) :=
  copy_call_to program (arithmetic_code true) r b pos

theorem recycle_call_to (target : Microcode.Program Port Label)
    (hc : ∀ scratch pc, NativeBuffer.program pc ≠ .halt → NativeBuffer.program pc ≠ .reject →
      target (.clear scratch pc) = MicrocodeEmbedding.instruction (clearBinding scratch).ports
        (Label.clear scratch) (NativeBuffer.program pc))
    (scratch : Bool) (word : List Bool) (b : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 4 * word.length + 6,
      OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) t (cfg (.clear scratch (.erase 2))
        (b.set (if scratch then .scratch else .acc) (Counter.marked word)) pos)
        (cfg (.clear scratch .done)
          (b.set (if scratch then .scratch else .acc) BinaryCarry.preparedOutput) pos) := by
  obtain ⟨t, ht, htr⟩ := NativeBuffer.recycle_trace word
    (fun _ => pos (if scratch then .scratch else .acc))
  have he := MicrocodeEmbedding.trace_embed (clearBinding scratch).ports (Label.clear scratch)
    NativeBuffer.program target (frame b pos) (hc scratch) htr
  refine ⟨t, ht, ?_⟩
  simpa only [clearBinding, embed_buffer] using he

theorem recycle_call (scratch : Bool) (word : List Bool) (b : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 4 * word.length + 6,
      Trace t (cfg (.clear scratch (.erase 2))
        (b.set (if scratch then .scratch else .acc) (Counter.marked word)) pos)
        (cfg (.clear scratch .done)
          (b.set (if scratch then .scratch else .acc) BinaryCarry.preparedOutput) pos) :=
  recycle_call_to program clear_code scratch word b pos

end TransposeFollowup.RepeatedAdd
