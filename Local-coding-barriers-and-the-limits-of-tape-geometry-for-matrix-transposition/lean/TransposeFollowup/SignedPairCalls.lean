import TransposeFollowup.SignedPairMachine

/-! Actual call traces in the signed-pair controller, with explicit frames. -/

namespace TransposeFollowup.SignedPair

open FixedTapeCompiler
open CopyMachine (Tape)
open BinaryCompare (Result)
set_option autoImplicit false

theorem embed_left (pc : BinaryCarry.Label) (a d l : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed leftBinding.ports (Label.add false)
      (BinaryCarry.cfg pc a d l (fun i => pos (leftBinding.ports i))).denote (frame s pos) =
      cfg (.add false pc) {s with a := a, d := d, left := l} pos := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    BinaryCarry.cfg cfg frame
  simp only [← leftBinding.values_eq_extend]
  congr 2 <;> funext t <;> cases t <;> rfl

theorem embed_right (pc : BinaryCarry.Label) (c b r : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed rightBinding.ports (Label.add true)
      (BinaryCarry.cfg pc c b r (fun i => pos (rightBinding.ports i))).denote (frame s pos) =
      cfg (.add true pc) {s with c := c, b := b, right := r} pos := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    BinaryCarry.cfg cfg frame
  simp only [← rightBinding.values_eq_extend]
  congr 2 <;> funext t <;> cases t <;> rfl

theorem embed_compare (pc : BinaryCompare.Label) (l r : Tape Bool) (s : Bank)
    (pos : Port → ℤ) :
    MicrocodeEmbedding.embed compareBinding.ports Label.compare
      (BinaryCompare.cfg pc l r (fun i => pos (compareBinding.ports i))).denote (frame s pos) =
      cfg (.compare pc) {s with left := l, right := r} pos := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    BinaryCompare.cfg cfg frame
  simp only [← compareBinding.values_eq_extend]
  congr 2 <;> funext t <;> cases t <;> rfl

theorem embed_buffer (port : Port) (labels : NativeBuffer.Label → Label)
    (pc : NativeBuffer.Label) (word : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding port).ports labels
      (NativeBuffer.cfg pc word (fun _ => pos port)).denote (frame s pos) =
      cfg (labels pc) (s.set port word) pos := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    NativeBuffer.cfg Microcode.focus cfg frame
  simp only [← (singleBinding port).values_eq_extend]
  congr 2 <;> funext t <;> cases port <;> cases t <;> rfl

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program pc = .jump next) : Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem left_call (a d : List Bool) (h : a.length = d.length) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 5 * d.length + 7,
      Trace t
        (cfg (.add false (.scan false false))
          {s with a := BinaryCarry.marked a, d := BinaryCarry.marked d, left := BinaryCarry.preparedOutput} pos)
        (cfg (.add false (.done (BinaryCarry.result false false a d).2))
          {s with a := BinaryCarry.marked a, d := BinaryCarry.marked d, left := BinaryCarry.marked (RepeatedAdd.addWord a d)} pos) := by
  obtain ⟨t, ht, htr⟩ := BinaryCarry.arithmetic_trace false false a d h
    (fun i => pos (leftBinding.ports i))
  have he := MicrocodeEmbedding.trace_embed leftBinding.ports (Label.add false)
    BinaryCarry.program program (frame s pos) (add_code false) htr
  refine ⟨t, by simpa [h] using ht, ?_⟩
  simpa only [embed_left, RepeatedAdd.addWord] using he

theorem right_call (c b : List Bool) (h : c.length = b.length) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 5 * b.length + 7,
      Trace t
        (cfg (.add true (.scan false false))
          {s with c := BinaryCarry.marked c, b := BinaryCarry.marked b, right := BinaryCarry.preparedOutput} pos)
        (cfg (.add true (.done (BinaryCarry.result false false c b).2))
          {s with c := BinaryCarry.marked c, b := BinaryCarry.marked b, right := BinaryCarry.marked (RepeatedAdd.addWord c b)} pos) := by
  obtain ⟨t, ht, htr⟩ := BinaryCarry.arithmetic_trace false false c b h
    (fun i => pos (rightBinding.ports i))
  have he := MicrocodeEmbedding.trace_embed rightBinding.ports (Label.add true)
    BinaryCarry.program program (frame s pos) (add_code true) htr
  refine ⟨t, by simpa [h] using ht, ?_⟩
  simpa only [embed_right, RepeatedAdd.addWord] using he

theorem compare_call (l r : List Bool) (h : l.length = r.length) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 5 * l.length + 6,
      Trace t (cfg (.compare (.scan .equal))
        {s with left := BinaryCompare.marked l, right := BinaryCompare.marked r} pos)
        (cfg (.compare (.done (BinaryCompare.numeric .equal (BinaryCompare.value l)
            (BinaryCompare.value r))))
          {s with left := BinaryCompare.marked l, right := BinaryCompare.marked r} pos) := by
  obtain ⟨t, ht, htr⟩ := BinaryCompare.comparison_trace l r h
    (fun i => pos (compareBinding.ports i))
  have he := MicrocodeEmbedding.trace_embed compareBinding.ports Label.compare
    BinaryCompare.program program (frame s pos) compare_code htr
  exact ⟨t, ht, by simpa only [embed_compare] using he⟩

theorem recycle_call (right : Bool) (r : Result) (word : List Bool) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 4 * word.length + 6,
      Trace t (cfg (.clear right r (.erase 2))
        (s.set (if right then .right else .left) (Counter.marked word)) pos)
        (cfg (.clear right r .done)
          (s.set (if right then .right else .left) BinaryCarry.preparedOutput) pos) := by
  obtain ⟨t, ht, htr⟩ := NativeBuffer.recycle_trace word
    (fun _ => pos (if right then .right else .left))
  have he := MicrocodeEmbedding.trace_embed (clearBinding right).ports (Label.clear right r)
    NativeBuffer.program program (frame s pos) (clear_code right r) htr
  refine ⟨t, ht, ?_⟩
  simpa only [clearBinding, embed_buffer] using he

end TransposeFollowup.SignedPair
