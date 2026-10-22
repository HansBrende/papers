import TransposeFollowup.RowConsumerMachine

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem jump_trace (pc next : Label) (row unit : List Bool) (s : Work) (pos : Port → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc row unit s pos) (cfg next row unit s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem embed_rewind (pc : NativeSealBack.Label) (w : Tape Bool) (row unit : List Bool)
    (s : Work) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (singleBinding .stream).ports Label.rewind
      (NativeSealBack.cfg pc w (fun _ => z)).denote (frame row unit s pos)=
      cfg (.rewind pc) row unit {s with stream:=w} (Function.update pos .stream z) := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus cfg frame
  simp only [← (singleBinding .stream).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_copy (pc : NativeMappedCopy.Label) (index : Tape Bool) (row unit : List Bool)
    (s : Work) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports Label.copy
      (NativeMappedCopy.cfg pc (Counter.marked (List.replicate unit.length false)) index
        (fun t => pos (copyBinding.ports t))) (frame row unit s pos)=
      cfg (.copy pc) row unit {s with index:=index} pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg cfg frame
  simp only [← copyBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

def sourceWord (b : Bool) (row index : List Bool) := if b then index else row

theorem embed_append (b : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (row unit index : List Bool) (pre : List (Sym Bool)) (s : Work) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (appendBinding b).ports (Label.append b)
      (NativeMappedAppend.cfg pc (Counter.marked (sourceWord b row index)) ⟨pre,[]⟩
        ![pos (if b then .index else .rowIndex),z]).denote
      (frame row unit {s with index:=Counter.marked index} pos)=
      cfg (.append b pc) row unit {s with index:=Counter.marked index,pre:=pre}
        (Function.update pos .output z) := by
  unfold MicrocodeEmbedding.embed NativeMappedAppend.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus2 Microcode.focus cfg frame
  simp only [← (appendBinding b).values_eq_extend]
  cases b <;> congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_increment (pc : RepeatedAdd.Label) (row unit index : List Bool)
    (s : Work) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed addBinding.ports Label.increment
      (RepeatedAdd.cfg pc (RepeatedAdd.ready [true] index unit) (fun p => pos (addPort p)))
      (frame row unit s pos)=
      cfg (.increment pc) row unit {s with index:=Counter.marked index} pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← addBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_erase_stream (pc : NativeErase.Label) (w : Tape Bool) (row unit : List Bool)
    (s : Work) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (singleBinding .stream).ports (Label.erase false)
      (NativeErase.cfg pc w (fun _ => z)).denote (frame row unit s pos)=
      cfg (.erase false pc) row unit {s with stream:=w} (Function.update pos .stream z) := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus cfg frame
  simp only [← (singleBinding .stream).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_erase_index (pc : NativeErase.Label) (w : Tape Bool) (row unit : List Bool)
    (s : Work) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding .index).ports (Label.erase true)
      (NativeErase.cfg pc w (fun _ => pos .index)).denote (frame row unit s pos)=
      cfg (.erase true pc) row unit {s with index:=w} pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus cfg frame
  simp only [← (singleBinding .index).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem rewind_call (row unit flags : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 2*flags.length+4, Trace t
      (cfg (.rewind .back) row unit {s with stream:=RowStream.closedTape flags} pos)
      (cfg (.rewind .done) row unit {s with stream:=Counter.marked flags}
        (Function.update pos .stream (pos .stream-flags.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeClosedStream.rewind_trace flags (fun _ => pos .stream)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .stream).ports Label.rewind
    NativeSealBack.program program (frame row unit s pos) rewind_code htr
  exact ⟨t,ht,by simpa only [embed_rewind,Function.update_eq_self] using he⟩

theorem copy_call (row unit : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 6*unit.length+14, Trace t
      (cfg (.copy (.init (.erase 0))) row unit {s with index:=⟨[],[]⟩} pos)
      (cfg (.copy (.seal .done)) row unit {s with index:=Counter.marked (List.replicate unit.length false)} pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id (List.replicate unit.length false)
    (fun j => pos (copyBinding.ports j))
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports Label.copy
    (NativeMappedCopy.program id) program (frame row unit s pos) copy_code htr
  exact ⟨t,by simpa using ht,by simpa only [List.map_id,embed_copy] using he⟩

theorem append_call (b : Bool) (row unit index : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 4*(sourceWord b row index).length+5, Trace t
      (cfg (.append b 0) row unit {s with index:=Counter.marked index} pos)
      (cfg (.append b 7) row unit
        {s with index:=Counter.marked index,pre:=(symbols (sourceWord b row index)).reverse++s.pre}
        (Function.update pos .output (pos .output+(sourceWord b row index).length))) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedAppend.append_trace id (sourceWord b row index) s.pre
    ![pos (if b then .index else .rowIndex),pos .output]
  have he := MicrocodeEmbedding.trace_embed (appendBinding b).ports (Label.append b)
    (Microcode.MappedAppendFamily.program id) program
    (frame row unit {s with index:=Counter.marked index} pos) (append_code b) htr
  have hpos : NativeMappedAppend.finalPositions
      ![pos (if b then .index else .rowIndex),pos .output] (sourceWord b row index).length=
      ![pos (if b then .index else .rowIndex),pos .output+(sourceWord b row index).length] := by
    funext j; fin_cases j <;> simp [NativeMappedAppend.finalPositions]
  rw [hpos] at he
  exact ⟨t,ht,by simpa only [List.map_id,embed_append,Function.update_eq_self] using he⟩

theorem increment_call (row unit index : List Bool) (h : index.length=unit.length)
    (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 18*unit.length+51, Trace t
      (cfg (.increment (.counter 0)) row unit {s with index:=Counter.marked index} pos)
      (cfg (.increment (.counter 12)) row unit {s with index:=Counter.marked (RepeatedAdd.addWord index unit)} pos) := by
  obtain ⟨t,ht,htr⟩ := RepeatedAdd.single_add_trace index unit h (fun p => pos (addPort p))
  have he := MicrocodeEmbedding.trace_embed addBinding.ports Label.increment
    RepeatedAdd.program program (frame row unit s pos) increment_code htr
  exact ⟨t,ht,by simpa only [embed_increment] using he⟩

theorem erase_stream_call (row unit flags : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 2*flags.length+3, Trace t
      (cfg (.erase false 4) row unit {s with stream:=RowStream.closedTape flags} pos)
      (cfg (.erase false 0) row unit {s with stream:=⟨[],[]⟩}
        (Function.update pos .stream (pos .stream-flags.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeClosedStream.erase_trace flags (fun _ => pos .stream)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .stream).ports (Label.erase false)
    NativeErase.program program (frame row unit s pos) (erase_code false) htr
  exact ⟨t,ht,by simpa only [embed_erase_stream,Function.update_eq_self] using he⟩

theorem erase_index_call (row unit index : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 4*index.length+4, Trace t
      (cfg (.erase true 2) row unit {s with index:=Counter.marked index} pos)
      (cfg (.erase true 0) row unit {s with index:=⟨[],[]⟩} pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace index (fun _ => pos .index)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .index).ports (Label.erase true)
    NativeErase.program program (frame row unit s pos) (erase_code true) htr
  exact ⟨t,ht,by simpa only [embed_erase_index] using he⟩

end TransposeFollowup.RowConsumer
