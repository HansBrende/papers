import TransposeFollowup.RowConsumerLoop

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem positions_stream (pos : Port → ℤ) (r : ℤ) :
    Function.update pos .stream (pos .stream+r)=positions pos r 0 := by
  funext p; cases p <;> simp [positions]

def initial (flags : List Bool) (pre : List (Sym Bool)) : Work :=
  ⟨RowStream.closedTape flags,⟨[],[]⟩,pre⟩

def final (pre : List (Sym Bool)) : Work := ⟨⟨[],[]⟩,⟨[],[]⟩,pre⟩

def zeroWord (unit : List Bool) := List.replicate unit.length false

def output (row unit flags : List Bool) := encoded row unit flags (zeroWord unit)

def budget (m : ℕ) (flags : List Bool) : ℕ :=
  flags.length*(18*m+58)+flags.count true*(8*m+12)+10*m+30

theorem prepare_trace (row unit flags : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 2*flags.length+6*unit.length+20, Trace t
      (cfg start row unit (initial flags pre) pos)
      (cfg .scan row unit (work [] flags (zeroWord unit) pre)
        (positions pos (-(flags.length : ℤ)) 0)) := by
  obtain ⟨a,ha,ta⟩ := rewind_call row unit flags (initial flags pre) pos
  simp only [sub_eq_add_neg,positions_stream] at ta
  let s1 : Work := ⟨Counter.marked flags,⟨[],[]⟩,pre⟩
  let p1 := positions pos (-(flags.length : ℤ)) 0
  have ja := jump_trace (.rewind .done) (.copy (.init (.erase 0))) row unit s1 p1 rfl
  obtain ⟨b,hb,tb⟩ := copy_call row unit s1 p1
  let s2 : Work := ⟨Counter.marked flags,Counter.marked (zeroWord unit),pre⟩
  have jb := jump_trace (.copy (.seal .done)) .scan row unit s2 p1 rfl
  exact ⟨a+1+b+1,by omega,trace_trans (trace_trans (trace_trans ta ja) tb) jb⟩

theorem finish_trace (row unit flags index : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 2*flags.length+4*index.length+10, Trace t
      (cfg .scan row unit (work flags [] index pre) pos)
      (cfg .done row unit (final pre) (positions pos (-(flags.length : ℤ)) 0)) := by
  have rd := read_stop row unit flags index pre pos
  let s0 := work flags [] index pre
  obtain ⟨a,ha,ta⟩ := erase_stream_call row unit flags s0 pos
  have hs : {s0 with stream:=RowStream.closedTape flags}=s0 := by simp [s0,work,cursor_final]
  rw [hs] at ta
  simp only [sub_eq_add_neg,positions_stream] at ta
  let s1 : Work := ⟨⟨[],[]⟩,Counter.marked index,pre⟩
  let p1 := positions pos (-(flags.length : ℤ)) 0
  have ja := jump_trace (.erase false 0) (.erase true 2) row unit s1 p1 rfl
  obtain ⟨b,hb,tb⟩ := erase_index_call row unit index s1 p1
  have jb := jump_trace (.erase true 0) .done row unit (final pre) p1 rfl
  exact ⟨1+a+1+b+1,by omega,trace_trans (trace_trans (trace_trans (trace_trans rd ta) ja) tb) jb⟩

theorem complete_trace (row unit flags : List Bool) (hr : row.length=unit.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ budget unit.length flags, Trace t
      (cfg start row unit (initial flags pre) pos)
      (cfg .done row unit (final ((symbols (output row unit flags)).reverse++pre))
        (positions pos (-(flags.length : ℤ)) (output row unit flags).length)) := by
  obtain ⟨a,ha,ta⟩ := prepare_trace row unit flags pre pos
  let p1 := positions pos (-(flags.length : ℤ)) 0
  have hz : (zeroWord unit).length=unit.length := List.length_replicate ..
  obtain ⟨b,hb,tb⟩ := loop_trace row unit [] flags (zeroWord unit) hr hz pre p1
  simp only [List.nil_append] at tb
  let pre1 := (symbols (output row unit flags)).reverse++pre
  let p2 := positions p1 flags.length (output row unit flags).length
  obtain ⟨c,hc,tc⟩ := finish_trace row unit flags (after unit flags (zeroWord unit)) pre1 p2
  rw [after_length unit flags (zeroWord unit) hz] at hc
  have whole := trace_trans (trace_trans ta tb) tc
  refine ⟨a+b+c,?_,?_⟩
  · unfold budget loopBudget at *
    nlinarith
  · simpa only [p1,p2,pre1,positions_add,neg_add_cancel,zero_add,add_zero] using whole

theorem budget_le (m : ℕ) (flags : List Bool) :
    budget m flags ≤ flags.length*(26*m+70)+10*m+30 := by
  have h := List.count_le_length (l:=flags) (a:=true)
  unfold budget
  nlinarith

theorem output_length (row unit flags : List Bool) (hr : row.length=unit.length) :
    (output row unit flags).length=2*unit.length*(flags.count true) :=
  encoded_length row unit flags (zeroWord unit) hr (List.length_replicate ..)

theorem native_complete (row unit flags : List Bool) (hr : row.length=unit.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget unit.length flags,
      Transpose.stepN nativeMachine input t
        ((cfg start row unit (initial flags pre) pos).denote nativeEncoding program inputPos outRev)=
        some ((cfg .done row unit (final ((symbols (output row unit flags)).reverse++pre))
          (positions pos (-(flags.length : ℤ)) (output row unit flags).length)).denote
          nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done row unit (final ((symbols (output row unit flags)).reverse++pre))
          (positions pos (-(flags.length : ℤ)) (output row unit flags).length)).denote
          nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace row unit flags hr pre pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro h; exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (row unit flags : List Bool) (hr : row.length=unit.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget unit.length flags,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start row unit (initial flags pre) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done row unit (final ((symbols (output row unit flags)).reverse++pre))
            (positions pos (-(flags.length : ℤ)) (output row unit flags).length)) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace row unit flags hr pre pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.RowConsumer
