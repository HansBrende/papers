import TransposeFollowup.MeasuredWord
import TransposeFollowup.NativeClosedStream
import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeCountedLoop

/-! Scan a marked source and decrement a physical counter once per bit.
Both heads return. The actual decrementer's amortized bound is retained;
there is no width-length scan charged on each source bit. -/
namespace TransposeFollowup.MeasuredScan
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label | read | count (pc : Microcode.DecrementFamily.Label) | rewind (pc : NativeSealBack.Label) | done | reject
  deriving DecidableEq,Fintype

def binding (t : Fin 2) : FinitePortBinding (Fin 1) (Fin 2) where
  ports:=⟨fun _ => t,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun q => if q=t then some 0 else none
  decode_spec:=by
    intro q i
    change (if q=t then some (0:Fin 1) else none)=some i ↔ t=q
    fin_cases i
    simp [eq_comm]

def program : Microcode.Program (Fin 2) Label
  | .read => .read 0 (fun s => match s with | .data _ => .count 0 | .stop => .rewind .back | _ => .reject)
  | .count pc => if pc=11 then .act (Microcode.single 0 ⟨none,.right⟩) .read
      else if pc=12 then .reject else (binding 1).instruction Label.count (Microcode.DecrementFamily.program pc)
  | .rewind .done => .jump .done
  | .rewind pc => (binding 0).instruction Label.rewind (NativeSealBack.program pc)
  | .done => .halt | .reject => .reject

def bank (source : Tape Bool) (cw : List Bool) : Fin 2 → Tape Bool := ![source,Counter.marked cw]
def cfg (pc : Label) (source : Tape Bool) (cw : List Bool) (pos : Fin 2 → ℤ) : NativeMicrocode.Config (Fin 2) Label :=
  ⟨⟨pc,fun p => (bank source cw p).denote⟩,pos⟩
def frame (source : Tape Bool) (cw : List Bool) (pos : Fin 2 → ℤ) : MicrocodeEmbedding.Frame (Fin 2) :=
  ⟨fun p => (bank source cw p).denote,pos⟩
def positions (pos : Fin 2 → ℤ) (d : ℤ) : Fin 2 → ℤ := fun t => pos t+if t=0 then d else 0

def cursor (pre rest : List Bool) : Tape Bool := ⟨(symbols pre).reverse++[.start],symbols rest++[.stop]⟩

theorem cursor_start (xs : List Bool) : cursor [] xs=Counter.marked xs := rfl
theorem cursor_end (xs : List Bool) : cursor xs []=RowStream.closedTape xs := by
  simp [cursor,RowStream.closedTape,symbols]

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem count_code (pc : Microcode.DecrementFamily.Label) (hh : Microcode.DecrementFamily.program pc≠.halt)
    (_ : Microcode.DecrementFamily.program pc≠.reject) :
    program (.count pc)=MicrocodeEmbedding.instruction (binding 1).ports Label.count (Microcode.DecrementFamily.program pc) := by
  have h11 : pc≠11 := by intro h; subst pc; exact hh rfl
  have h12 : pc≠12 := by intro h; subst pc; exact hh rfl
  simp [program,h11,h12,FinitePortBinding.instruction_eq]

theorem rewind_code (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc≠.halt)
    (_ : NativeSealBack.program pc≠.reject) :
    program (.rewind pc)=MicrocodeEmbedding.instruction (binding 0).ports Label.rewind (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem embed_count (pc : Microcode.DecrementFamily.Label) (xs old : List Bool) (source : Tape Bool) (pos : Fin 2 → ℤ) :
    MicrocodeEmbedding.embed (binding 1).ports Label.count (NativeCounter.cfg pc xs (fun _ => pos 1)).denote
      (frame source old pos)=cfg (.count pc) source xs pos := by
  unfold MicrocodeEmbedding.embed NativeCounter.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← (binding 1).values_eq_extend]
  congr 2 <;> funext i <;> fin_cases i <;> rfl

theorem embed_rewind (pc : NativeSealBack.Label) (source base : Tape Bool) (cw : List Bool) (pos : Fin 2 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (binding 0).ports Label.rewind (NativeSealBack.cfg pc source (fun _ => z)).denote
      (frame base cw pos)=cfg (.rewind pc) source cw (Function.update pos 0 z) := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← (binding 0).values_eq_extend]
  congr 2 <;> funext i <;> fin_cases i <;> simp [binding,FinitePortBinding.values,bank]

theorem count_call (source : Tape Bool) (cw : List Bool) (hc : 0<Counter.value cw) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 2*Counter.stepCost cw, Trace t (cfg (.count 0) source cw pos)
      (cfg (.count 11) source (Counter.decrement cw) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeCounter.decrement_trace cw (fun _ => pos 1)
  have he := MicrocodeEmbedding.trace_embed (binding 1).ports Label.count Microcode.DecrementFamily.program
    program (frame source cw pos) count_code htr
  exact ⟨t,ht,by simpa only [embed_count,NativeCounter.returnLabel,MeasuredWord.nonzero cw hc,Bool.false_eq_true,ite_false] using he⟩

theorem rewind_call (xs cw : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 2*xs.length+4, Trace t (cfg (.rewind .back) (RowStream.closedTape xs) cw pos)
      (cfg (.rewind .done) (Counter.marked xs) cw (positions pos (-(xs.length:ℤ)))) := by
  obtain ⟨t,ht,htr⟩ := NativeClosedStream.rewind_trace xs (fun _ => pos 0)
  have he := MicrocodeEmbedding.trace_embed (binding 0).ports Label.rewind NativeSealBack.program
    program (frame (RowStream.closedTape xs) cw pos) rewind_code htr
  have hp : Function.update pos 0 (pos 0-xs.length)=positions pos (-(xs.length:ℤ)) := by
    funext i; fin_cases i <;> simp [positions,sub_eq_add_neg]
  exact ⟨t,ht,by simpa only [embed_rewind,Function.update_eq_self,hp] using he⟩

theorem positions_zero (pos : Fin 2 → ℤ) : positions pos 0=pos := by funext i; simp [positions]
theorem positions_add (pos : Fin 2 → ℤ) (a b : ℤ) : positions (positions pos a) b=positions pos (a+b) := by
  funext i; fin_cases i <;> simp [positions,add_assoc]

theorem read_trace (pre rest cw : List Bool) (pos : Fin 2 → ℤ) :
    Trace 1 (cfg .read (cursor pre rest) cw pos)
      (cfg (if rest=[] then .rewind .back else .count 0) (cursor pre rest) cw pos) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,program]
  · have hs : NativeMicrocode.step program (cfg .read (cursor pre rest) cw pos)=
        cfg (if rest=[] then .rewind .back else .count 0) (cursor pre rest) cw pos := by
      cases rest <;> simp [NativeMicrocode.step,Microcode.actualStep,cfg,program,bank,cursor,Tape.read,symbols]
    rw [hs]; exact .refl _

theorem advance_step (pre rest cw : List Bool) (b : Bool) (pos : Fin 2 → ℤ) :
    NativeMicrocode.step program (cfg (.count 11) (cursor pre (b::rest)) cw pos)=
      cfg .read (cursor (pre++[b]) rest) cw (positions pos 1) := by
  let z : NativeZipper.Config (Fin 2) Label := ⟨⟨.count 11,bank (cursor pre (b::rest)) cw⟩,pos⟩
  have hz : NativeZipper.step program z=
      ⟨⟨.read,bank (cursor (pre++[b]) rest) cw⟩,positions pos 1⟩ := by
    simp only [NativeZipper.step,Microcode.step,program,z,ite_true]
    congr 2 <;> funext i <;> fin_cases i <;>
      simp [Microcode.single,Microcode.Action.apply,bank,cursor,symbols,Tape.moveRight,Tape.read,
        positions,NativeMicrocode.direction,Transpose.Dir.shift]
  have he := NativeZipper.step_denote program z
  rw [hz] at he
  exact he.symm

theorem advance_trace (pre rest cw : List Bool) (b : Bool) (pos : Fin 2 → ℤ) :
    Trace 1 (cfg (.count 11) (cursor pre (b::rest)) cw pos)
      (cfg .read (cursor (pre++[b]) rest) cw (positions pos 1)) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,program]
  · rw [advance_step]; exact .refl _

theorem scan_trace (pre rest cw : List Bool) (hc : rest.length ≤ Counter.value cw) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 2*Counter.totalCost rest.length cw+2*rest.length+1, Trace t
      (cfg .read (cursor pre rest) cw (positions pos pre.length))
      (cfg (.rewind .back) (RowStream.closedTape (pre++rest)) (Counter.wordAfter rest.length cw)
        (positions pos (pre++rest).length)) := by
  induction rest generalizing pre cw with
  | nil =>
    refine ⟨1,by simp [Counter.totalCost],?_⟩
    simpa only [List.append_nil,List.length_nil,Counter.wordAfter,ite_true,cursor_end] using read_trace pre [] cw (positions pos pre.length)
  | cons b rest ih =>
    have hp : 0<Counter.value cw := by simpa using (show 0<Counter.value cw by simp only [List.length_cons] at hc;omega)
    have hd := Counter.decrement_value cw (MeasuredWord.nonzero cw hp)
    have tr := read_trace pre (b::rest) cw (positions pos pre.length)
    obtain ⟨a,ha,ta⟩ := count_call (cursor pre (b::rest)) cw hp (positions pos pre.length)
    have tm := advance_trace pre rest (Counter.decrement cw) b (positions pos pre.length)
    obtain ⟨d,hd',td⟩ := ih (pre++[b]) (Counter.decrement cw) (by simp only [List.length_cons] at hc;omega)
    have ht : Trace d (cfg .read (cursor (pre++[b]) rest) (Counter.decrement cw)
        (positions (positions pos pre.length) 1))
        (cfg (.rewind .back) (RowStream.closedTape (pre++b::rest)) (Counter.wordAfter rest.length (Counter.decrement cw))
          (positions pos (pre++b::rest).length)) := by
      simpa [positions_add,List.append_assoc] using td
    refine ⟨1+a+1+d,?_,?_⟩
    · simp only [List.length_cons,Counter.totalCost]
      omega
    · simpa only [List.cons_ne_nil,ite_false,Counter.wordAfter,List.length_cons] using
        NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tr ta) tm) ht

theorem complete_trace (xs cw : List Bool) (hc : xs.length ≤ Counter.value cw) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 12*xs.length+4*cw.length+6, Trace t (cfg .read (Counter.marked xs) cw pos)
      (cfg .done (Counter.marked xs) (Counter.wordAfter xs.length cw) pos) := by
  obtain ⟨a,ha,ta⟩ := scan_trace [] xs cw hc pos
  have ta' : Trace a (cfg .read (Counter.marked xs) cw pos)
      (cfg (.rewind .back) (RowStream.closedTape xs) (Counter.wordAfter xs.length cw) (positions pos xs.length)) := by
    simpa only [List.nil_append,List.length_nil,Int.natCast_zero,positions_zero,cursor_start] using ta
  obtain ⟨b,hb,tb⟩ := rewind_call xs (Counter.wordAfter xs.length cw) (positions pos xs.length)
  have hp : positions (positions pos (xs.length:ℤ)) (-(xs.length:ℤ))=pos := by
    rw [positions_add,add_neg_cancel,positions_zero]
  rw [hp] at tb
  have tj : Trace 1 (cfg (.rewind .done) (Counter.marked xs) (Counter.wordAfter xs.length cw) pos)
      (cfg .done (Counter.marked xs) (Counter.wordAfter xs.length cw) pos) := by
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,cfg,program]
    · exact .refl _
  have hcost := NativeCounter.native_sequence_budget xs.length cw
  exact ⟨a+b+1,by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta' tb) tj⟩

theorem length_count_trace (xs : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 16*xs.length+6, Trace t (cfg .read (Counter.marked xs) (List.replicate xs.length true) pos)
      (cfg .done (Counter.marked xs) (MeasuredWord.counted xs.length) pos) := by
  simpa only [MeasuredWord.counted,List.length_replicate,show ∀ m:ℕ,12*m+4*m+6=16*m+6 by intro m;omega] using
    complete_trace xs (List.replicate xs.length true) (MeasuredWord.capacity xs.length) pos

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 2) Label.read
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem native_complete (xs cw : List Bool) (hc : xs.length ≤ Counter.value cw) (pos : Fin 2 → ℤ)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 12*xs.length+4*cw.length+6,
      Transpose.stepN nativeMachine w t ((cfg .read (Counter.marked xs) cw pos).denote nativeEncoding program inputPos outRev)=
        some ((cfg .done (Counter.marked xs) (Counter.wordAfter xs.length cw) pos).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine w ((cfg .done (Counter.marked xs) (Counter.wordAfter xs.length cw) pos).denote
        nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace xs cw hc pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program w inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program w inputPos outRev _).mpr
  intro h; exact h.1 rfl

theorem fixed_resources : nativeMachine.k=2 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=22 ∧ nativeEncoding.label .read=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=22
  decide +kernel

end TransposeFollowup.MeasuredScan
