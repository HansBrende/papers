import TransposeFollowup.NativeIOCore
import TransposeFollowup.NativeMappedCopy

/-! Actual loading from the original external input. The only work tape
starts blank. The caller writes both delimiters, copies every input bit,
then rewinds the work head. The external input head ends at its right end. -/
namespace TransposeFollowup.RawInputCopy
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label
  | init (pc : NativeBuffer.Label)
  | read | write (bit : Bool) | advance
  | seal (pc : NativeSealBack.Label)
  | done
  deriving DecidableEq, Fintype

def binding : FinitePortBinding (Fin 1) (Fin 1) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intro p q; simp [eq_comm]

def start : Label := .init (.erase 0)

def program : NativeIO.Program (Fin 1) Label
  | .init .done => .work (.jump .read)
  | .init pc => .work (binding.instruction Label.init (NativeBuffer.program pc))
  | .read => .readInput (fun x => match x with | some b => .write b | none => .seal .seal)
  | .write b => .work (.act (Microcode.single 0 ⟨some (.data b),.right⟩) .advance)
  | .advance => .moveInput .right .read
  | .seal .done => .work (.jump .done)
  | .seal pc => .work (binding.instruction Label.seal (NativeSealBack.program pc))
  | .done => .work .halt

def workCfg (pc : Label) (word : Tape Bool) (pos : ℤ) : NativeMicrocode.Config (Fin 1) Label :=
  ⟨⟨pc,fun _ => word.denote⟩,fun _ => pos⟩
def cfg (pc : Label) (word : Tape Bool) (pos inputPos : ℤ) (outRev : List Bool) : NativeIO.Config (Fin 1) Label :=
  ⟨workCfg pc word pos,inputPos,outRev⟩
def frame (pos : ℤ) : MicrocodeEmbedding.Frame (Fin 1) :=
  ⟨fun _ => (⟨[],[]⟩ : Tape Bool).denote,fun _ => pos⟩
abbrev Trace (w : List Bool) := OperationalTrace.Trace (NativeIO.step program w) (NativeIO.Active program)

theorem init_code (pc : NativeBuffer.Label) (hh : NativeBuffer.program pc≠.halt) (_ : NativeBuffer.program pc≠.reject) :
    NativeIO.workProgram program (.init pc)=MicrocodeEmbedding.instruction binding.ports Label.init (NativeBuffer.program pc) := by
  cases pc <;> simp_all [NativeIO.workProgram,program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem seal_code (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc≠.halt) (_ : NativeSealBack.program pc≠.reject) :
    NativeIO.workProgram program (.seal pc)=MicrocodeEmbedding.instruction binding.ports Label.seal (NativeSealBack.program pc) := by
  cases pc <;> simp_all [NativeIO.workProgram,program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem embed_init (pc : NativeBuffer.Label) (word : Tape Bool) (pos basePos : ℤ) :
    MicrocodeEmbedding.embed binding.ports Label.init (NativeBuffer.cfg pc word (fun _ => pos)).denote (frame basePos)=
      workCfg (.init pc) word pos := by
  unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus workCfg frame
  simp only [← binding.values_eq_extend]
  congr 2
  funext i
  fin_cases i
  rfl

theorem embed_seal (pc : NativeSealBack.Label) (word : Tape Bool) (pos basePos : ℤ) :
    MicrocodeEmbedding.embed binding.ports Label.seal (NativeSealBack.cfg pc word (fun _ => pos)).denote (frame basePos)=
      workCfg (.seal pc) word pos := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus workCfg frame
  simp only [← binding.values_eq_extend]
  congr 2
  funext i
  fin_cases i
  rfl

theorem init_call (w : List Bool) (pos inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2, Trace w t (cfg start ⟨[],[]⟩ pos inputPos outRev)
      (cfg (.init .done) BinaryCarry.preparedOutput pos inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos)
  have he := MicrocodeEmbedding.trace_embed binding.ports Label.init NativeBuffer.program
    (NativeIO.workProgram program) (frame pos) init_code htr
  have hi := NativeIO.lift_work_trace program w inputPos outRev he
  exact ⟨t,ht,by simpa only [embed_init,cfg,start] using hi⟩

theorem seal_call (w xs : List Bool) (pos inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*xs.length+5, Trace w t (cfg (.seal .seal) (NativeSealBack.openWord xs) pos inputPos outRev)
      (cfg (.seal .done) (Counter.marked xs) (pos-xs.length) inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace xs (fun _ => pos)
  have he := MicrocodeEmbedding.trace_embed binding.ports Label.seal NativeSealBack.program
    (NativeIO.workProgram program) (frame pos) seal_code htr
  have hi := NativeIO.lift_work_trace program w inputPos outRev he
  exact ⟨t,ht,by simpa only [embed_seal,cfg] using hi⟩

theorem jump_trace (w : List Bool) (pc next : Label) (word : Tape Bool) (pos inputPos : ℤ) (outRev : List Bool)
    (h : program pc=.work (.jump next)) : Trace w 1 (cfg pc word pos inputPos outRev) (cfg next word pos inputPos outRev) :=
  NativeIO.jump_trace _ _ _ _ h

theorem input_at (pre rest : List Bool) : Transpose.readInput (pre++rest) pre.length=rest.head? := by
  have h : ¬(pre.length : ℤ)<0 := by omega
  simp only [Transpose.readInput,h,ite_false,Int.toNat_natCast]
  clear h
  induction pre with
  | nil => cases rest <;> rfl
  | cons b pre ih => simpa only [List.cons_append,List.length_cons,Transpose.nth] using ih

theorem read_trace (w : List Bool) (word : Tape Bool) (pos inputPos : ℤ) (outRev : List Bool) :
    Trace w 1 (cfg .read word pos inputPos outRev)
      (cfg (match Transpose.readInput w inputPos with | some b => .write b | none => .seal .seal) word pos inputPos outRev) := by
  apply OperationalTrace.Trace.cons
  · trivial
  · exact .refl _

theorem write_step (w xs : List Bool) (b : Bool) (pos inputPos : ℤ) (outRev : List Bool) :
    NativeIO.step program w (cfg (.write b) (NativeSealBack.openWord xs) pos inputPos outRev)=
      cfg .advance (NativeSealBack.openWord (xs++[b])) (pos+1) inputPos outRev := by
  let z : NativeZipper.Config (Fin 1) Label := ⟨⟨.write b,fun _ => NativeSealBack.openWord xs⟩,fun _ => pos⟩
  have hz : NativeZipper.step (NativeIO.workProgram program) z=
      ⟨⟨.advance,fun _ => NativeSealBack.openWord (xs++[b])⟩,fun _ => pos+1⟩ := by
    simp only [NativeZipper.step,Microcode.step,NativeIO.workProgram,program,z]
    congr 2 <;> funext i <;> fin_cases i <;>
      simp [Microcode.single,Microcode.Action.apply,NativeSealBack.openWord,symbols,
        Tape.write,Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]
  have he := NativeZipper.step_denote (NativeIO.workProgram program) z
  rw [hz] at he
  change (⟨NativeMicrocode.step (NativeIO.workProgram program) z.denote,inputPos,outRev⟩ : NativeIO.Config _ _)=_
  rw [← he]
  rfl

theorem write_trace (w xs : List Bool) (b : Bool) (pos inputPos : ℤ) (outRev : List Bool) :
    Trace w 1 (cfg (.write b) (NativeSealBack.openWord xs) pos inputPos outRev)
      (cfg .advance (NativeSealBack.openWord (xs++[b])) (pos+1) inputPos outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · rw [write_step]; exact .refl _

theorem advance_trace (w : List Bool) (word : Tape Bool) (pos inputPos : ℤ) (outRev : List Bool) :
    Trace w 1 (cfg .advance word pos inputPos outRev) (cfg .read word pos (inputPos+1) outRev) := by
  apply OperationalTrace.Trace.cons
  · trivial
  · exact .refl _

theorem scan_trace (pre rest : List Bool) (pos : ℤ) (outRev : List Bool) :
    Trace (pre++rest) (3*rest.length+1)
      (cfg .read (NativeSealBack.openWord pre) (pos+pre.length) pre.length outRev)
      (cfg (.seal .seal) (NativeSealBack.openWord (pre++rest)) (pos+(pre++rest).length) (pre++rest).length outRev) := by
  induction rest generalizing pre with
  | nil =>
    have h : Transpose.readInput pre pre.length=none := by simpa only [List.append_nil,List.head?_nil] using input_at pre []
    simpa only [List.append_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,h] using
      read_trace pre (NativeSealBack.openWord pre) (pos+pre.length) pre.length outRev
  | cons b rest ih =>
    have tr := read_trace (pre++b::rest) (NativeSealBack.openWord pre) (pos+pre.length) pre.length outRev
    rw [input_at] at tr
    have tw := write_trace (pre++b::rest) pre b (pos+pre.length) pre.length outRev
    have ta := advance_trace (pre++b::rest) (NativeSealBack.openWord (pre++[b])) (pos+pre.length+1) pre.length outRev
    have ti := ih (pre++[b])
    have hi : Trace (pre++b::rest) (3*rest.length+1)
        (cfg .read (NativeSealBack.openWord (pre++[b])) (pos+pre.length+1) (pre.length+1) outRev)
        (cfg (.seal .seal) (NativeSealBack.openWord (pre++b::rest))
          (pos+(pre++b::rest).length) (pre++b::rest).length outRev) := by
      simpa [List.append_assoc,Int.natCast_add,add_assoc] using ti
    have ht := NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tr tw) ta) hi
    convert ht using 1
    simp
    omega

theorem complete_trace (w : List Bool) (pos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 5*w.length+10, Trace w t (cfg start ⟨[],[]⟩ pos 0 outRev)
      (cfg .done (Counter.marked w) pos w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := init_call w pos 0 outRev
  have ja := jump_trace w (.init .done) .read BinaryCarry.preparedOutput pos 0 outRev rfl
  have tb : Trace w (3*w.length+1) (cfg .read BinaryCarry.preparedOutput pos 0 outRev)
      (cfg (.seal .seal) (NativeSealBack.openWord w) (pos+w.length) w.length outRev) := by
    simpa only [List.nil_append,List.length_nil,Int.natCast_zero,add_zero,
      show NativeSealBack.openWord []=BinaryCarry.preparedOutput from rfl] using scan_trace [] w pos outRev
  obtain ⟨b,hb,tb'⟩ := seal_call w w (pos+w.length) w.length outRev
  have jp := jump_trace w (.seal .done) .done (Counter.marked w) pos w.length outRev rfl
  have hr : pos+(w.length : ℤ)-w.length=pos := by omega
  rw [hr] at tb'
  exact ⟨a+1+(3*w.length+1)+b+1,by omega,
    NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
      (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta ja) tb) tb') jp⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 1) start
noncomputable def nativeMachine := NativeIO.machine nativeEncoding program

theorem native_complete (w : List Bool) : ∃ t ≤ 5*w.length+10,
    Transpose.stepN nativeMachine w t (Transpose.init nativeMachine)=
      some ((cfg .done (Counter.marked w) 0 w.length []).denote nativeEncoding program) ∧
    Transpose.step nativeMachine w ((cfg .done (Counter.marked w) 0 w.length []).denote nativeEncoding program)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace w 0 []
  refine ⟨t,ht,?_,?_⟩
  · have hb : (cfg start ⟨[],[]⟩ 0 0 []).denote nativeEncoding program=Transpose.init nativeMachine :=
      NativeIO.blank_denote nativeEncoding program start (NativeMicrocode.initialEncoding_start _)
    rw [← hb]
    exact NativeIO.trace_stepN nativeEncoding program w htr
  · apply (NativeIO.step_none_iff nativeEncoding program w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program]

theorem fixed_resources : nativeMachine.k=1 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=21 ∧ nativeEncoding.label start=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=21
  decide +kernel

end TransposeFollowup.RawInputCopy
