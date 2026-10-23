import TransposeFollowup.NativeMatchingXorTags
import TransposeFollowup.NativeSealBack
import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeCountedLoop

/-! Expand an arbitrary physical row-mask stream with one reusable unary
row clock. This uniform caller reads each mask bit and invokes the fixed
bit-repetition controller. The clock is restored after every row. -/
namespace TransposeFollowup.NativeMatchingXorTagStream
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label | scan | repeat (bit : Bool) (pc : NativeMatchingXorTags.Label) | advance | done | reject
  deriving DecidableEq, Fintype

def repeatBinding : FinitePortBinding (Fin 2) (Fin 3) where
  ports := ⟨![1,2],by decide +kernel⟩
  decode := fun p => if p=1 then some 0 else if p=2 then some 1 else none
  decode_spec := by decide +kernel

def program : Microcode.Program (Fin 3) Label
  | .scan => .read 0 (fun s => match s with
      | .data b => .repeat b .clock | .stop => .done | _ => .reject)
  | .repeat _ .done => .jump .advance
  | .repeat b pc => repeatBinding.instruction (Label.repeat b) (NativeMatchingXorTags.program b pc)
  | .advance => .act (Microcode.single 0 ⟨none,.right⟩) .scan
  | .done => .halt
  | .reject => .reject

theorem repeat_code (b : Bool) (pc : NativeMatchingXorTags.Label)
    (hh : NativeMatchingXorTags.program b pc≠.halt) (_ : NativeMatchingXorTags.program b pc≠.reject) :
    program (.repeat b pc)=MicrocodeEmbedding.instruction repeatBinding.ports
      (Label.repeat b) (NativeMatchingXorTags.program b pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def bank (flags clock out : Tape Bool) : Fin 3 → Tape Bool := ![flags,clock,out]
def cfg (pc : Label) (flags clock out : Tape Bool) (pos : Fin 3 → ℤ) : NativeZipper.Config (Fin 3) Label :=
  ⟨⟨pc,bank flags clock out⟩,pos⟩
def frame (flags clock out : Tape Bool) (pos : Fin 3 → ℤ) : MicrocodeEmbedding.Frame (Fin 3) :=
  ⟨fun p => (bank flags clock out p).denote,pos⟩

def expanded (W : ℕ) (flags : List Bool) := flags.flatMap (fun b => List.replicate W b)
def advance (pos : Fin 3 → ℤ) (rows bits : ℕ) : Fin 3 → ℤ :=
  fun p => pos p + if p=0 then rows else if p=2 then bits else 0

@[simp] theorem advance_zero (pos : Fin 3 → ℤ) : advance pos 0 0=pos := by funext p; simp [advance]

theorem advance_add (pos : Fin 3 → ℤ) (a b c d : ℕ) :
    advance (advance pos a b) c d=advance pos (a+c) (b+d) := by
  funext p; simp [advance]; split_ifs <;> ring

theorem expanded_length (W : ℕ) (flags : List Bool) : (expanded W flags).length=flags.length*W := by
  induction flags with
  | nil => simp [expanded]
  | cons b flags ih => simp [expanded,List.flatMap_cons,Nat.add_mul,Nat.add_comm]

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem scan_bit (b : Bool) (fl fr : List (Sym Bool)) (clock out : Tape Bool) (pos : Fin 3 → ℤ) :
    Trace 1 (cfg .scan ⟨fl,.data b::fr⟩ clock out pos).denote
      (cfg (.repeat b .clock) ⟨fl,.data b::fr⟩ clock out pos).denote := by
  have h : NativeZipper.step program (cfg .scan ⟨fl,.data b::fr⟩ clock out pos)=
      cfg (.repeat b .clock) ⟨fl,.data b::fr⟩ clock out pos := by
    simp [NativeZipper.step,Microcode.step,program,cfg,bank,Tape.read]
  have hc : NativeMicrocode.Active program (cfg .scan ⟨fl,.data b::fr⟩ clock out pos).denote := by
    simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]
  apply OperationalTrace.Trace.cons hc
  rw [← NativeZipper.step_denote]
  rw [h]
  exact .refl _

theorem scan_stop (fl fr : List (Sym Bool)) (clock out : Tape Bool) (pos : Fin 3 → ℤ) :
    Trace 1 (cfg .scan ⟨fl,.stop::fr⟩ clock out pos).denote (cfg .done ⟨fl,.stop::fr⟩ clock out pos).denote := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]
  · have h : NativeZipper.step program (cfg .scan ⟨fl,.stop::fr⟩ clock out pos)=cfg .done ⟨fl,.stop::fr⟩ clock out pos := by
      simp [NativeZipper.step,Microcode.step,program,cfg,bank,Tape.read]
    rw [← NativeZipper.step_denote,h]
    exact .refl _

theorem embed_repeat (b : Bool) (pc : NativeMatchingXorTags.Label) (flags clock out baseClock baseOut : Tape Bool)
    (pos : Fin 3 → ℤ) (rpos : Fin 2 → ℤ) :
    MicrocodeEmbedding.embed repeatBinding.ports (Label.repeat b)
      (NativeMatchingXorTags.cfg pc clock out rpos).denote (frame flags baseClock baseOut pos)=
      (cfg (.repeat b pc) flags clock out (repeatBinding.values rpos pos)).denote := by
  unfold MicrocodeEmbedding.embed NativeMatchingXorTags.cfg NativeZipper.Config.denote
    Microcode.Config.denote cfg frame
  simp only [← repeatBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem repeat_call (b : Bool) (flags : Tape Bool) (clock : List Bool) (acc : List Bool)
    (pos : Fin 3 → ℤ) :
    ∃ t ≤ 4*clock.length+4, Trace t
      (cfg (.repeat b .clock) flags (Counter.marked clock) (NativeSealBack.openWord acc) pos).denote
      (cfg (.repeat b .done) flags (Counter.marked clock)
        (NativeSealBack.openWord (acc++List.replicate clock.length b)) (advance pos 0 clock.length)).denote := by
  obtain ⟨t,ht,htr⟩ := NativeZipper.trace_of_run (NativeMatchingXorTags.program b)
    (NativeMatchingXorTags.complete_run b clock [] [] ((symbols acc).reverse++[.start]) []
      (fun p => pos (repeatBinding.ports p)))
  have he := MicrocodeEmbedding.trace_embed repeatBinding.ports (Label.repeat b)
    (NativeMatchingXorTags.program b) program (frame flags (Counter.marked clock) (NativeSealBack.openWord acc) pos)
    (repeat_code b) htr
  have hpi : repeatBinding.values (fun p => pos (repeatBinding.ports p)) pos=pos := by
    funext p; fin_cases p <;> rfl
  have hpf : repeatBinding.values (NativeMatchingXorTags.advance (fun p => pos (repeatBinding.ports p)) 0 clock.length) pos=
      advance pos 0 clock.length := by
    funext p; fin_cases p <;> simp [repeatBinding,FinitePortBinding.values,NativeMatchingXorTags.advance,advance]
  refine ⟨t,ht,?_⟩
  simpa only [Counter.marked,NativeSealBack.openWord,List.nil_append,List.drop_nil,
    NativeMatchingXorTags.symbols,CopyMachine.symbols,embed_repeat,hpi,hpf,symbols,
    List.map_append,List.reverse_append,List.map_replicate,List.reverse_replicate,List.append_assoc] using he

theorem advance_trace (b : Bool) (fl fr : List (Sym Bool)) (clock out : Tape Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2, Trace t (cfg (.repeat b .done) ⟨fl,.data b::fr⟩ clock out pos).denote
      (cfg .scan ⟨.data b::fl,fr⟩ clock out (advance pos 1 0)).denote := by
  have h : NativeZipper.run program 2 (cfg (.repeat b .done) ⟨fl,.data b::fr⟩ clock out pos)=
      cfg .scan ⟨.data b::fl,fr⟩ clock out (advance pos 1 0) := by
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,bank,
      Microcode.Action.apply,Microcode.single,Tape.read,Tape.moveRight,NativeMicrocode.direction,Transpose.Dir.shift]
    constructor <;> funext p <;> fin_cases p <;> simp [advance]
  exact NativeZipper.trace_of_run program h


theorem complete_trace (flags clock acc : List Bool) (fl fr : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    ∃ t ≤ flags.length*(4*clock.length+7)+1, Trace t
      (cfg .scan ⟨fl,symbols flags++.stop::fr⟩ (Counter.marked clock) (NativeSealBack.openWord acc) pos).denote
      (cfg .done ⟨(symbols flags).reverse++fl,.stop::fr⟩ (Counter.marked clock)
        (NativeSealBack.openWord (acc++expanded clock.length flags))
        (advance pos flags.length (flags.length*clock.length))).denote := by
  induction flags generalizing fl acc pos with
  | nil =>
    refine ⟨1,by simp,?_⟩
    simpa [symbols,expanded] using scan_stop fl fr (Counter.marked clock) (NativeSealBack.openWord acc) pos
  | cons b flags ih =>
    have ts := scan_bit b fl (symbols flags++.stop::fr) (Counter.marked clock) (NativeSealBack.openWord acc) pos
    obtain ⟨a,ha,ta⟩ := repeat_call b ⟨fl,.data b::(symbols flags++.stop::fr)⟩ clock acc pos
    obtain ⟨c,hc,tc⟩ := advance_trace b fl (symbols flags++.stop::fr) (Counter.marked clock)
      (NativeSealBack.openWord (acc++List.replicate clock.length b)) (advance pos 0 clock.length)
    obtain ⟨t,ht,htr⟩ := ih (acc := acc++List.replicate clock.length b) (fl := .data b::fl)
      (pos := advance (advance pos 0 clock.length) 1 0)
    refine ⟨1+a+c+t,?_,?_⟩
    · simp only [List.length_cons]
      nlinarith
    · have hp : advance (advance (advance pos 0 clock.length) 1 0) flags.length
          (flags.length*clock.length)=advance pos (b::flags).length ((b::flags).length*clock.length) := by
        rw [advance_add,advance_add]
        simp only [List.length_cons,zero_add,Nat.add_mul,Nat.one_mul]
        congr 1 <;> omega
      have htr' := NativeCountedLoop.trace_trans
        (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ts ta) tc) htr
      simpa only [symbols,List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,
        List.singleton_append,List.nil_append,expanded,List.flatMap_cons,hp] using htr'

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 3) Label.scan
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=3 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=18 := by
  refine ⟨rfl,rfl,?_⟩
  change Fintype.card Label-1+1=18
  decide +kernel

theorem native_expand (flags clock acc : List Bool) (fl fr : List (Sym Bool)) (pos : Fin 3 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ flags.length*(4*clock.length+7)+1,
      Transpose.stepN nativeMachine input t
        ((cfg .scan ⟨fl,symbols flags++.stop::fr⟩ (Counter.marked clock) (NativeSealBack.openWord acc) pos).denote.denote
          nativeEncoding program inputPos outRev)=
        some ((cfg .done ⟨(symbols flags).reverse++fl,.stop::fr⟩ (Counter.marked clock)
          (NativeSealBack.openWord (acc++expanded clock.length flags))
          (advance pos flags.length (flags.length*clock.length))).denote.denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done ⟨(symbols flags).reverse++fl,.stop::fr⟩ (Counter.marked clock)
          (NativeSealBack.openWord (acc++expanded clock.length flags))
          (advance pos flags.length (flags.length*clock.length))).denote.denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace flags clock acc fl fr pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]

end TransposeFollowup.NativeMatchingXorTagStream
