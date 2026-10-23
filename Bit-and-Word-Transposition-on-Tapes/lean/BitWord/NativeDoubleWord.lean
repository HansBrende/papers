import BitWord.NativeTapeCalls
import TransposeFollowup.NativeMappedAppend

/-! A literal two-tape caller prepends one low zero bit to a marked binary
word. This turns the suffix parameter k into the exponent 2k for the ruler. -/
namespace BitWord.NativeDoubleWord
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop
set_option autoImplicit false
abbrev Port := Fin 2
abbrev Bank := Port → Tape Bool

def binding := pairBinding (0:Port) 1 (by decide)
inductive Label | init (pc : NativeBuffer.Label) | zero | append (pc : Microcode.MappedAppendFamily.Label)
  | seal (pc : NativeSealBack.Label) | done
  deriving DecidableEq,Fintype
def start : Label := .init (.erase 0)
def program : Microcode.Program Port Label
  | .init .done => .jump .zero
  | .init pc => (singleBinding (1:Port)).instruction Label.init (NativeBuffer.program pc)
  | .zero => .act (Microcode.single 1 ⟨some (.data false),.right⟩) (.append 0)
  | .append pc => if pc=7 then .jump (.seal .seal) else
      binding.instruction Label.append (Microcode.MappedAppendFamily.program id pc)
  | .seal .done => .jump .done
  | .seal pc => (singleBinding (1:Port)).instruction Label.seal (NativeSealBack.program pc)
  | .done => .halt
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)
abbrev cfg := workCfg (T:=Port) (L:=Label)

theorem init_code (pc : NativeBuffer.Label) (hh : NativeBuffer.program pc≠.halt)
    (_ : NativeBuffer.program pc≠.reject) :
    program (.init pc)=MicrocodeEmbedding.instruction (singleBinding (1:Port)).ports Label.init
      (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]
theorem append_code (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program id pc≠.halt)
    (_ : Microcode.MappedAppendFamily.program id pc≠.reject) :
    program (.append pc)=MicrocodeEmbedding.instruction binding.ports Label.append
      (Microcode.MappedAppendFamily.program id pc) := by
  have hp : pc≠7 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]
theorem seal_code (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc≠.halt)
    (_ : NativeSealBack.program pc≠.reject) :
    program (.seal pc)=MicrocodeEmbedding.instruction (singleBinding (1:Port)).ports Label.seal
      (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem jump (pc next : Label) (bank : Bank) (pos : Port → ℤ) (h : program pc=.jump next) :
    Trace 1 (cfg pc bank pos) (cfg next bank pos) := NativeMicrocode.jump_trace _ _ _ h

theorem zero_trace (xs : List Bool) (pos : Port → ℤ) :
    Trace 1 (cfg .zero ![Counter.marked xs,NativeSealBack.openWord []] pos)
      (cfg (.append 0) ![Counter.marked xs,NativeSealBack.openWord [false]]
        ![pos 0,pos 1+1]) := by
  let z : NativeZipper.Config Port Label :=
    ⟨⟨.zero,![Counter.marked xs,NativeSealBack.openWord []]⟩,pos⟩
  have hr : NativeZipper.run program 1 z=
      ⟨⟨.append 0,![Counter.marked xs,NativeSealBack.openWord [false]]⟩,![pos 0,pos 1+1]⟩ := by
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,z,
      Microcode.single,Microcode.Action.apply,NativeSealBack.openWord,symbols,Tape.write,Tape.moveRight,Tape.read,
      NativeMicrocode.direction,Transpose.Dir.shift]
    constructor <;> funext i <;> fin_cases i <;> simp
  obtain ⟨t,ht,htr⟩ := NativeZipper.trace_of_run program hr
  have he : t=1 := by
    -- The source state is active, so a zero-step trace cannot change its label.
    cases t with
    | zero => cases htr
    | succ t => omega
  simpa [he,z,cfg,workCfg,NativeZipper.Config.denote,Microcode.Config.denote] using htr

@[simp] theorem update_zero {A : Type*} (a b c : A) :
    Function.update ![a,b] (0:Port) c=![c,b] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_one {A : Type*} (a b c : A) :
    Function.update ![a,b] (1:Port) c=![a,c] := by funext i; fin_cases i <;> rfl
@[simp] theorem eta (pos : Port → ℤ) : ![pos 0,pos 1]=pos := by funext i; fin_cases i <;> rfl

 theorem complete_trace (xs : List Bool) (pos : Port → ℤ) :
    ∃ t≤6*xs.length+20,Trace t
      (cfg start ![Counter.marked xs,⟨[],[]⟩] pos)
      (cfg .done ![Counter.marked xs,Counter.marked (false::xs)] pos) := by
  let b0 : Bank := ![Counter.marked xs,⟨[],[]⟩]
  let b1 : Bank := ![Counter.marked xs,NativeSealBack.openWord []]
  let b2 : Bank := ![Counter.marked xs,NativeSealBack.openWord [false]]
  let b3 : Bank := ![Counter.marked xs,NativeSealBack.openWord (false::xs)]
  let b4 : Bank := ![Counter.marked xs,Counter.marked (false::xs)]
  let p1 : Port → ℤ := ![pos 0,pos 1+1]
  let p2 : Port → ℤ := ![pos 0,pos 1+1+xs.length]
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤2,Trace t (cfg start b0 pos) (cfg (.init .done) b1 pos) := by
    simpa [start,b0,b1] using NativeTapeCalls.initialize_call program 1 Label.init init_code b0 pos rfl
  have j0 := jump (.init .done) .zero b1 pos rfl
  have tr1 := zero_trace xs pos
  obtain ⟨t2,h2,tr2⟩ : ∃ t≤4*xs.length+5,Trace t (cfg (.append 0) b2 p1)
      (cfg (.append 7) b3 p2) := by
    obtain ⟨t,ht,htr⟩ := NativeMappedAppend.append_trace id xs [.data false,.start] p1
    have hh := call_pair 0 1 (by decide) Label.append (Microcode.MappedAppendFamily.program id)
      program append_code 0 7 b2 p1 (b2 0) (NativeSealBack.openWord (false::xs)) (p1 0) (p1 1+xs.length) t
    have ht' := hh (by
      have hp : NativeMappedAppend.finalPositions p1 xs.length=p2 := by
        funext i; fin_cases i <;> simp [p1,p2,NativeMappedAppend.finalPositions]
      simpa [workCfg,NativeMappedAppend.cfg,NativeZipper.Config.denote,Microcode.Config.denote,
        Microcode.focus2,Microcode.focus,b2,p1,p2,b3,NativeSealBack.openWord,symbols,
        List.reverse_cons,List.append_assoc,hp] using htr)
    exact ⟨t,ht,by simpa [b2,b3,p1,p2] using ht'⟩
  have j2 := jump (.append 7) (.seal .seal) b3 p2 (by simp [program])
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤2*(false::xs).length+5,Trace t (cfg (.seal .seal) b3 p2)
      (cfg (.seal .done) b4 pos) := by
    simpa [b3,b4,p2,add_assoc,add_comm,add_left_comm] using NativeTapeCalls.seal_call program 1 Label.seal seal_code b3 p2 (false::xs) rfl
  have j3 := jump (.seal .done) .done b4 pos rfl
  have a0 := trace_trans tr0 j0
  have a1 := trace_trans a0 tr1
  have a2 := trace_trans a1 tr2
  have a3 := trace_trans a2 j2
  have a4 := trace_trans a3 tr3
  have a5 := trace_trans a4 j3
  refine ⟨_,?_,a5⟩
  simp only [List.length_cons] at h3
  omega

 theorem value_double (xs : List Bool) : Counter.value (false::xs)=2*Counter.value xs := by
   simp [Counter.value]

end BitWord.NativeDoubleWord
