import BitWord.NativeSplitScan
import BitWord.NativeBankCalls
import TransposeFollowup.NativeMappedAppend
import TransposeFollowup.NativeErase

/-! Stable even/odd splitting on three fixed tapes, with paid initialization,
rewinds, concatenation and scratch cleanup. -/
namespace BitWord.NativeSplit
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop

abbrev Port := Fin 3
abbrev Bank := Port → Tape Bool

def scratch (side : Bool) : Port := if side then 2 else 1

def allBinding : FinitePortBinding Port Port where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p t; simp [eq_comm]

def appendBinding (side : Bool) := pairBinding (scratch side) 0 (by cases side <;> decide)

inductive Label
  | init (side : Bool) (pc : NativeBuffer.Label)
  | scan (pc : NativeSplitScan.Label)
  | seal (port : Fin 3) (pc : NativeSealBack.Label)
  | recycle (pc : NativeBuffer.Label)
  | append (side : Bool) (pc : Microcode.MappedAppendFamily.Label)
  | finish (pc : NativeSealBack.Label)
  | erase (side : Bool) (pc : NativeErase.Label)
  | done
  deriving DecidableEq, Fintype

def start : Label := .init false (.erase 0)

def program : Microcode.Program Port Label
  | .init side .done => .jump (if side then .scan (.scan false) else .init true (.erase 0))
  | .init side pc => (singleBinding (scratch side)).instruction (Label.init side) (NativeBuffer.program pc)
  | .scan .done => .jump (.seal 0 .back)
  | .scan pc => allBinding.instruction Label.scan (NativeSplitScan.program pc)
  | .seal port .done => .jump (if port=0 then .seal 1 .seal else if port=1 then .seal 2 .seal else .recycle (.erase 2))
  | .seal port pc => (singleBinding port).instruction (Label.seal port) (NativeSealBack.program pc)
  | .recycle .done => .jump (.append false 0)
  | .recycle pc => (singleBinding 0).instruction Label.recycle (NativeBuffer.program pc)
  | .append side pc => if pc=7 then .jump (if side then .finish .seal else .append true 0)
      else (appendBinding side).instruction (Label.append side) (Microcode.MappedAppendFamily.program id pc)
  | .finish .done => .jump (.erase false 2)
  | .finish pc => (singleBinding 0).instruction Label.finish (NativeSealBack.program pc)
  | .erase side pc => if pc=0 then .jump (if side then .done else .erase true 2)
      else (singleBinding (scratch side)).instruction (Label.erase side) (NativeErase.program pc)
  | .done => .halt

theorem init_code (side : Bool) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc ≠ .halt) (_ : NativeBuffer.program pc ≠ .reject) :
    program (.init side pc) = MicrocodeEmbedding.instruction (singleBinding (scratch side)).ports
      (Label.init side) (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem scan_code (pc : NativeSplitScan.Label)
    (hh : NativeSplitScan.program pc ≠ .halt) (_ : NativeSplitScan.program pc ≠ .reject) :
    program (.scan pc) = MicrocodeEmbedding.instruction allBinding.ports Label.scan (NativeSplitScan.program pc) := by
  cases pc <;> simp_all [program,NativeSplitScan.program,FinitePortBinding.instruction_eq]

theorem seal_code (port : Port) (pc : NativeSealBack.Label)
    (hh : NativeSealBack.program pc ≠ .halt) (_ : NativeSealBack.program pc ≠ .reject) :
    program (.seal port pc) = MicrocodeEmbedding.instruction (singleBinding port).ports
      (Label.seal port) (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem recycle_code (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc ≠ .halt) (_ : NativeBuffer.program pc ≠ .reject) :
    program (.recycle pc) = MicrocodeEmbedding.instruction (singleBinding 0).ports
      Label.recycle (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem append_code (side : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program id pc ≠ .halt)
    (_ : Microcode.MappedAppendFamily.program id pc ≠ .reject) :
    program (.append side pc) = MicrocodeEmbedding.instruction (appendBinding side).ports
      (Label.append side) (Microcode.MappedAppendFamily.program id pc) := by
  have hp : pc ≠ 7 := by intro h; subst pc; exact hh rfl
  simp only [program,if_neg hp,FinitePortBinding.instruction_eq]

theorem finish_code (pc : NativeSealBack.Label)
    (hh : NativeSealBack.program pc ≠ .halt) (_ : NativeSealBack.program pc ≠ .reject) :
    program (.finish pc) = MicrocodeEmbedding.instruction (singleBinding 0).ports
      Label.finish (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem erase_code (side : Bool) (pc : NativeErase.Label)
    (hh : NativeErase.program pc ≠ .halt) (_ : NativeErase.program pc ≠ .reject) :
    program (.erase side pc) = MicrocodeEmbedding.instruction (singleBinding (scratch side)).ports
      (Label.erase side) (NativeErase.program pc) := by
  have hp : pc ≠ 0 := by intro h; subst pc; exact hh rfl
  simp only [program,if_neg hp,FinitePortBinding.instruction_eq]

abbrev cfg := workCfg (T := Port) (L := Label)
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem jump (pc next : Label) (s : Bank) (pos : Port → ℤ) (h : program pc = .jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) := NativeMicrocode.jump_trace _ _ _ h

theorem initialize_call (side : Bool) (s : Bank) (pos : Port → ℤ)
    (hs : s (scratch side) = ⟨[],[]⟩) :
    ∃ t ≤ 2, Trace t (cfg (.init side (.erase 0)) s pos)
      (cfg (.init side .done) (Function.update s (scratch side) (NativeSealBack.openWord [])) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos (scratch side))
  have hh := call_single (scratch side) (Label.init side) NativeBuffer.program program (init_code side)
    (.erase 0) .done s pos (NativeSealBack.openWord []) (pos (scratch side)) t
  have hh' := hh (by simpa [workCfg,NativeBuffer.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs,NativeSealBack.openWord,BinaryCarry.preparedOutput,symbols] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

theorem seal_call (port : Port) (s : Bank) (pos : Port → ℤ) (xs : List Bool)
    (hs : s port = NativeSealBack.openWord xs) :
    ∃ t ≤ 2*xs.length+5, Trace t (cfg (.seal port .seal) s pos)
      (cfg (.seal port .done) (Function.update s port (Counter.marked xs))
        (Function.update pos port (pos port-xs.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace xs (fun _ => pos port)
  refine ⟨t,ht,call_single port (Label.seal port) NativeSealBack.program program (seal_code port)
    .seal .done s pos (Counter.marked xs) (pos port-xs.length) t ?_⟩
  simpa [workCfg,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,hs] using htr

theorem rewind_source_call (s : Bank) (pos : Port → ℤ) (xs : List Bool)
    (hs : s 0 = ⟨(symbols xs).reverse++[.start],[.stop]⟩) :
    ∃ t ≤ 2*xs.length+4, Trace t (cfg (.seal 0 .back) s pos)
      (cfg (.seal 0 .done) (Function.update s 0 (Counter.marked xs))
        (Function.update pos 0 (pos 0-xs.length))) := by
  have hr := NativeSealBack.seal_run xs (fun _ => pos 0)
  rw [show 2*xs.length+5 = 1+(2*xs.length+4) by omega, NativeZipper.run_add] at hr
  have hfirst : NativeZipper.run NativeSealBack.program 1
      (NativeSealBack.cfg .seal (NativeSealBack.openWord xs) (fun _ => pos 0)) =
      NativeSealBack.cfg .back ⟨(symbols xs).reverse++[.start],[.stop]⟩ (fun _ => pos 0) := by
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
      NativeSealBack.program,NativeSealBack.cfg,NativeSealBack.openWord,Microcode.focus,
      Microcode.single,Microcode.Action.apply,Tape.write,NativeMicrocode.direction,Transpose.Dir.shift]
    constructor <;> funext i <;> fin_cases i <;> simp
  rw [hfirst] at hr
  obtain ⟨t,ht,htr⟩ := NativeZipper.trace_of_run NativeSealBack.program hr
  refine ⟨t,ht,call_single 0 (Label.seal 0) NativeSealBack.program program (seal_code 0)
    .back .done s pos (Counter.marked xs) (pos 0-xs.length) t ?_⟩
  simpa [workCfg,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,hs] using htr

theorem recycle_call (s : Bank) (pos : Port → ℤ) (xs : List Bool) (hs : s 0 = Counter.marked xs) :
    ∃ t ≤ 4*xs.length+6, Trace t (cfg (.recycle (.erase 2)) s pos)
      (cfg (.recycle .done) (Function.update s 0 (NativeSealBack.openWord [])) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.recycle_trace xs (fun _ => pos 0)
  have hh := call_single 0 Label.recycle NativeBuffer.program program recycle_code
    (.erase 2) .done s pos (NativeSealBack.openWord []) (pos 0) t
  have hh' := hh (by simpa [workCfg,NativeBuffer.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs,NativeSealBack.openWord,BinaryCarry.preparedOutput,symbols] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

@[simp] theorem append_positions (a b : ℤ) (n : ℕ) :
    NativeMappedAppend.finalPositions ![a,b] n = ![a,b+n] := by
  funext i; fin_cases i <;> simp [NativeMappedAppend.finalPositions]

theorem append_call (side : Bool) (s : Bank) (pos : Port → ℤ) (xs acc : List Bool)
    (hs : s (scratch side) = Counter.marked xs) (ha : s 0 = NativeSealBack.openWord acc) :
    ∃ t ≤ 4*xs.length+5, Trace t (cfg (.append side 0) s pos)
      (cfg (.append side 7) (Function.update s 0 (NativeSealBack.openWord (acc++xs)))
        (Function.update pos 0 (pos 0+xs.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedAppend.append_trace id xs
    ((symbols acc).reverse++[.start]) ![pos (scratch side),pos 0]
  have hh := call_pair (scratch side) 0 (by cases side <;> decide) (Label.append side)
    (Microcode.MappedAppendFamily.program id) program (append_code side) 0 7 s pos
    (s (scratch side)) (NativeSealBack.openWord (acc++xs)) (pos (scratch side)) (pos 0+xs.length) t
  refine ⟨t,ht,?_⟩
  apply (by simpa only [Function.update_eq_self] using hh)
  simpa [workCfg,NativeMappedAppend.cfg,NativeZipper.Config.denote,Microcode.Config.denote,
    Microcode.focus2,Microcode.focus,hs,ha,NativeSealBack.openWord,
    symbols,List.map_append,List.reverse_append,List.append_assoc] using htr

theorem finish_call (s : Bank) (pos : Port → ℤ) (xs : List Bool)
    (hs : s 0 = NativeSealBack.openWord xs) :
    ∃ t ≤ 2*xs.length+5, Trace t (cfg (.finish .seal) s pos)
      (cfg (.finish .done) (Function.update s 0 (Counter.marked xs))
        (Function.update pos 0 (pos 0-xs.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace xs (fun _ => pos 0)
  refine ⟨t,ht,call_single 0 Label.finish NativeSealBack.program program finish_code
    .seal .done s pos (Counter.marked xs) (pos 0-xs.length) t ?_⟩
  simpa [workCfg,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,hs] using htr

theorem erase_call (side : Bool) (s : Bank) (pos : Port → ℤ) (xs : List Bool)
    (hs : s (scratch side) = Counter.marked xs) :
    ∃ t ≤ 4*xs.length+4, Trace t (cfg (.erase side 2) s pos)
      (cfg (.erase side 0) (Function.update s (scratch side) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun _ => pos (scratch side))
  have hh := call_single (scratch side) (Label.erase side) NativeErase.program program (erase_code side)
    2 0 s pos ⟨[],[]⟩ (pos (scratch side)) t
  have hh' := hh (by simpa [workCfg,NativeErase.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

end BitWord.NativeSplit
