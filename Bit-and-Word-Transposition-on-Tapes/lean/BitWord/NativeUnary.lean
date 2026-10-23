import BitWord.NativeTapeCalls
import BitWord.NativeSplitRun
import TransposeFollowup.RadiusClockRun

/-! Preserve a binary word while constructing its unary value. The countdown
uses the shared amortized counter proof. -/
namespace BitWord.NativeUnary
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames NativeCountedLoop
open NativeSplit (update_three_zero update_three_one update_three_two three_eta)
abbrev Port := Fin 3
abbrev Bank := Port → Tape Bool

def copyBinding := pairBinding (0:Port) 1 (by decide)
def fillBinding := pairBinding (1:Port) 2 (by decide)

inductive Label
  | copy (pc : NativeMappedCopy.Label)
  | init (pc : NativeBuffer.Label)
  | fill (pc : CountedFill.Label 1)
  | seal (pc : NativeSealBack.Label)
  | erase (pc : NativeErase.Label)
  | done
  deriving DecidableEq,Fintype

def start : Label := .copy (.init (.erase 0))
def program : Microcode.Program Port Label
  | .copy (.seal .done) => .jump (.init (.erase 0))
  | .copy pc => copyBinding.instruction Label.copy (NativeMappedCopy.program id pc)
  | .init .done => .jump (.fill (.counter 0))
  | .init pc => (singleBinding 2).instruction Label.init (NativeBuffer.program pc)
  | .fill (.counter pc) => if pc=12 then .jump (.seal .seal)
      else fillBinding.instruction Label.fill (CountedFill.program 1 false (.counter pc))
  | .fill pc => fillBinding.instruction Label.fill (CountedFill.program 1 false pc)
  | .seal .done => .jump (.erase 2)
  | .seal pc => (singleBinding 2).instruction Label.seal (NativeSealBack.program pc)
  | .erase pc => if pc=0 then .jump .done else (singleBinding 1).instruction Label.erase (NativeErase.program pc)
  | .done => .halt

abbrev cfg := workCfg (T:=Port) (L:=Label)
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem copy_code (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.copy pc)=MicrocodeEmbedding.instruction copyBinding.ports Label.copy (NativeMappedCopy.program id pc) := by
  have hp : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem init_code : NativeTapeCalls.Code program 2 Label.init NativeBuffer.program := by
  intro pc hh _; cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem fill_code (pc : CountedFill.Label 1) (hh : CountedFill.program 1 false pc≠.halt)
    (_ : CountedFill.program 1 false pc≠.reject) :
    program (.fill pc)=MicrocodeEmbedding.instruction fillBinding.ports Label.fill (CountedFill.program 1 false pc) := by
  have hp : pc≠.counter 12 := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem seal_code : NativeTapeCalls.Code program 2 Label.seal NativeSealBack.program := by
  intro pc hh _; cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem erase_code : NativeTapeCalls.Code program 1 Label.erase NativeErase.program := by
  intro pc hh _
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp only [program,ite_eq_right hp,FinitePortBinding.instruction_eq]

theorem copy_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t≤6*xs.length+14,Trace t
      (cfg start ![Counter.marked xs,⟨[],[]⟩,⟨[],[]⟩] pos)
      (cfg (.copy (.seal .done)) ![Counter.marked xs,Counter.marked xs,⟨[],[]⟩] pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs ![pos 0,pos 1]
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports Label.copy (NativeMappedCopy.program id) program
    (frame ![Counter.marked xs,⟨[],[]⟩,⟨[],[]⟩] pos) copy_code htr
  have hcfg (pc : NativeMappedCopy.Label) (a b : Tape Bool) (p : Fin 2 → ℤ) :
      NativeMappedCopy.cfg pc a b p=workCfg pc ![a,b] p := by
    unfold NativeMappedCopy.cfg workCfg
    congr 2; funext i; fin_cases i <;> rfl
  simp only [hcfg] at he
  rw [embed_work,embed_work] at he
  exact ⟨t,ht,by simpa [start,copyBinding,pair_values] using he⟩

def filledPos (pos : Port → ℤ) (n : ℕ) : Port → ℤ := ![pos 0,pos 1,pos 2+n]

theorem fill_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t≤11*Counter.value xs+8+4*xs.length,Trace t
      (cfg (.fill (.counter 0)) ![Counter.marked xs,Counter.marked xs,NativeSealBack.openWord []] pos)
      (cfg (.fill (.counter 12)) ![Counter.marked xs,Counter.marked (List.replicate xs.length true),
        NativeSealBack.openWord (List.replicate (Counter.value xs) false)] (filledPos pos (Counter.value xs))) := by
  let p : Fin 2 → ℤ := ![pos 1,pos 2]
  obtain ⟨t,ht,htr⟩ := CountedFill.fill_trace 1 false xs [] p
  have he := MicrocodeEmbedding.trace_embed fillBinding.ports Label.fill (CountedFill.program 1 false) program
    (frame ![Counter.marked xs,Counter.marked xs,NativeSealBack.openWord []] pos) fill_code htr
  have hcfg (pc : CountedFill.Label 1) (fuel acc : List Bool) :
      (CountedFill.cfg pc fuel acc p).denote = workCfg pc
        ![Counter.marked fuel,NativeSealBack.openWord acc] ![pos 1,pos 2+acc.length] := by
    unfold CountedFill.cfg NativeZipper.Config.denote Microcode.Config.denote workCfg
    congr 1
    · congr 1; funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [CountedFill.positions,p]
  simp only [hcfg,embed_work] at he
  refine ⟨t,by omega,?_⟩
  have hpos : Function.update (Function.update pos (1:Port) (pos 1)) 2 (pos 2)=pos := by simp
  have hu : Function.update pos (2:Port) (pos 2+Counter.value xs)=filledPos pos (Counter.value xs) := by
    funext i; fin_cases i <;> simp [filledPos]
  simpa [fillBinding,pair_values,hu] using he

theorem jump (pc next : Label) (s : Bank) (pos : Port → ℤ) (h : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) := NativeMicrocode.jump_trace _ _ _ h

theorem complete_trace (xs : List Bool) (pos : Port → ℤ) :
    ∃ t≤13*Counter.value xs+14*xs.length+40,Trace t
      (cfg start ![Counter.marked xs,⟨[],[]⟩,⟨[],[]⟩] pos)
      (cfg .done ![Counter.marked xs,⟨[],[]⟩,Counter.marked (List.replicate (Counter.value xs) false)] pos) := by
  let z : Tape Bool := ⟨[],[]⟩
  let out := List.replicate (Counter.value xs) false
  let ones := List.replicate xs.length true
  let b1 : Bank := ![Counter.marked xs,Counter.marked xs,z]
  let b2 : Bank := ![Counter.marked xs,Counter.marked xs,NativeSealBack.openWord []]
  let b3 : Bank := ![Counter.marked xs,Counter.marked ones,NativeSealBack.openWord out]
  let b4 : Bank := ![Counter.marked xs,Counter.marked ones,Counter.marked out]
  let b5 : Bank := ![Counter.marked xs,z,Counter.marked out]
  let p3 := filledPos pos (Counter.value xs)
  obtain ⟨t0,h0,tr0⟩ := copy_call xs pos
  have j0 := jump (.copy (.seal .done)) (.init (.erase 0)) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤2,Trace t (cfg (.init (.erase 0)) b1 pos) (cfg (.init .done) b2 pos) := by
    simpa [b1,b2,z] using NativeTapeCalls.initialize_call program 2 Label.init init_code b1 pos rfl
  have j1 := jump (.init .done) (.fill (.counter 0)) b2 pos rfl
  obtain ⟨t2,h2,tr2⟩ := fill_call xs pos
  have j2 := jump (.fill (.counter 12)) (.seal .seal) b3 p3 rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤2*out.length+5,Trace t
      (cfg (.seal .seal) b3 p3) (cfg (.seal .done) b4 pos) := by
    simpa [b3,b4,p3,filledPos,out] using NativeTapeCalls.seal_call program 2 Label.seal seal_code b3 p3 out rfl
  have j3 := jump (.seal .done) (.erase 2) b4 pos rfl
  obtain ⟨t4,h4,tr4⟩ : ∃ t≤4*ones.length+4,Trace t (cfg (.erase 2) b4 pos) (cfg (.erase 0) b5 pos) := by
    simpa [b4,b5,z] using NativeTapeCalls.erase program 1 Label.erase erase_code b4 pos ones rfl
  have j4 := jump (.erase 0) .done b5 pos rfl
  have s0 := trace_trans tr0 j0
  have s1 := trace_trans tr1 j1
  have s2 := trace_trans tr2 j2
  have s3 := trace_trans tr3 j3
  have s4 := trace_trans tr4 j4
  have acc1 := trace_trans s0 s1
  have acc2 := trace_trans acc1 s2
  have acc3 := trace_trans acc2 s3
  have acc4 := trace_trans acc3 s4
  refine ⟨_,?_,acc4⟩
  simp only [out,ones,List.length_replicate] at h3 h4
  omega

end BitWord.NativeUnary
