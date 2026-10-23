import BitWord.NativeTapeCalls
import TransposeFollowup.PreparedPairCalls

/-! Pad one marked binary word by the length of a second word and a fixed
constant. Both source words and all heads are preserved. -/
namespace BitWord.NativeCrossPad
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames NativeCountedLoop
set_option autoImplicit false
abbrev Port := Fin 3
abbrev Bank := Port → Tape Bool

def source (zero : Bool) : Port := if zero then 1 else 0
def appendBinding (zero : Bool) := pairBinding (source zero) (2 : Port) (by cases zero <;> decide)
def tailBinding := pairBinding (0 : Port) (2 : Port) (by decide)
def mapBit (zero : Bool) : Bool → Bool := if zero then fun _ => false else id

def padded (C : ℕ) (xs ys : List Bool) := xs++List.replicate (ys.length+C) false
@[simp] theorem padded_length (C : ℕ) (xs ys : List Bool) :
    (padded C xs ys).length=xs.length+ys.length+C := by simp [padded]; omega
@[simp] theorem padded_value (C : ℕ) (xs ys : List Bool) :
    Counter.value (padded C xs ys)=Counter.value xs := PaddedWord.value_append_zeroes _ _

inductive Label (C : ℕ)
  | init (pc : NativeBuffer.Label)
  | append (zero : Bool) (pc : Microcode.MappedAppendFamily.Label)
  | tail (pc : PaddedWord.Label C)
  deriving DecidableEq, Fintype

def start (C : ℕ) : Label C := .init (.erase 0)
def program (C : ℕ) : Microcode.Program Port (Label C)
  | .init .done => .jump (.append false 0)
  | .init pc => (singleBinding 2).instruction Label.init (NativeBuffer.program pc)
  | .append z pc => if pc=7 then
      .jump (if z then .tail (.fill ⟨C,by omega⟩) else .append true 0)
      else (appendBinding z).instruction (Label.append z) (Microcode.MappedAppendFamily.program (mapBit z) pc)
  | .tail pc => tailBinding.instruction Label.tail (PaddedWord.program C id pc)

abbrev cfg {C : ℕ} := workCfg (T:=Port) (L:=Label C)
abbrev Trace (C : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program C))
  (NativeMicrocode.Active (program C))

theorem init_code (C : ℕ) : NativeTapeCalls.Code (program C) 2 Label.init NativeBuffer.program := by
  intro pc hh _; cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]
theorem append_code (C : ℕ) (z : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program (mapBit z) pc ≠ .halt)
    (_ : Microcode.MappedAppendFamily.program (mapBit z) pc ≠ .reject) :
    program C (.append z pc)=MicrocodeEmbedding.instruction (appendBinding z).ports
      (Label.append z) (Microcode.MappedAppendFamily.program (mapBit z) pc) := by
  have hp : pc ≠ 7 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]
theorem tail_code (C : ℕ) (pc : PaddedWord.Label C)
    (_ : PaddedWord.program C id pc ≠ .halt) (_ : PaddedWord.program C id pc ≠ .reject) :
    program C (.tail pc)=MicrocodeEmbedding.instruction tailBinding.ports Label.tail
      (PaddedWord.program C id pc) := tailBinding.instruction_eq _ _

theorem append_call (C : ℕ) (z : Bool) (xs acc : List Bool) (s : Bank) (pos : Port → ℤ)
    (hs : s (source z)=Counter.marked xs) (ht : s 2=NativeSealBack.openWord acc) :
    ∃ t ≤ 4*xs.length+5,Trace C t (cfg (.append z 0) s pos)
      (cfg (.append z 7) (Function.update s 2 (NativeSealBack.openWord (acc++xs.map (mapBit z))))
        (Function.update pos 2 (pos 2+xs.length))) := by
  obtain ⟨t,htime,htr⟩ := NativeMappedAppend.append_trace (mapBit z) xs
    ((symbols acc).reverse++[.start]) ![pos (source z),pos 2]
  have hh := call_pair (source z) 2 (by cases z <;> decide) (Label.append (C:=C) z)
    (Microcode.MappedAppendFamily.program (mapBit z)) (program C) (append_code C z)
    0 7 s pos (s (source z)) (NativeSealBack.openWord (acc++xs.map (mapBit z)))
    (pos (source z)) (pos 2+xs.length) t
  have hpos : NativeMappedAppend.finalPositions ![pos (source z),pos 2] xs.length=
      ![pos (source z),pos 2+xs.length] := by funext i; fin_cases i <;> simp [NativeMappedAppend.finalPositions]
  rw [hpos] at htr
  have hr := hh (by simpa [workCfg,hs,ht,NativeMappedAppend.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus2,Microcode.focus,NativeSealBack.openWord,
    NativeMappedAppend.finalPositions,symbols,List.reverse_append,List.append_assoc] using htr)
  exact ⟨t,htime,by simpa only [Function.update_eq_self] using hr⟩

theorem tail_call (C : ℕ) (acc : List Bool) (s : Bank) (pos : Port → ℤ)
    (ht : s 2=NativeSealBack.openWord acc) :
    ∃ t ≤ 2*acc.length+3*C+6,Trace C t (cfg (.tail (.fill ⟨C,by omega⟩)) s pos)
      (cfg (.tail (.seal .done)) (Function.update s 2 (Counter.marked (acc++List.replicate C false)))
        (Function.update pos 2 (pos 2-acc.length))) := by
  obtain ⟨t,htime,htr⟩ := NativePaddedField.tail_trace C (s 0) acc ![pos 0,pos 2]
  have hh := call_pair 0 2 (by decide) (Label.tail (C:=C)) (PaddedWord.program C id)
    (program C) (tail_code C) (.fill ⟨C,by omega⟩) (.seal .done) s pos (s 0)
    (Counter.marked (acc++List.replicate C false)) (pos 0) (pos 2-acc.length) t
  have hb (x y : Tape Bool) : NativeMappedCopy.bank x y = ![x,y] := by funext i; fin_cases i <;> rfl
  have hpos : Function.update ![pos 0,pos 2] 1 (pos 2-acc.length)=![pos 0,pos 2-acc.length] := by
    funext i; fin_cases i <;> rfl
  have hr := hh (by simpa [workCfg,ht,PaddedWord.cfg,hb,NativePaddedField.padded,hpos] using htr)
  exact ⟨t,htime,by simpa only [Function.update_eq_self] using hr⟩

theorem jump (C : ℕ) (pc next : Label C) (s : Bank) (pos : Port → ℤ)
    (h : program C pc=.jump next) : Trace C 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem complete_trace (C : ℕ) (xs ys : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 6*(xs.length+ys.length)+3*C+21,Trace C t
      (cfg (start C) ![Counter.marked xs,Counter.marked ys,⟨[],[]⟩] pos)
      (cfg (.tail (.seal .done)) ![Counter.marked xs,Counter.marked ys,Counter.marked (padded C xs ys)] pos) := by
  let b0 : Bank := ![Counter.marked xs,Counter.marked ys,⟨[],[]⟩]
  let b1 := Function.update b0 2 (NativeSealBack.openWord [])
  let b2 := Function.update b1 2 (NativeSealBack.openWord xs)
  let a := xs++List.replicate ys.length false
  let b3 := Function.update b2 2 (NativeSealBack.openWord a)
  let p1 := Function.update pos 2 (pos 2+xs.length)
  let p2 := Function.update p1 2 (p1 2+ys.length)
  obtain ⟨t0,h0,tr0⟩ := NativeTapeCalls.initialize_call (program C) 2 Label.init (init_code C) b0 pos rfl
  have j0 := jump C (.init .done) (.append false 0) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ := append_call C false xs [] b1 pos rfl rfl
  simp only [mapBit,Bool.false_eq_true,↓reduceIte,List.map_id,List.nil_append] at tr1
  have j1 := jump C (.append false 7) (.append true 0) b2 p1 rfl
  obtain ⟨t2,h2,tr2⟩ := append_call C true ys xs b2 p1 rfl rfl
  simp only [mapBit,↓reduceIte,List.map_const'] at tr2
  have j2 := jump C (.append true 7) (.tail (.fill ⟨C,by omega⟩)) b3 p2 rfl
  obtain ⟨t3,h3,tr3⟩ := tail_call C a b3 p2 rfl
  have ho : Function.update b3 2 (Counter.marked (a++List.replicate C false))=
      ![Counter.marked xs,Counter.marked ys,Counter.marked (padded C xs ys)] := by
    funext p; fin_cases p <;> simp [b3,b2,b1,b0,a,padded,List.append_assoc]
  have hp : Function.update p2 2 (p2 2-a.length)=pos := by
    funext p; fin_cases p <;> simp [p2,p1,a]
  rw [ho,hp] at tr3
  refine ⟨_,?_,trace_trans tr0 (trace_trans j0 (trace_trans tr1 (trace_trans j1
    (trace_trans tr2 (trace_trans j2 tr3)))))⟩
  simp [a] at h3
  omega

end BitWord.NativeCrossPad
