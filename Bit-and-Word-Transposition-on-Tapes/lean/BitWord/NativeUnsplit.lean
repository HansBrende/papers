import BitWord.NativeBoundedCopy
import BitWord.NativeInterleave
import BitWord.NativeResize

/-! In-place inverse stable split, using a physical half-length ruler. -/
namespace BitWord.NativeUnsplit
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames NativeCountedLoop
abbrev Port := Fin 4
abbrev Bank := Port → Tape Bool

def scratch (side : Bool) : Port := if side then 2 else 1

def copyBinding (side : Bool) : FinitePortBinding (Fin 3) Port where
  ports := ⟨![0,scratch side,3],by intro i j h; cases side <;> fin_cases i <;> fin_cases j <;> simp_all [scratch]⟩
  decode := if side then ![some 0,none,some 1,some 2] else ![some 0,some 1,none,some 2]
  decode_spec := by intro p i; cases side <;> fin_cases p <;> fin_cases i <;> decide

def shuffleBinding : FinitePortBinding (Fin 3) Port where
  ports := ⟨![0,1,2],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  decode := ![some 0,some 1,some 2,none]
  decode_spec := by intro p i; fin_cases p <;> fin_cases i <;> decide

inductive Label
  | init (side : Bool) (pc : NativeBuffer.Label)
  | copy (side : Bool) (pc : NativeBoundedCopy.Label)
  | rewind (pc : NativeSealBack.Label)
  | erase (pc : NativeErase.Label)
  | shuffle (pc : NativeInterleave.Label)
  | done
  deriving DecidableEq, Fintype

def start : Label := .init false (.erase 0)
def program : Microcode.Program Port Label
  | .init side .done => .jump (.copy side .scan)
  | .init side pc => (singleBinding (scratch side)).instruction (Label.init side) (NativeBuffer.program pc)
  | .copy side .done => .jump (if side then .rewind .back else .init true (.erase 0))
  | .copy side pc => (copyBinding side).instruction (Label.copy side) (NativeBoundedCopy.program pc)
  | .rewind .done => .jump (.erase 2)
  | .rewind pc => (singleBinding 0).instruction Label.rewind (NativeSealBack.program pc)
  | .erase pc => if pc=0 then .jump (.shuffle NativeInterleave.start)
      else (singleBinding 0).instruction Label.erase (NativeErase.program pc)
  | .shuffle .done => .jump .done
  | .shuffle pc => shuffleBinding.instruction Label.shuffle (NativeInterleave.program pc)
  | .done => .halt

abbrev cfg := workCfg (T := Port) (L := Label)
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem init_code (side : Bool) : NativeTapeCalls.Code program (scratch side) (Label.init side) NativeBuffer.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem copy_code (side : Bool) (pc : NativeBoundedCopy.Label)
    (hh : NativeBoundedCopy.program pc≠.halt) (_ : NativeBoundedCopy.program pc≠.reject) :
    program (.copy side pc)=MicrocodeEmbedding.instruction (copyBinding side).ports
      (Label.copy side) (NativeBoundedCopy.program pc) := by
  cases pc <;> simp_all [program,NativeBoundedCopy.program,FinitePortBinding.instruction_eq]

theorem rewind_code : NativeTapeCalls.Code program 0 Label.rewind NativeSealBack.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem erase_code : NativeTapeCalls.Code program 0 Label.erase NativeErase.program := by
  intro pc hh _
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp only [program,ite_eq_right hp,FinitePortBinding.instruction_eq]

theorem shuffle_code (pc : NativeInterleave.Label)
    (hh : NativeInterleave.program pc≠.halt) (_ : NativeInterleave.program pc≠.reject) :
    program (.shuffle pc)=MicrocodeEmbedding.instruction shuffleBinding.ports Label.shuffle
      (NativeInterleave.program pc) := by
  cases pc <;> simp_all [program,NativeInterleave.program,FinitePortBinding.instruction_eq]

def copyBank (side : Bool) (src dst other clock : Tape Bool) : Bank :=
  if side then ![src,other,dst,clock] else ![src,dst,other,clock]

def shifted (pos : Port → ℤ) (n : ℕ) : Port → ℤ := ![pos 0+n,pos 1,pos 2,pos 3]
@[simp] theorem shifted_zero (pos : Port → ℤ) : shifted pos 0=pos := by
  funext p; fin_cases p <;> simp [shifted]

theorem shifted_add (pos : Port → ℤ) (n m : ℕ) : shifted (shifted pos n) m=shifted pos (n+m) := by
  funext p; fin_cases p <;> simp [shifted,Nat.cast_add,add_assoc]

@[simp] theorem copy_values {A : Type*} (side : Bool) (x : Fin 3 → A) (s : Port → A) :
    (copyBinding side).values x s = if side then ![x 0,s 1,x 1,x 2] else ![x 0,x 1,s 2,x 2] := by
  cases side <;> funext i <;> fin_cases i <;> rfl

@[simp] theorem shuffle_values {A : Type*} (x : Fin 3 → A) (s : Port → A) :
    shuffleBinding.values x s=![x 0,x 1,x 2,s 3] := by funext i; fin_cases i <;> rfl

theorem copy_call (side : Bool) (xs fs : List Bool) (hlen : fs.length=xs.length)
    (sl sr : List (Sym Bool)) (other : Tape Bool) (pos : Port → ℤ) :
    ∃ t≤6*xs.length+5,Trace t
      (cfg (.copy side .scan) (copyBank side ⟨sl,symbols xs++sr⟩
        (NativeSealBack.openWord []) other (Counter.marked fs)) pos)
      (cfg (.copy side .done) (copyBank side ⟨(symbols xs).reverse++sl,sr⟩
        (Counter.marked xs) other (Counter.marked fs)) (shifted pos xs.length)) := by
  let p : Fin 3 → ℤ := ![pos 0,pos (scratch side),pos 3]
  let s := copyBank side ⟨sl,symbols xs++sr⟩ (NativeSealBack.openWord []) other (Counter.marked fs)
  obtain ⟨t,ht,htr⟩ := NativeBoundedCopy.block_trace xs fs hlen sl sr [] p
  have hh := MicrocodeEmbedding.trace_embed (copyBinding side).ports (Label.copy side)
    NativeBoundedCopy.program program (frame s pos) (copy_code side) htr
  change Trace t
    (MicrocodeEmbedding.embed (copyBinding side).ports (Label.copy side)
      (workCfg .scan ![⟨sl,symbols xs++sr⟩,NativeSealBack.openWord [],Counter.marked fs] p) _)
    (MicrocodeEmbedding.embed (copyBinding side).ports (Label.copy side)
      (workCfg .done ![⟨(symbols xs).reverse++sl,sr⟩,Counter.marked xs,Counter.marked fs]
        (NativeBoundedCopy.shift p xs.length 0 0)) _) at hh
  rw [embed_work,embed_work] at hh
  refine ⟨t,ht,?_⟩
  cases side <;> simpa [copy_values,copyBank,s,p,scratch,shifted,NativeBoundedCopy.shift,NativeResize.four_eta] using hh

theorem shuffle_call (a b : List Bool) (hab : a.length=b.length) (clock : Tape Bool) (pos : Port → ℤ) :
    ∃ t≤20*a.length+40,Trace t
      (cfg (.shuffle NativeInterleave.start) ![⟨[],[]⟩,Counter.marked a,Counter.marked b,clock] pos)
      (cfg (.shuffle .done) ![Counter.marked (NativeInterleave.output a b),⟨[],[]⟩,⟨[],[]⟩,clock] pos) := by
  let p : Fin 3 → ℤ := ![pos 0,pos 1,pos 2]
  let s : Bank := ![⟨[],[]⟩,Counter.marked a,Counter.marked b,clock]
  obtain ⟨t,ht,htr⟩ := NativeInterleave.complete_trace a b hab p
  have hh := MicrocodeEmbedding.trace_embed shuffleBinding.ports Label.shuffle
    NativeInterleave.program program (frame s pos) shuffle_code htr
  rw [embed_work,embed_work] at hh
  exact ⟨t,ht,by simpa [shuffle_values,s,p,NativeResize.four_eta] using hh⟩

end BitWord.NativeUnsplit
