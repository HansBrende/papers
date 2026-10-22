import TransposeFollowup.BinaryCompareRun
import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeCountedLoop

/-! Equality of two ordered pairs of binary words. Both pairs and all
four heads are preserved. An unequal first field skips the second test. -/
namespace TransposeFollowup.NativePairEqual
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def comparePort (second : Bool) : Fin 2 → Fin 4 := if second then ![1,3] else ![0,2]
def compareBinding (second : Bool) : FinitePortBinding (Fin 2) (Fin 4) where
  ports:=⟨comparePort second,by cases second <;> decide +kernel⟩
  decode:=fun p => if p=comparePort second 0 then some 0 else if p=comparePort second 1 then some 1 else none
  decode_spec:=by intro p j;cases second <;> fin_cases p <;> fin_cases j <;> decide +kernel

inductive Label
  | compare (second : Bool) (pc : BinaryCompare.Label)
  | done (equal : Bool)
  deriving DecidableEq,Fintype

def start : Label := .compare false (.scan .equal)
def program : Microcode.Program (Fin 4) Label
  | .compare false (.done r) => if r=.equal then .jump (.compare true (.scan .equal)) else .jump (.done false)
  | .compare true (.done r) => .jump (.done (decide (r=.equal)))
  | .compare second pc => (compareBinding second).instruction (Label.compare second) (BinaryCompare.program pc)
  | .done _ => .halt

theorem compare_code (second : Bool) (pc : BinaryCompare.Label) (hh : BinaryCompare.program pc≠.halt)
    (_ : BinaryCompare.program pc≠.reject) :
    program (.compare second pc)=MicrocodeEmbedding.instruction (compareBinding second).ports (Label.compare second) (BinaryCompare.program pc) := by
  cases pc with
  | done _ => exact False.elim (hh rfl)
  | _ => cases second <;> simp only [program,FinitePortBinding.instruction_eq]

def bank (a1 a2 b1 b2 : Tape Bool) : Fin 4 → Tape Bool := ![a1,a2,b1,b2]
def cfg (pc : Label) (s : Fin 4 → Tape Bool) (pos : Fin 4 → ℤ) : NativeMicrocode.Config (Fin 4) Label :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Fin 4 → Tape Bool) (pos : Fin 4 → ℤ) : MicrocodeEmbedding.Frame (Fin 4) := ⟨fun p => (s p).denote,pos⟩
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem embed_compare (second : Bool) (pc : BinaryCompare.Label) (a b : Tape Bool) (s : Fin 4 → Tape Bool)
    (pos : Fin 4 → ℤ) :
    MicrocodeEmbedding.embed (compareBinding second).ports (Label.compare second)
      (BinaryCompare.cfg pc a b (fun p => pos (comparePort second p))).denote (frame s pos)=
      cfg (.compare second pc) (Function.update (Function.update s (comparePort second 0) a) (comparePort second 1) b) pos := by
  unfold MicrocodeEmbedding.embed BinaryCompare.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← (compareBinding second).values_eq_extend]
  congr 2 <;> funext p <;> cases second <;> fin_cases p <;> rfl

theorem compare_call (second : Bool) (a b : List Bool) (hw : a.length=b.length)
    (s : Fin 4 → Tape Bool) (ha : s (comparePort second 0)=BinaryCompare.marked a)
    (hb : s (comparePort second 1)=BinaryCompare.marked b) (pos : Fin 4 → ℤ) :
    ∃ t ≤ 5*a.length+6,Trace t (cfg (.compare second (.scan .equal)) s pos)
      (cfg (.compare second (.done (BinaryCompare.numeric .equal (BinaryCompare.value a) (BinaryCompare.value b)))) s pos) := by
  obtain ⟨t,ht,htr⟩:=BinaryCompare.comparison_trace a b hw (fun p => pos (comparePort second p))
  have he:=MicrocodeEmbedding.trace_embed (compareBinding second).ports (Label.compare second) BinaryCompare.program program
    (frame s pos) (compare_code second) htr
  exact ⟨t,ht,by simpa only [embed_compare,← ha,← hb,Function.update_eq_self] using he⟩

theorem jump_trace (pc next : Label) (s : Fin 4 → Tape Bool) (pos : Fin 4 → ℤ) (h : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

def samePair (a b : List Bool × List Bool) : Bool :=
  decide ((BinaryCompare.value a.1,BinaryCompare.value a.2)=(BinaryCompare.value b.1,BinaryCompare.value b.2))

theorem numeric_equal_iff (a b : ℕ) : BinaryCompare.numeric .equal a b=.equal ↔ a=b := by
  unfold BinaryCompare.numeric
  split_ifs <;> simp_all <;> omega

end TransposeFollowup.NativePairEqual
