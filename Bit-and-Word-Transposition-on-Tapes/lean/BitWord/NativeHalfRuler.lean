import BitWord.NativeDoubleWord
import BitWord.NativePowerTwoRun
import BitWord.NativeBindingCalls
import BitWord.NativeTapeCalls
import TransposeFollowup.NativeCounter

/-! A literal caller constructs the half-bank ruler from a retained binary n.
It doubles n, decrements the temporary exponent once, calls the checked power
ruler routine, and clears the temporary exponent. -/
namespace BitWord.NativeHalfRuler
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop
set_option autoImplicit false
noncomputable section
abbrev Port := NativePowerTwo.Port ⊕ Unit
abbrev Bank := Port → Tape Bool
def parameter : Port := .inr ()
def exponent : Port := .inl .source
def result : Port := .inl .result
def doubleBinding := pairBinding parameter exponent (by simp [parameter,exponent])
def powerBinding : FinitePortBinding NativePowerTwo.Port Port where
  ports := ⟨Sum.inl,Sum.inl_injective⟩
  decode := fun p => match p with | .inl i => some i | .inr _ => none
  decode_spec := by intro p i; cases p <;> simp [eq_comm]
inductive Label
  | double (pc : NativeDoubleWord.Label)
  | decrement (pc : Microcode.DecrementFamily.Label)
  | power (pc : NativePowerTwo.Label)
  | erase (pc : NativeErase.Label)
  | done
  deriving DecidableEq,Fintype
def start : Label := .double NativeDoubleWord.start
def program : Microcode.Program Port Label
  | .double .done => .jump (.decrement 0)
  | .double pc => doubleBinding.instruction Label.double (NativeDoubleWord.program pc)
  | .decrement pc => if pc=11 then .jump (.power NativePowerTwo.start) else
      (singleBinding exponent).instruction Label.decrement (Microcode.DecrementFamily.program pc)
  | .power .done => .jump (.erase 2)
  | .power pc => powerBinding.instruction Label.power (NativePowerTwo.program pc)
  | .erase pc => if pc=0 then .jump .done else
      (singleBinding exponent).instruction Label.erase (NativeErase.program pc)
  | .done => .halt
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)
abbrev cfg := workCfg (T:=Port) (L:=Label)
def bank (param exp ruler : Tape Bool) : Bank := Sum.elim
  (fun p => match p with | .source => exp | .result => ruler | _ => ⟨[],[]⟩) (fun _ => param)
@[simp] theorem bank_update_exponent (p e r v : Tape Bool) :
    Function.update (bank p e r) exponent v=bank p v r := by
  funext i; cases i with
  | inl i => cases i <;> simp [bank,exponent]
  | inr i => simp [bank,exponent]
@[simp] theorem power_values {A : Type*} (a : NativePowerTwo.Port → A) (f : Port → A) :
    powerBinding.values a f=Sum.elim a (fun _ => f parameter) := by
  funext i; cases i <;> rfl

theorem double_code (pc : NativeDoubleWord.Label)
    (hh : NativeDoubleWord.program pc≠.halt) (_ : NativeDoubleWord.program pc≠.reject) :
    program (.double pc)=MicrocodeEmbedding.instruction doubleBinding.ports Label.double
      (NativeDoubleWord.program pc) := by
  cases pc <;> simp_all [program,NativeDoubleWord.program,FinitePortBinding.instruction_eq]
theorem decrement_code (pc : Microcode.DecrementFamily.Label)
    (hh : Microcode.DecrementFamily.program pc≠.halt) (_ : Microcode.DecrementFamily.program pc≠.reject) :
    program (.decrement pc)=MicrocodeEmbedding.instruction (singleBinding exponent).ports Label.decrement
      (Microcode.DecrementFamily.program pc) := by
  have hp : pc≠11 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]
theorem power_code (pc : NativePowerTwo.Label)
    (hh : NativePowerTwo.program pc≠.halt) (_ : NativePowerTwo.program pc≠.reject) :
    program (.power pc)=MicrocodeEmbedding.instruction powerBinding.ports Label.power
      (NativePowerTwo.program pc) := by
  cases pc <;> simp_all [program,NativePowerTwo.program,FinitePortBinding.instruction_eq]
theorem erase_code (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program (.erase pc)=MicrocodeEmbedding.instruction (singleBinding exponent).ports Label.erase
      (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]
theorem jump (pc next : Label) (s : Bank) (pos : Port → ℤ) (h : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) := NativeMicrocode.jump_trace _ _ _ h

def exponentWord (xs : List Bool) := Counter.decrement (false::xs)
def budget (xs : List Bool) := 6*xs.length+20+2*Counter.stepCost (false::xs)+
  NativePowerTwo.budget (exponentWord xs)+4*(exponentWord xs).length+8

theorem exponent_value (xs : List Bool) (hx : 0<Counter.value xs) :
    Counter.value (exponentWord xs)=2*Counter.value xs-1 := by
  have hz : Counter.isZero (false::xs)=false := by
    cases he : Counter.isZero (false::xs)
    · rfl
    · have hv := (Counter.value_zero_iff (false::xs)).mpr he
      rw [NativeDoubleWord.value_double] at hv
      omega
  have hd := Counter.decrement_value (false::xs) hz
  rw [NativeDoubleWord.value_double] at hd
  dsimp [exponentWord]
  omega

/-- All five tapes start with only the parameter populated. The result is a
unary half-volume ruler, and the parameter and all absolute heads are retained. -/
theorem complete_trace (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) :
    ∃ t≤budget xs,Trace t
      (cfg start (bank (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩) pos)
      (cfg .done (bank (Counter.marked xs) ⟨[],[]⟩
        (Counter.marked (List.replicate (2^(2*Counter.value xs-1)) true))) pos) := by
  let z : Tape Bool := ⟨[],[]⟩
  let p := Counter.marked xs
  let e := false::xs
  let f := exponentWord xs
  let r := Counter.marked (NativePowerTwo.ruler f)
  let b0 := bank p z z
  let b1 := bank p (Counter.marked e) z
  let b2 := bank p (Counter.marked f) z
  let b3 := bank p (Counter.marked f) r
  let b4 := bank p z r
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤6*xs.length+20,Trace t (cfg start b0 pos) (cfg (.double .done) b1 pos) := by
    obtain ⟨t,ht,htr⟩ := NativeDoubleWord.complete_trace xs ![pos parameter,pos exponent]
    have hh := call_pair parameter exponent (by simp [parameter,exponent]) Label.double
      NativeDoubleWord.program program double_code NativeDoubleWord.start .done b0 pos
      (b0 parameter) (Counter.marked e) (pos parameter) (pos exponent) t
      (by simpa [b0,bank,parameter,exponent,p,z,e] using htr)
    exact ⟨t,ht,by simpa [start,b0,b1,e] using hh⟩
  have j0 := jump (.double .done) (.decrement 0) b1 pos rfl
  have hz : Counter.isZero e=false := by
    cases he : Counter.isZero e
    · rfl
    · have hv := (Counter.value_zero_iff e).mpr he
      simp only [e,NativeDoubleWord.value_double] at hv
      omega
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤2*Counter.stepCost e,Trace t (cfg (.decrement 0) b1 pos)
      (cfg (.decrement 11) b2 pos) := by
    obtain ⟨t,ht,htr⟩ := NativeCounter.decrement_trace e (fun _ => pos exponent)
    have hc : (NativeCounter.cfg 0 e (fun _ => pos exponent)).denote=
        workCfg 0 (fun _ => b1 exponent) (fun _ => pos exponent) := by
      simp [NativeCounter.cfg,NativeZipper.Config.denote,Microcode.Config.denote,workCfg,b1,bank,exponent,Microcode.focus]
    have hf : (NativeCounter.cfg (NativeCounter.returnLabel e) (Counter.decrement e)
        (fun _ => pos exponent)).denote=workCfg 11 (fun _ => Counter.marked f) (fun _ => pos exponent) := by
      simp [NativeCounter.cfg,NativeZipper.Config.denote,Microcode.Config.denote,workCfg,NativeCounter.returnLabel,hz,
        Microcode.focus,f,exponentWord,e]
    rw [hc,hf] at htr
    have hh := call_single exponent Label.decrement Microcode.DecrementFamily.program program decrement_code
      0 11 b1 pos (Counter.marked f) (pos exponent) t htr
    exact ⟨t,ht,by simpa [b1,b2] using hh⟩
  have j1 := jump (.decrement 11) (.power NativePowerTwo.start) b2 pos (by simp [program])
  obtain ⟨t2,h2,tr2⟩ : ∃ t≤NativePowerTwo.budget f,Trace t (cfg (.power NativePowerTwo.start) b2 pos)
      (cfg (.power .done) b3 pos) := by
    obtain ⟨t,ht,htr⟩ := NativePowerTwo.complete_trace f (fun i => pos (.inl i))
    have hproj : (fun i => b2 (powerBinding.ports i))=NativePowerTwo.initial f := by
      funext i; cases i <;> rfl
    have hh := NativeBindingCalls.restoring_call powerBinding Label.power NativePowerTwo.program program
      power_code NativePowerTwo.start .done b2 pos (NativePowerTwo.final f) t
      (by
        rw [hproj]
        simpa only [NativePowerTwo.cfg,workCfg,powerBinding,Function.Embedding.coeFn_mk] using htr)
    refine ⟨t,ht,?_⟩
    have hv : powerBinding.values (NativePowerTwo.final f) b2=b3 := by
      funext i; cases i with
      | inl i => cases i <;> simp [power_values,NativePowerTwo.final,NativePowerTwo.bank,b2,b3,bank,r]
      | inr i => simp [power_values,b2,b3,bank,parameter]
    simpa only [hv] using hh
  have j2 := jump (.power .done) (.erase 2) b3 pos rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤4*f.length+4,Trace t (cfg (.erase 2) b3 pos) (cfg (.erase 0) b4 pos) := by
    simpa [b3,b4] using NativeTapeCalls.erase program exponent Label.erase erase_code b3 pos f rfl
  have j3 := jump (.erase 0) .done b4 pos (by simp [program])
  have a0 := trace_trans tr0 j0
  have a1 := trace_trans a0 tr1
  have a2 := trace_trans a1 j1
  have a3 := trace_trans a2 tr2
  have a4 := trace_trans a3 j2
  have a5 := trace_trans a4 tr3
  have a6 := trace_trans a5 j3
  refine ⟨t0+1+t1+1+t2+1+t3+1,?_,?_⟩
  · dsimp [budget]; dsimp [e,f] at h1 h2 h3; omega
  · simpa only [b0,b4,p,r,f,z,NativePowerTwo.ruler,exponent_value xs hx] using a6
/-- The retained parameter can be padded: the bound explicitly includes its
physical word length as well as the generated bank volume. -/
theorem budget_bound (xs : List Bool) (hx : 0<Counter.value xs) :
    budget xs ≤ 200*(2^(2*Counter.value xs)+xs.length+1) := by
  have hc := NativeCounter.native_sequence_budget 1 (false::xs)
  simp only [Counter.totalCost,List.length_cons] at hc
  have hl : (exponentWord xs).length=xs.length+1 := by
    simp [exponentWord,Counter.length_decrement]
  have he := exponent_value xs hx
  have hv : Counter.value xs ≤ 2^(2*Counter.value xs) := by
    exact (Nat.le_mul_of_pos_left _ (by decide : 0<2)).trans
      (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hp : 2^(2*Counter.value xs-1)≤2^(2*Counter.value xs) :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have ho : 1≤2^(2*Counter.value xs) := Nat.succ_le_of_lt (by positivity)
  have hs : 2*Counter.value xs-1 ≤ 2*Counter.value xs := Nat.sub_le _ _
  unfold budget NativePowerTwo.budget
  rw [hl,he]
  nlinarith

end
end BitWord.NativeHalfRuler
