import TransposeFollowup.NativePairEqualRun
import TransposeFollowup.PreparedPairCalls

/-! Membership of a retained candidate in one physical pair batch. The
found flag is one bit of control; all coordinates remain on work tapes. -/
namespace TransposeFollowup.BatchMembership
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def readBinding : FinitePortBinding (Fin 5) (Fin 7) where
  ports:=⟨![0,1,2,3,4],by decide +kernel⟩
  decode:=fun p => if p=0 then some 0 else if p=1 then some 1 else if p=2 then some 2 else if p=3 then some 3 else if p=4 then some 4 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
def compareBinding : FinitePortBinding (Fin 4) (Fin 7) where
  ports:=⟨![5,6,3,4],by decide +kernel⟩
  decode:=fun p => if p=5 then some 0 else if p=6 then some 1 else if p=3 then some 2 else if p=4 then some 3 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
def fieldPort (second : Bool) : Fin 7 := if second then 4 else 3
def eraseBinding (second : Bool) : FinitePortBinding (Fin 1) (Fin 7) where
  ports:=⟨fun _ => fieldPort second,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=fieldPort second then some 0 else none
  decode_spec:=by intro p j;cases second <;> fin_cases p <;> fin_cases j <;> decide +kernel

inductive Label (small : ℕ)
  | read (found : Bool) (pc : PreparedPair.Label small 0)
  | compare (found : Bool) (pc : NativePairEqual.Label)
  | erase (found second : Bool) (pc : NativeErase.Label)
  | done (found : Bool)
  deriving DecidableEq,Fintype
def start (small : ℕ) (found : Bool) : Label small := .read found (.prepare (.init (.erase 0)))
def program (small : ℕ) : Microcode.Program (Fin 7) (Label small)
  | .read found (.done true) => .jump (.compare found NativePairEqual.start)
  | .read found (.done false) => .jump (.done found)
  | .read found pc => readBinding.instruction (Label.read found) (PreparedPair.program small 0 pc)
  | .compare found (.done equal) => .jump (.erase (found || equal) false 2)
  | .compare found pc => compareBinding.instruction (Label.compare found) (NativePairEqual.program pc)
  | .erase found second pc => if pc=0 then .jump (if second then start small found else .erase found true 2)
    else (eraseBinding second).instruction (Label.erase found second) (NativeErase.program pc)
  | .done _ => .halt

theorem read_code (small : ℕ) (found : Bool) (pc : PreparedPair.Label small 0) (hh : PreparedPair.program small 0 pc≠.halt)
    (_ : PreparedPair.program small 0 pc≠.reject) :
    program small (.read found pc)=MicrocodeEmbedding.instruction readBinding.ports (Label.read found) (PreparedPair.program small 0 pc) := by
  cases pc with
  | done b => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem compare_code (small : ℕ) (found : Bool) (pc : NativePairEqual.Label) (hh : NativePairEqual.program pc≠.halt)
    (_ : NativePairEqual.program pc≠.reject) :
    program small (.compare found pc)=MicrocodeEmbedding.instruction compareBinding.ports (Label.compare found) (NativePairEqual.program pc) := by
  cases pc with
  | done b => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem erase_code (small : ℕ) (found second : Bool) (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt)
    (_ : NativeErase.program pc≠.reject) :
    program small (.erase found second pc)=MicrocodeEmbedding.instruction (eraseBinding second).ports (Label.erase found second) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

abbrev Bank := Fin 7 → Tape Bool
def bank (source template input first second a b : Tape Bool) : Bank := ![source,template,input,first,second,a,b]
def cfg {small : ℕ} (pc : Label small) (s : Bank) (pos : Fin 7 → ℤ) : NativeMicrocode.Config (Fin 7) (Label small) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Fin 7 → ℤ) : MicrocodeEmbedding.Frame (Fin 7) := ⟨fun p => (s p).denote,pos⟩
def advance (pos : Fin 7 → ℤ) (m : ℕ) : Fin 7 → ℤ := fun p => pos p+if p=2 then (m : ℤ) else 0
abbrev Trace (small : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program small)) (NativeMicrocode.Active (program small))
theorem advance_add (pos : Fin 7 → ℤ) (a b : ℕ) : advance (advance pos a) b=advance pos (a+b) := by
  funext p;fin_cases p <;> simp [advance,add_assoc]
theorem advance_zero (pos : Fin 7 → ℤ) : advance pos 0=pos := by funext p;simp [advance]

def liftRead (s : PreparedPair.Bank) (a b : Tape Bool) : Bank := ![s 0,s 1,s 2,s 3,s 4,a,b]
theorem liftRead_bank (source template input first second a b : Tape Bool) :
    liftRead (PreparedPair.bank source template input first second) a b=bank source template input first second a b := by
  funext p;fin_cases p <;> rfl
theorem embed_read (small : ℕ) (found : Bool) (pc : PreparedPair.Label small 0) (s base : PreparedPair.Bank)
    (a b : Tape Bool) (rpos : Fin 5 → ℤ) (pos : Fin 7 → ℤ) :
    MicrocodeEmbedding.embed readBinding.ports (Label.read (small:=small) found) (PreparedPair.cfg pc s rpos)
      (frame (liftRead base a b) pos)=cfg (.read found pc) (liftRead s a b) (readBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed PreparedPair.cfg cfg frame
  simp only [← readBinding.values_eq_extend]
  congr 2
  funext p;fin_cases p <;> rfl
theorem read_positions (pos : Fin 7 → ℤ) : readBinding.values (fun p => pos (readBinding.ports p)) pos=pos := by
  funext p;fin_cases p <;> rfl
theorem read_final_positions (pos : Fin 7 → ℤ) (m : ℕ) :
    readBinding.values (PreparedPair.advance (fun p => pos (readBinding.ports p)) m) pos=advance pos m := by
  funext p;fin_cases p <;> simp [readBinding,FinitePortBinding.values,PreparedPair.advance,advance]

theorem read_pair_call (small : ℕ) (found : Bool) (xs first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (a b : Tape Bool) (pos : Fin 7 → ℤ) :
    ∃ t ≤ PreparedPair.pairBudget small 0 xs,Trace small t
      (cfg (start small found) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ a b) pos)
      (cfg (.read found (.done true)) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(symbols (first++second)).reverse++pre,suffix⟩
        (Counter.marked first) (Counter.marked second) a b) (advance pos (2*(2*xs.length+small)))) := by
  obtain ⟨t,ht,htr⟩:=PreparedPair.pair_trace small 0 xs first second hp hf hs pre suffix (fun p => pos (readBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (small:=small) found) (PreparedPair.program small 0) (program small)
    (frame (liftRead (PreparedPair.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) a b) pos)
    (read_code small found) htr
  simp only [embed_read,read_positions,read_final_positions] at he
  exact ⟨t,ht,by simpa only [liftRead_bank,start,NativePaddedField.padded,List.replicate_zero,List.append_nil] using he⟩

theorem read_stop_call (small : ℕ) (found : Bool) (xs : List Bool) (pre suffix : List (Sym Bool)) (a b : Tape Bool) (pos : Fin 7 → ℤ) :
    ∃ t ≤ PreparedPair.stopBudget small xs,Trace small t
      (cfg (start small found) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ a b) pos)
      (cfg (.read found (.done false)) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨.stop::pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ a b) (advance pos 1)) := by
  obtain ⟨t,ht,htr⟩:=PreparedPair.stop_trace small 0 xs pre suffix (fun p => pos (readBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (small:=small) found) (PreparedPair.program small 0) (program small)
    (frame (liftRead (PreparedPair.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) a b) pos) (read_code small found) htr
  simp only [embed_read,read_positions,read_final_positions] at he
  exact ⟨t,ht,by simpa only [liftRead_bank,start] using he⟩

end TransposeFollowup.BatchMembership
