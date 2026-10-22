import TransposeFollowup.PreparedPairCalls

/-! A real batch loop: read a pair, append its two padded fields, erase
both temporary fields, and return to the reader. STOP is copied once.
The record count is not a parameter of the finite program. -/
namespace TransposeFollowup.NormalizedBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def readBinding : FinitePortBinding (Fin 5) (Fin 6) where
  ports:=⟨![0,1,2,3,4],by decide +kernel⟩
  decode:=fun p => if p=0 then some 0 else if p=1 then some 1 else if p=2 then some 2 else if p=3 then some 3 else if p=4 then some 4 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
def fieldPort (second : Bool) : Fin 6 := if second then 4 else 3
def appendBinding (second : Bool) : FinitePortBinding (Fin 2) (Fin 6) where
  ports:=⟨![fieldPort second,5],by cases second <;> decide +kernel⟩
  decode:=fun p => if p=fieldPort second then some 0 else if p=5 then some 1 else none
  decode_spec:=by intro p j;cases second <;> fin_cases p <;> fin_cases j <;> decide +kernel
def eraseBinding (second : Bool) : FinitePortBinding (Fin 1) (Fin 6) where
  ports:=⟨fun _ => fieldPort second,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=fieldPort second then some 0 else none
  decode_spec:=by intro p j;cases second <;> fin_cases p <;> fin_cases j <;> decide +kernel

inductive Label (small pad : ℕ)
  | read (pc : PreparedPair.Label small pad)
  | append (second : Bool) (pc : Microcode.MappedAppendFamily.Label)
  | erase (second : Bool) (pc : NativeErase.Label)
  | done
  deriving DecidableEq,Fintype

def start (small pad : ℕ) : Label small pad := .read (.prepare (.init (.erase 0)))
def program (small pad : ℕ) : Microcode.Program (Fin 6) (Label small pad)
  | .read (.done true) => .jump (.append false 0)
  | .read (.done false) => .act (Microcode.single 5 ⟨some .stop,.right⟩) .done
  | .read pc => readBinding.instruction Label.read (PreparedPair.program small pad pc)
  | .append second pc => if pc=7 then .jump (if second then .erase false 2 else .append true 0)
    else (appendBinding second).instruction (Label.append second) (Microcode.MappedAppendFamily.program id pc)
  | .erase second pc => if pc=0 then .jump (if second then start small pad else .erase true 2)
    else (eraseBinding second).instruction (Label.erase second) (NativeErase.program pc)
  | .done => .halt

theorem read_code (small pad : ℕ) (pc : PreparedPair.Label small pad) (hh : PreparedPair.program small pad pc≠.halt)
    (_ : PreparedPair.program small pad pc≠.reject) :
    program small pad (.read pc)=MicrocodeEmbedding.instruction readBinding.ports Label.read (PreparedPair.program small pad pc) := by
  cases pc with
  | done b => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem append_code (small pad : ℕ) (second : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program id pc≠.halt) (_ : Microcode.MappedAppendFamily.program id pc≠.reject) :
    program small pad (.append second pc)=MicrocodeEmbedding.instruction (appendBinding second).ports (Label.append second)
      (Microcode.MappedAppendFamily.program id pc) := by
  have hp : pc≠7 := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

theorem erase_code (small pad : ℕ) (second : Bool) (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt)
    (_ : NativeErase.program pc≠.reject) :
    program small pad (.erase second pc)=MicrocodeEmbedding.instruction (eraseBinding second).ports (Label.erase second) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

abbrev Bank := Fin 6 → Tape Bool
def bank (source template input first second output : Tape Bool) : Bank := ![source,template,input,first,second,output]
def cfg {small pad : ℕ} (pc : Label small pad) (s : Bank) (pos : Fin 6 → ℤ) : NativeMicrocode.Config (Fin 6) (Label small pad) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Fin 6 → ℤ) : MicrocodeEmbedding.Frame (Fin 6) := ⟨fun p => (s p).denote,pos⟩
def advance (pos : Fin 6 → ℤ) (read written : ℕ) : Fin 6 → ℤ :=
  fun p => pos p+(if p=2 then (read : ℤ) else 0)+(if p=5 then (written : ℤ) else 0)
abbrev Trace (small pad : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program small pad)) (NativeMicrocode.Active (program small pad))

theorem advance_add (pos : Fin 6 → ℤ) (a b c d : ℕ) : advance (advance pos a b) c d=advance pos (a+c) (b+d) := by
  funext p;fin_cases p <;> simp [advance,add_assoc]
theorem advance_zero (pos : Fin 6 → ℤ) : advance pos 0 0=pos := by funext p;simp [advance]

def liftRead (s : PreparedPair.Bank) (output : Tape Bool) : Bank := ![s 0,s 1,s 2,s 3,s 4,output]
theorem liftRead_bank (source template input first second output : Tape Bool) :
    liftRead (PreparedPair.bank source template input first second) output=bank source template input first second output := by
  funext p;fin_cases p <;> rfl

theorem embed_read (small pad : ℕ) (pc : PreparedPair.Label small pad) (s base : PreparedPair.Bank) (output : Tape Bool)
    (rpos : Fin 5 → ℤ) (pos : Fin 6 → ℤ) :
    MicrocodeEmbedding.embed readBinding.ports (Label.read (small:=small) (pad:=pad)) (PreparedPair.cfg pc s rpos)
      (frame (liftRead base output) pos)=cfg (.read pc) (liftRead s output) (readBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed PreparedPair.cfg cfg frame
  simp only [← readBinding.values_eq_extend]
  congr 2
  funext p;fin_cases p <;> rfl

theorem read_positions (pos : Fin 6 → ℤ) : readBinding.values (fun p => pos (readBinding.ports p)) pos=pos := by
  funext p;fin_cases p <;> rfl
theorem read_final_positions (pos : Fin 6 → ℤ) (m : ℕ) :
    readBinding.values (PreparedPair.advance (fun p => pos (readBinding.ports p)) m) pos=advance pos m 0 := by
  funext p;fin_cases p <;> simp [readBinding,FinitePortBinding.values,PreparedPair.advance,advance]

theorem read_pair_call (small pad : ℕ) (xs first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (output : Tape Bool) (pos : Fin 6 → ℤ) :
    ∃ t ≤ PreparedPair.pairBudget small pad xs,Trace small pad t
      (cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ output) pos)
      (cfg (.read (.done true)) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(symbols (first++second)).reverse++pre,suffix⟩
        (Counter.marked (NativePaddedField.padded pad first)) (Counter.marked (NativePaddedField.padded pad second)) output)
        (advance pos (2*(2*xs.length+small)) 0)) := by
  obtain ⟨t,ht,htr⟩ := PreparedPair.pair_trace small pad xs first second hp hf hs pre suffix (fun p => pos (readBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (small:=small) (pad:=pad)) (PreparedPair.program small pad) (program small pad)
    (frame (liftRead (PreparedPair.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) output) pos)
    (read_code small pad) htr
  simp only [embed_read,read_positions,read_final_positions] at he
  exact ⟨t,ht,by simpa only [liftRead_bank,start] using he⟩

theorem read_stop_call (small pad : ℕ) (xs : List Bool) (pre suffix : List (Sym Bool)) (output : Tape Bool) (pos : Fin 6 → ℤ) :
    ∃ t ≤ PreparedPair.stopBudget small xs,Trace small pad t
      (cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ output) pos)
      (cfg (.read (.done false)) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨.stop::pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ output) (advance pos 1 0)) := by
  obtain ⟨t,ht,htr⟩ := PreparedPair.stop_trace small pad xs pre suffix (fun p => pos (readBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (small:=small) (pad:=pad)) (PreparedPair.program small pad) (program small pad)
    (frame (liftRead (PreparedPair.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) output) pos) (read_code small pad) htr
  simp only [embed_read,read_positions,read_final_positions] at he
  exact ⟨t,ht,by simpa only [liftRead_bank,start] using he⟩

theorem jump_trace (small pad : ℕ) (pc next : Label small pad) (s : Bank) (pos : Fin 6 → ℤ)
    (h : program small pad pc=.jump next) : Trace small pad 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.NormalizedBatch
