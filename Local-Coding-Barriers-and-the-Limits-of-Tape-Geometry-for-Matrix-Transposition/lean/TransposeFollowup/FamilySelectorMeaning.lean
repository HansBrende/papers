import TransposeFollowup.PrefixMembershipRun
import TransposeFollowup.NormalizedBatchCalls
import TransposeFollowup.PortBindingValues
import TransposeFollowup.NormalizedRecordsSize
import TransposeFollowup.RationalPageOpcode

/-! Read raw candidates on one stream and test them against an independent
normalized prefix. Emit only absent candidates,then physically erase both
fields. The query prefix is rewound on every call; neither record count nor
coordinate values occur in the finite program. -/
namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def readBinding : FinitePortBinding (Fin 5) (Fin 9) where
  ports:=⟨![0,1,7,5,6],by decide +kernel⟩
  decode:=fun p => if p=0 then some 0 else if p=1 then some 1 else if p=7 then some 2 else if p=5 then some 3 else if p=6 then some 4 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
def queryBinding : FinitePortBinding (Fin 7) (Fin 9) where
  ports:=⟨![0,1,2,3,4,5,6],by decide +kernel⟩
  decode:=fun p => if p=0 then some 0 else if p=1 then some 1 else if p=2 then some 2 else if p=3 then some 3 else if p=4 then some 4 else if p=5 then some 5 else if p=6 then some 6 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
def fieldPort (second : Bool) : Fin 9 := if second then 6 else 5
def appendBinding (second : Bool) : FinitePortBinding (Fin 2) (Fin 9) where
  ports:=⟨![fieldPort second,8],by cases second <;> decide +kernel⟩
  decode:=fun p => if p=fieldPort second then some 0 else if p=8 then some 1 else none
  decode_spec:=by intro p j;cases second <;> fin_cases p <;> fin_cases j <;> decide +kernel
def eraseBinding (second : Bool) : FinitePortBinding (Fin 1) (Fin 9) where
  ports:=⟨fun _ => fieldPort second,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=fieldPort second then some 0 else none
  decode_spec:=by intro p j;cases second <;> fin_cases p <;> fin_cases j <;> decide +kernel

inductive Label (small pad K : ℕ)
  | read (pc : PreparedPair.Label small pad)
  | query (pc : PrefixMembership.Label (small+pad) K)
  | append (second : Bool) (pc : Microcode.MappedAppendFamily.Label)
  | erase (second : Bool) (pc : NativeErase.Label)
  | done
  deriving DecidableEq,Fintype
def start (small pad K : ℕ) : Label small pad K := .read (.prepare (.init (.erase 0)))
def program (small pad K : ℕ) : Microcode.Program (Fin 9) (Label small pad K)
  | .read (.done true) => .jump (.query (PrefixMembership.start (small+pad) K))
  | .read (.done false) => .act (Microcode.single 8 ⟨some .stop,.right⟩) .done
  | .read pc => readBinding.instruction Label.read (PreparedPair.program small pad pc)
  | .query (.rewind found .done) => .jump (if found then .erase false 2 else .append false 0)
  | .query pc => queryBinding.instruction Label.query (PrefixMembership.program (small+pad) K pc)
  | .append second pc => if pc=7 then .jump (if second then .erase false 2 else .append true 0)
    else (appendBinding second).instruction (Label.append second) (Microcode.MappedAppendFamily.program id pc)
  | .erase second pc => if pc=0 then .jump (if second then start small pad K else .erase true 2)
    else (eraseBinding second).instruction (Label.erase second) (NativeErase.program pc)
  | .done => .halt

theorem read_code (small pad K : ℕ) (pc : PreparedPair.Label small pad) (hh : PreparedPair.program small pad pc≠.halt)
    (_ : PreparedPair.program small pad pc≠.reject) :
    program small pad K (.read pc)=MicrocodeEmbedding.instruction readBinding.ports Label.read (PreparedPair.program small pad pc) := by
  cases pc with
  | done b => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem query_code (small pad K : ℕ) (pc : PrefixMembership.Label (small+pad) K)
    (hh : PrefixMembership.program (small+pad) K pc≠.halt) (_ : PrefixMembership.program (small+pad) K pc≠.reject) :
    program small pad K (.query pc)=MicrocodeEmbedding.instruction queryBinding.ports Label.query (PrefixMembership.program (small+pad) K pc) := by
  cases pc with
  | rewind f pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,FinitePortBinding.instruction_eq]
  | phase i pc => simp only [program,FinitePortBinding.instruction_eq]
theorem append_code (small pad K : ℕ) (second : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program id pc≠.halt) (_ : Microcode.MappedAppendFamily.program id pc≠.reject) :
    program small pad K (.append second pc)=MicrocodeEmbedding.instruction (appendBinding second).ports (Label.append second)
      (Microcode.MappedAppendFamily.program id pc) := by
  have hp : pc≠7 := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]
theorem erase_code (small pad K : ℕ) (second : Bool) (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt)
    (_ : NativeErase.program pc≠.reject) :
    program small pad K (.erase second pc)=MicrocodeEmbedding.instruction (eraseBinding second).ports (Label.erase second) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

abbrev Bank := Fin 9 → Tape Bool
def bank (source template query testA testB first second input output : Tape Bool) : Bank :=
  ![source,template,query,testA,testB,first,second,input,output]
def cfg {small pad K : ℕ} (pc : Label small pad K) (s : Bank) (pos : Fin 9 → ℤ) : NativeMicrocode.Config (Fin 9) (Label small pad K) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Fin 9 → ℤ) : MicrocodeEmbedding.Frame (Fin 9) := ⟨fun p => (s p).denote,pos⟩
def advance (pos : Fin 9 → ℤ) (read written : ℕ) : Fin 9 → ℤ :=
  fun p => pos p+(if p=7 then (read : ℤ) else 0)+(if p=8 then (written : ℤ) else 0)
abbrev Trace (small pad K : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program small pad K)) (NativeMicrocode.Active (program small pad K))
theorem advance_add (pos : Fin 9 → ℤ) (a b c d : ℕ) : advance (advance pos a b) c d=advance pos (a+c) (b+d) := by
  funext p;fin_cases p <;> simp [advance,add_assoc]
theorem advance_zero (pos : Fin 9 → ℤ) : advance pos 0 0=pos := by funext p;simp [advance]
theorem jump_trace (small pad K : ℕ) (pc next : Label small pad K) (s : Bank) (pos : Fin 9 → ℤ)
    (h : program small pad K pc=.jump next) : Trace small pad K 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.FilteredBatch


namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def liftRead (s : PreparedPair.Bank) (query testA testB output : Tape Bool) : Bank :=
  bank (s 0) (s 1) query testA testB (s 3) (s 4) (s 2) output
theorem liftRead_bank (source template input first second query testA testB output : Tape Bool) :
    liftRead (PreparedPair.bank source template input first second) query testA testB output=
      bank source template query testA testB first second input output := by
  funext p;fin_cases p <;> rfl
theorem read_values (s base : PreparedPair.Bank) (query testA testB output : Tape Bool) :
    readBinding.values s (liftRead base query testA testB output)=liftRead s query testA testB output := by
  funext p;fin_cases p <;> rfl
theorem embed_read (small pad K : ℕ) (pc : PreparedPair.Label small pad) (s base : PreparedPair.Bank)
    (query testA testB output : Tape Bool) (rpos : Fin 5 → ℤ) (pos : Fin 9 → ℤ) :
    MicrocodeEmbedding.embed readBinding.ports (Label.read (small:=small) (pad:=pad) (K:=K)) (PreparedPair.cfg pc s rpos)
      (frame (liftRead base query testA testB output) pos)=
      cfg (.read pc) (liftRead s query testA testB output) (readBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed PreparedPair.cfg cfg frame
  simp only [← readBinding.values_eq_extend,FinitePortBinding.map_values,read_values]
theorem read_positions (pos : Fin 9 → ℤ) : readBinding.values (fun p => pos (readBinding.ports p)) pos=pos := by
  funext p;fin_cases p <;> rfl
theorem read_final_positions (pos : Fin 9 → ℤ) (m : ℕ) :
    readBinding.values (PreparedPair.advance (fun p => pos (readBinding.ports p)) m) pos=advance pos m 0 := by
  funext p;fin_cases p <;> simp [readBinding,FinitePortBinding.values,PreparedPair.advance,advance]

theorem read_pair_call (small pad K : ℕ) (xs first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (query output : Tape Bool) (pos : Fin 9 → ℤ) :
    ∃ t ≤ PreparedPair.pairBudget small pad xs,Trace small pad K t
      (cfg (start small pad K) (bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩
        ⟨pre,symbols (first++second)++suffix⟩ output) pos)
      (cfg (.read (.done true)) (bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩
        (Counter.marked (NativePaddedField.padded pad first)) (Counter.marked (NativePaddedField.padded pad second))
        ⟨(symbols (first++second)).reverse++pre,suffix⟩ output) (advance pos (2*(2*xs.length+small)) 0)) := by
  obtain ⟨t,ht,htr⟩:=PreparedPair.pair_trace small pad xs first second hp hf hs pre suffix (fun p => pos (readBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (small:=small) (pad:=pad) (K:=K))
    (PreparedPair.program small pad) (program small pad K)
    (frame (liftRead (PreparedPair.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩)
      query ⟨[],[]⟩ ⟨[],[]⟩ output) pos) (read_code small pad K) htr
  simp only [embed_read,read_positions,read_final_positions] at he
  exact ⟨t,ht,by simpa only [liftRead_bank,start] using he⟩

theorem read_stop_call (small pad K : ℕ) (xs : List Bool) (pre suffix : List (Sym Bool)) (query output : Tape Bool) (pos : Fin 9 → ℤ) :
    ∃ t ≤ PreparedPair.stopBudget small xs,Trace small pad K t
      (cfg (start small pad K) (bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ output) pos)
      (cfg (.read (.done false)) (bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨.stop::pre,suffix⟩ output)
        (advance pos 1 0)) := by
  obtain ⟨t,ht,htr⟩:=PreparedPair.stop_trace small pad xs pre suffix (fun p => pos (readBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (small:=small) (pad:=pad) (K:=K))
    (PreparedPair.program small pad) (program small pad K)
    (frame (liftRead (PreparedPair.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩)
      query ⟨[],[]⟩ ⟨[],[]⟩ output) pos) (read_code small pad K) htr
  simp only [embed_read,read_positions,read_final_positions] at he
  exact ⟨t,ht,by simpa only [liftRead_bank,start] using he⟩

end TransposeFollowup.FilteredBatch


namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

def liftQuery (s : BatchMembership.Bank) (input output : Tape Bool) : Bank :=
  bank (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) input output
theorem liftQuery_bank (xs : List Bool) (a : List Bool × List Bool) (query input output : Tape Bool) :
    liftQuery (BatchMembership.queryBank xs a query) input output=
      bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked a.1) (Counter.marked a.2) input output := by
  funext p;fin_cases p <;> rfl
theorem query_values (s base : BatchMembership.Bank) (input output : Tape Bool) :
    queryBinding.values s (liftQuery base input output)=liftQuery s input output := by
  funext p;fin_cases p <;> rfl
theorem embed_query (small pad : ℕ) (pc : PrefixMembership.Label (small+pad) K) (s base : BatchMembership.Bank)
    (input output : Tape Bool) (rpos : Fin 7 → ℤ) (pos : Fin 9 → ℤ) :
    MicrocodeEmbedding.embed queryBinding.ports (Label.query (small:=small) (pad:=pad)) (PrefixMembership.cfg pc s rpos)
      (frame (liftQuery base input output) pos)=cfg (.query pc) (liftQuery s input output) (queryBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed PrefixMembership.cfg cfg frame
  simp only [← queryBinding.values_eq_extend,FinitePortBinding.map_values,query_values]
theorem query_positions (pos : Fin 9 → ℤ) : queryBinding.values (fun p => pos (queryBinding.ports p)) pos=pos := by
  funext p;fin_cases p <;> rfl

def found (batches : Fin K → List (List Bool × List Bool)) (a : List Bool × List Bool) :=
  (PrefixMembership.segments batches 0 K).any (NativePairEqual.samePair a)
def queryTape (batches : Fin K → List (List Bool × List Bool)) (suffix : List (Sym Bool)) : Tape Bool :=
  ⟨[],PrefixMembership.stream batches 0 K++suffix⟩

theorem query_call (small pad : ℕ) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+(small+pad)) (ha2 : a.2.length=2*xs.length+(small+pad)) (hp : 0<2*xs.length+(small+pad))
    (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i,p.1.length=2*xs.length+(small+pad) ∧ p.2.length=2*xs.length+(small+pad))
    (suffix : List (Sym Bool)) (input output : Tape Bool) (pos : Fin 9 → ℤ) :
    ∃ t ≤ 3*PrefixMembership.scanBudget (small+pad) xs batches 0 K+3,Trace small pad K t
      (cfg (.query (PrefixMembership.start (small+pad) K))
        (bank (Counter.marked xs) ⟨[],[]⟩ (queryTape batches suffix) ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked a.1) (Counter.marked a.2) input output) pos)
      (cfg (.query (.rewind (found batches a) .done))
        (bank (Counter.marked xs) ⟨[],[]⟩ (queryTape batches suffix) ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked a.1) (Counter.marked a.2) input output) pos) := by
  obtain ⟨t,ht,htr⟩:=PrefixMembership.complete_trace (small+pad) xs a ha1 ha2 hp batches hw suffix (fun p => pos (queryBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed queryBinding.ports (Label.query (small:=small) (pad:=pad))
    (PrefixMembership.program (small+pad) K) (program small pad K)
    (frame (liftQuery (BatchMembership.queryBank xs a (queryTape batches suffix)) input output) pos) (query_code small pad K) htr
  simp only [embed_query,query_positions] at he
  exact ⟨t,ht,by simpa only [liftQuery_bank,found,queryTape] using he⟩

end TransposeFollowup.FilteredBatch


namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem append_values (second : Bool) (source output : Tape Bool) (s : Bank) :
    (appendBinding second).values (Function.update (Function.update (fun _ : Fin 2 => (⟨[],[]⟩ : Tape Bool)) 0 source) 1 output) s=
      Function.update (Function.update s (fieldPort second) source) 8 output := by
  funext p;cases second <;> fin_cases p <;> rfl

theorem erase_values (second : Bool) (word : Tape Bool) (s : Bank) :
    (eraseBinding second).values (Function.update (fun _ : Fin 1 => (⟨[],[]⟩ : Tape Bool)) 0 word) s=Function.update s (fieldPort second) word := by
  funext p;cases second <;> fin_cases p <;> rfl

theorem embed_append (small pad K : ℕ) (second : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (source output : Tape Bool) (s : Bank) (rpos : Fin 2 → ℤ) (pos : Fin 9 → ℤ) :
    MicrocodeEmbedding.embed (appendBinding second).ports (Label.append (small:=small) (pad:=pad) (K:=K) second)
      (NativeMappedAppend.cfg pc source output rpos).denote (frame s pos)=
      cfg (.append second pc) (Function.update (Function.update s (fieldPort second) source) 8 output)
        ((appendBinding second).values rpos pos) := by
  unfold MicrocodeEmbedding.embed NativeMappedAppend.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus2 Microcode.focus cfg frame
  simp only [← (appendBinding second).values_eq_extend,FinitePortBinding.map_values,append_values]

theorem append_positions (second : Bool) (pos : Fin 9 → ℤ) :
    (appendBinding second).values (fun p => pos ((appendBinding second).ports p)) pos=pos := by
  funext p;cases second <;> fin_cases p <;> rfl

theorem append_final_positions (second : Bool) (pos : Fin 9 → ℤ) (m : ℕ) :
    (appendBinding second).values (NativeMappedAppend.finalPositions (fun p => pos ((appendBinding second).ports p)) m) pos=advance pos 0 m := by
  funext p;cases second <;> fin_cases p <;> simp [appendBinding,fieldPort,FinitePortBinding.values,NativeMappedAppend.finalPositions,advance]

theorem append_call (small pad K : ℕ) (second : Bool) (xs : List Bool) (pre : List (Sym Bool))
    (s : Bank) (hs : s (fieldPort second)=Counter.marked xs) (ho : s 8=⟨pre,[]⟩) (pos : Fin 9 → ℤ) :
    ∃ t ≤ 4*xs.length+5,Trace small pad K t (cfg (.append second 0) s pos)
      (cfg (.append second 7) (Function.update s 8 ⟨(symbols xs).reverse++pre,[]⟩) (advance pos 0 xs.length)) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedAppend.append_trace id xs pre (fun p => pos ((appendBinding second).ports p))
  have he := MicrocodeEmbedding.trace_embed (appendBinding second).ports (Label.append (small:=small) (pad:=pad) (K:=K) second)
    (Microcode.MappedAppendFamily.program id) (program small pad K) (frame s pos) (append_code small pad K second) htr
  exact ⟨t,ht,by simpa only [embed_append,append_positions,append_final_positions,List.map_id,← hs,← ho,Function.update_eq_self] using he⟩

theorem embed_erase (small pad K : ℕ) (second : Bool) (pc : NativeErase.Label) (word : Tape Bool) (s : Bank) (pos : Fin 9 → ℤ) :
    MicrocodeEmbedding.embed (eraseBinding second).ports (Label.erase (small:=small) (pad:=pad) (K:=K) second)
      (NativeErase.cfg pc word (fun _ => pos (fieldPort second))).denote (frame s pos)=
      cfg (.erase second pc) (Function.update s (fieldPort second) word) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← (eraseBinding second).values_eq_extend,FinitePortBinding.map_values,erase_values]
  congr 1
  funext p;cases second <;> fin_cases p <;> rfl

theorem erase_call (small pad K : ℕ) (second : Bool) (xs : List Bool) (s : Bank)
    (hs : s (fieldPort second)=Counter.marked xs) (pos : Fin 9 → ℤ) :
    ∃ t ≤ 4*xs.length+4,Trace small pad K t (cfg (.erase second 2) s pos)
      (cfg (.erase second 0) (Function.update s (fieldPort second) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun _ => pos (fieldPort second))
  have he := MicrocodeEmbedding.trace_embed (eraseBinding second).ports (Label.erase (small:=small) (pad:=pad) (K:=K) second)
    NativeErase.program (program small pad K) (frame s pos) (erase_code small pad K second) htr
  exact ⟨t,ht,by simpa only [embed_erase,← hs,Function.update_eq_self] using he⟩

theorem update_first (source template query testA testB first second input output word : Tape Bool) :
    Function.update (bank source template query testA testB first second input output) (fieldPort false) word=bank source template query testA testB word second input output := by
  funext p;fin_cases p <;> rfl
theorem update_second (source template query testA testB first second input output word : Tape Bool) :
    Function.update (bank source template query testA testB first second input output) (fieldPort true) word=bank source template query testA testB first word input output := by
  funext p;fin_cases p <;> rfl
theorem update_output (source template query testA testB first second input output word : Tape Bool) :
    Function.update (bank source template query testA testB first second input output) 8 word=bank source template query testA testB first second input word := by
  funext p;fin_cases p <;> rfl

theorem copy_stop_trace (small pad K : ℕ) (xs : List Bool) (query input : Tape Bool) (pre : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ 1,Trace small pad K t
      (cfg (.read (.done false)) (bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ input ⟨pre,[]⟩) pos)
      (cfg .done (bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ input ⟨.stop::pre,[]⟩) (advance pos 0 1)) := by
  let z : NativeZipper.Config (Fin 9) (Label small pad K) :=
    ⟨⟨.read (.done false),bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ input ⟨pre,[]⟩⟩,pos⟩
  let z' : NativeZipper.Config (Fin 9) (Label small pad K) :=
    ⟨⟨.done,bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ input ⟨.stop::pre,[]⟩⟩,advance pos 0 1⟩
  have hr : NativeZipper.run (program small pad K) 1 z=z' := by
    simp only [z,z',NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program]
    congr 2
    · funext p;fin_cases p <;> rfl
    · funext p;fin_cases p <;> simp [Microcode.single,advance,NativeMicrocode.direction,Transpose.Dir.shift]
  exact NativeZipper.trace_of_run (program small pad K) hr

end TransposeFollowup.FilteredBatch


namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def holding (xs : List Bool) (query : Tape Bool) (a : List Bool × List Bool) (input output : Tape Bool) :=
  bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked a.1) (Counter.marked a.2) input output
def ready (xs : List Bool) (query input output : Tape Bool) :=
  bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ input output

theorem clear_trace (small pad K : ℕ) (xs : List Bool) (query : Tape Bool) (a : List Bool × List Bool)
    (input output : Tape Bool) (pos : Fin 9 → ℤ) :
    ∃ t ≤ 4*a.1.length+4*a.2.length+10,Trace small pad K t
      (cfg (.erase false 2) (holding xs query a input output) pos)
      (cfg (start small pad K) (ready xs query input output) pos) := by
  obtain ⟨x,hx,tx⟩:=erase_call small pad K false a.1 (holding xs query a input output) rfl pos
  simp only [holding,update_first] at tx
  have j1:=jump_trace small pad K (.erase false 0) (.erase true 2)
    (bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked a.2) input output) pos rfl
  obtain ⟨y,hy,ty⟩:=erase_call small pad K true a.2
    (bank (Counter.marked xs) ⟨[],[]⟩ query ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked a.2) input output) rfl pos
  rw [update_second] at ty
  have j2:=jump_trace small pad K (.erase true 0) (start small pad K) (ready xs query input output) pos rfl
  exact ⟨x+1+y+1,by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tx j1) ty) j2⟩

theorem emit_trace (small pad K : ℕ) (xs : List Bool) (query : Tape Bool) (a : List Bool × List Bool)
    (input : Tape Bool) (out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ 4*a.1.length+4*a.2.length+12,Trace small pad K t
      (cfg (.append false 0) (holding xs query a input ⟨out,[]⟩) pos)
      (cfg (.erase false 2) (holding xs query a input ⟨(symbols (a.1++a.2)).reverse++out,[]⟩)
        (advance pos 0 (a.1.length+a.2.length))) := by
  let outA:=(symbols a.1).reverse++out
  let p1:=advance pos 0 a.1.length
  let p2:=advance p1 0 a.2.length
  obtain ⟨x,hx,tx⟩:=append_call small pad K false a.1 out (holding xs query a input ⟨out,[]⟩) rfl rfl pos
  simp only [holding,update_output] at tx
  have j1:=jump_trace small pad K (.append false 7) (.append true 0) (holding xs query a input ⟨outA,[]⟩) p1 rfl
  obtain ⟨y,hy,ty⟩:=append_call small pad K true a.2 outA (holding xs query a input ⟨outA,[]⟩) rfl rfl p1
  simp only [holding,update_output] at ty
  have j2:=jump_trace small pad K (.append true 7) (.erase false 2)
    (holding xs query a input ⟨(symbols a.2).reverse++outA,[]⟩) p2 rfl
  refine ⟨x+1+y+1,by omega,?_⟩
  simpa only [p2,p1,advance_add,Nat.zero_add,holding,outA,symbols,List.map_append,List.reverse_append,List.append_assoc]
    using NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tx j1) ty) j2

def emitted (already : Bool) (a : List Bool × List Bool) : List Bool := if already then [] else a.1++a.2

theorem finish_trace (small pad K : ℕ) (already : Bool) (xs : List Bool) (query : Tape Bool) (a : List Bool × List Bool)
    (input : Tape Bool) (out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ 8*a.1.length+8*a.2.length+23,Trace small pad K t
      (cfg (.query (.rewind already .done)) (holding xs query a input ⟨out,[]⟩) pos)
      (cfg (start small pad K) (ready xs query input ⟨(symbols (emitted already a)).reverse++out,[]⟩)
        (advance pos 0 (emitted already a).length)) := by
  cases already with
  | false =>
    have j:=jump_trace small pad K (.query (.rewind false .done)) (.append false 0) (holding xs query a input ⟨out,[]⟩) pos rfl
    obtain ⟨x,hx,tx⟩:=emit_trace small pad K xs query a input out pos
    obtain ⟨y,hy,ty⟩:=clear_trace small pad K xs query a input ⟨(symbols (a.1++a.2)).reverse++out,[]⟩
      (advance pos 0 (a.1.length+a.2.length))
    refine ⟨1+x+y,by omega,?_⟩
    simpa only [emitted,Bool.false_eq_true,ite_false,List.length_append] using NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans j tx) ty
  | true =>
    have j:=jump_trace small pad K (.query (.rewind true .done)) (.erase false 2) (holding xs query a input ⟨out,[]⟩) pos rfl
    obtain ⟨x,hx,tx⟩:=clear_trace small pad K xs query a input ⟨out,[]⟩ pos
    refine ⟨1+x,by omega,?_⟩
    simpa only [emitted,ite_true,symbols,List.map_nil,List.reverse_nil,List.nil_append,List.length_nil,advance_zero]
      using NativeCountedLoop.trace_trans j tx

end TransposeFollowup.FilteredBatch


namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

def paddedPair (pad : ℕ) (p : List Bool × List Bool) :=
  (NativePaddedField.padded pad p.1,NativePaddedField.padded pad p.2)
def recordBits (pad : ℕ) (batches : Fin K → List (List Bool × List Bool)) (p : List Bool × List Bool) :=
  emitted (found batches (paddedPair pad p)) (paddedPair pad p)
def recordBudget (small pad : ℕ) (xs : List Bool) (batches : Fin K → List (List Bool × List Bool)) :=
  80*xs.length+37*small+22*pad+88+3*PrefixMembership.scanBudget (small+pad) xs batches 0 K

theorem record_trace (small pad : ℕ) (xs first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i,p.1.length=2*xs.length+(small+pad) ∧ p.2.length=2*xs.length+(small+pad))
    (querySuffix pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ recordBudget small pad xs batches,Trace small pad K t
      (cfg (start small pad K) (ready xs (queryTape batches querySuffix) ⟨pre,symbols (first++second)++suffix⟩ ⟨out,[]⟩) pos)
      (cfg (start small pad K) (ready xs (queryTape batches querySuffix) ⟨(symbols (first++second)).reverse++pre,suffix⟩
        ⟨(symbols (recordBits pad batches (first,second))).reverse++out,[]⟩)
        (advance pos (2*(2*xs.length+small)) (recordBits pad batches (first,second)).length)) := by
  let a:=paddedPair pad (first,second)
  let input : Tape Bool:=⟨(symbols (first++second)).reverse++pre,suffix⟩
  let p1:=advance pos (2*(2*xs.length+small)) 0
  have h1 : a.1.length=2*xs.length+(small+pad) := by simp [a,paddedPair,NativePaddedField.padded_length,hf,Nat.add_assoc]
  have h2 : a.2.length=2*xs.length+(small+pad) := by simp [a,paddedPair,NativePaddedField.padded_length,hs,Nat.add_assoc]
  have hpos : 0<2*xs.length+(small+pad) := by omega
  obtain ⟨x,hx,tx⟩:=read_pair_call small pad K xs first second hp hf hs pre suffix (queryTape batches querySuffix) ⟨out,[]⟩ pos
  have j:=jump_trace small pad K (.read (.done true)) (.query (PrefixMembership.start (small+pad) K))
    (holding xs (queryTape batches querySuffix) a input ⟨out,[]⟩) p1 rfl
  obtain ⟨y,hy,ty⟩:=query_call small pad xs a h1 h2 hpos batches hw querySuffix input ⟨out,[]⟩ p1
  obtain ⟨z,hz,tz⟩:=finish_trace small pad K (found batches a) xs (queryTape batches querySuffix) a input out p1
  refine ⟨x+1+y+z,?_,?_⟩
  · unfold PreparedPair.pairBudget at hx
    unfold recordBudget
    omega
  · simpa only [holding,ready,a,paddedPair,input,p1,advance_add,Nat.add_zero,Nat.zero_add,recordBits]
      using NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tx j) ty) tz

theorem stop_trace (small pad K : ℕ) (xs : List Bool) (query : Tape Bool)
    (pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ PreparedPair.stopBudget small xs+1,Trace small pad K t
      (cfg (start small pad K) (ready xs query ⟨pre,.stop::suffix⟩ ⟨out,[]⟩) pos)
      (cfg .done (ready xs query ⟨.stop::pre,suffix⟩ ⟨.stop::out,[]⟩) (advance pos 1 1)) := by
  obtain ⟨a,ha,ta⟩:=read_stop_call small pad K xs pre suffix query ⟨out,[]⟩ pos
  obtain ⟨b,hb,tb⟩:=copy_stop_trace small pad K xs query ⟨.stop::pre,suffix⟩ out (advance pos 1 0)
  refine ⟨a+b,by omega,?_⟩
  simpa only [ready,advance_add,Nat.zero_add,Nat.add_zero] using NativeCountedLoop.trace_trans ta tb

end TransposeFollowup.FilteredBatch


namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

def outputBits (pad : ℕ) (batches : Fin K → List (List Bool × List Bool)) (rs : List (List Bool × List Bool)) :=
  rs.flatMap (recordBits pad batches)
def outputBatch (pad : ℕ) (batches : Fin K → List (List Bool × List Bool)) (rs : List (List Bool × List Bool)) :=
  symbols (outputBits pad batches rs)++[Sym.stop]
def batchBudget (small pad : ℕ) (xs : List Bool) (batches : Fin K → List (List Bool × List Bool)) (rs : List (List Bool × List Bool)) :=
  rs.length*recordBudget small pad xs batches+PreparedPair.stopBudget small xs+1

theorem records_trace (small pad : ℕ) (xs : List Bool) (hp : 0<2*xs.length+small)
    (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i,p.1.length=2*xs.length+(small+pad) ∧ p.2.length=2*xs.length+(small+pad))
    (rs : List (List Bool × List Bool)) (hr : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (querySuffix pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ rs.length*recordBudget small pad xs batches,Trace small pad K t
      (cfg (start small pad K) (ready xs (queryTape batches querySuffix) ⟨pre,symbols (NormalizedBatch.inputBits rs)++suffix⟩ ⟨out,[]⟩) pos)
      (cfg (start small pad K) (ready xs (queryTape batches querySuffix)
        ⟨(symbols (NormalizedBatch.inputBits rs)).reverse++pre,suffix⟩ ⟨(symbols (outputBits pad batches rs)).reverse++out,[]⟩)
        (advance pos (NormalizedBatch.inputBits rs).length (outputBits pad batches rs).length)) := by
  induction rs generalizing pre out pos with
  | nil =>
    refine ⟨0,by simp,?_⟩
    simp only [NormalizedBatch.inputBits,outputBits,List.flatMap_nil,symbols,List.map_nil,List.nil_append,List.reverse_nil,List.length_nil,advance_zero]
    exact .refl _
  | cons p rs ih =>
    have hpw:=hr p (by simp)
    have hrw : ∀ q ∈ rs,q.1.length=2*xs.length+small ∧ q.2.length=2*xs.length+small := by
      intro q hq;exact hr q (by simp [hq])
    have hlen : (p.1++p.2).length=2*(2*xs.length+small) := by simp [hpw.1,hpw.2,two_mul]
    obtain ⟨x,hx,tx⟩:=record_trace small pad xs p.1 p.2 hp hpw.1 hpw.2 batches hw querySuffix pre
      (symbols (NormalizedBatch.inputBits rs)++suffix) out pos
    rw [← hlen] at tx
    obtain ⟨y,hy,ty⟩:=ih hrw ((symbols (p.1++p.2)).reverse++pre) ((symbols (recordBits pad batches p)).reverse++out)
      (advance pos (p.1++p.2).length (recordBits pad batches p).length)
    refine ⟨x+y,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega
    · simpa only [NormalizedBatch.inputBits,outputBits,List.flatMap_cons,symbols,List.map_append,List.reverse_append,List.append_assoc,
        List.length_append,advance_add,Nat.add_assoc] using NativeCountedLoop.trace_trans tx ty

theorem batch_trace (small pad : ℕ) (xs : List Bool) (hp : 0<2*xs.length+small)
    (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i,p.1.length=2*xs.length+(small+pad) ∧ p.2.length=2*xs.length+(small+pad))
    (rs : List (List Bool × List Bool)) (hr : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (querySuffix pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ batchBudget small pad xs batches rs,Trace small pad K t
      (cfg (start small pad K) (ready xs (queryTape batches querySuffix) ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩ ⟨out,[]⟩) pos)
      (cfg .done (ready xs (queryTape batches querySuffix)
        ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩ ⟨(outputBatch pad batches rs).reverse++out,[]⟩)
        (advance pos (NormalizedBatch.inputBatch rs).length (outputBatch pad batches rs).length)) := by
  obtain ⟨x,hx,tx⟩:=records_trace small pad xs hp batches hw rs hr querySuffix pre (.stop::suffix) out pos
  obtain ⟨y,hy,ty⟩:=stop_trace small pad K xs (queryTape batches querySuffix) ((symbols (NormalizedBatch.inputBits rs)).reverse++pre) suffix
    ((symbols (outputBits pad batches rs)).reverse++out) (advance pos (NormalizedBatch.inputBits rs).length (outputBits pad batches rs).length)
  refine ⟨x+y,by unfold batchBudget;omega,?_⟩
  simpa only [NormalizedBatch.inputBatch,outputBatch,List.append_assoc,List.cons_append,List.nil_append,List.reverse_append,
    List.reverse_cons,List.reverse_nil,List.length_append,List.length_cons,List.length_nil,symbols,List.length_map,advance_add]
    using NativeCountedLoop.trace_trans tx ty

end TransposeFollowup.FilteredBatch


namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

noncomputable def nativeEncoding (small pad K : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 9) (start small pad K)
noncomputable def nativeMachine (small pad K : ℕ) := NativeMicrocode.machine (nativeEncoding small pad K) (program small pad K)

def labelEquiv (small pad K : ℕ) : Label small pad K ≃ PreparedPair.Label small pad ⊕ PrefixMembership.Label (small+pad) K ⊕
    (Bool × Microcode.MappedAppendFamily.Label) ⊕ (Bool × NativeErase.Label) ⊕ Unit where
  toFun
    | .read pc => .inl pc
    | .query pc => .inr (.inl pc)
    | .append b pc => .inr (.inr (.inl (b,pc)))
    | .erase b pc => .inr (.inr (.inr (.inl (b,pc))))
    | .done => .inr (.inr (.inr (.inr ())))
  invFun
    | .inl pc => .read pc
    | .inr (.inl pc) => .query pc
    | .inr (.inr (.inl (b,pc))) => .append b pc
    | .inr (.inr (.inr (.inl (b,pc)))) => .erase b pc
    | .inr (.inr (.inr (.inr _))) => .done
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc|⟨b,pc⟩|⟨b,pc⟩|⟨⟩) <;> rfl

theorem fixed_resources (small pad K : ℕ) : (nativeMachine small pad K).k=9 ∧ (nativeMachine small pad K).g+1=5 ∧
    (nativeMachine small pad K).q+1=small+2*pad+205+K*(2*(small+pad)+478) ∧
    (nativeEncoding small pad K).label (start small pad K)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label small pad K)-1+1=_
  rw [Fintype.card_congr (labelEquiv small pad K)]
  have hs:=(PreparedPair.fixed_resources small pad).2.2.1
  change Fintype.card (PreparedPair.Label small pad)-1+1=small+2*pad+164 at hs
  have hp : 0<Fintype.card (PreparedPair.Label small pad) := Fintype.card_pos_iff.mpr ⟨.done false⟩
  have hq:=(PrefixMembership.fixed_resources (small+pad) K).2.2.1
  change Fintype.card (PrefixMembership.Label (small+pad) K)-1+1=K*(2*(small+pad)+478)+8 at hq
  have hqp : 0<Fintype.card (PrefixMembership.Label (small+pad) K) := Fintype.card_pos_iff.mpr ⟨.rewind false .done⟩
  have ha : Fintype.card Microcode.MappedAppendFamily.Label=8 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_unit,ha]
  omega

theorem native_batch (small pad : ℕ) (xs : List Bool) (hp : 0<2*xs.length+small)
    (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i,p.1.length=2*xs.length+(small+pad) ∧ p.2.length=2*xs.length+(small+pad))
    (rs : List (List Bool × List Bool)) (hr : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (querySuffix pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ batchBudget small pad xs batches rs,
      Transpose.stepN (nativeMachine small pad K) input t
        ((cfg (start small pad K) (ready xs (queryTape batches querySuffix) ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩ ⟨out,[]⟩) pos).denote
          (nativeEncoding small pad K) (program small pad K) ip outRev)=
        some ((cfg .done (ready xs (queryTape batches querySuffix)
          ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩ ⟨(outputBatch pad batches rs).reverse++out,[]⟩)
          (advance pos (NormalizedBatch.inputBatch rs).length (outputBatch pad batches rs).length)).denote
          (nativeEncoding small pad K) (program small pad K) ip outRev) ∧
      Transpose.step (nativeMachine small pad K) input
        ((cfg .done (ready xs (queryTape batches querySuffix)
          ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩ ⟨(outputBatch pad batches rs).reverse++out,[]⟩)
          (advance pos (NormalizedBatch.inputBatch rs).length (outputBatch pad batches rs).length)).denote
          (nativeEncoding small pad K) (program small pad K) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=batch_trace small pad xs hp batches hw rs hr querySuffix pre suffix out pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding small pad K) (program small pad K) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding small pad K) (program small pad K) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (small pad : ℕ) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 9 ↪ U) (labels : Label small pad K → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program small pad K pc≠.halt → program small pad K pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program small pad K pc))
    (xs : List Bool) (hp : 0<2*xs.length+small) (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i,p.1.length=2*xs.length+(small+pad) ∧ p.2.length=2*xs.length+(small+pad))
    (rs : List (List Bool × List Bool)) (hr : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (querySuffix pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ batchBudget small pad xs batches rs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (start small pad K) (ready xs (queryTape batches querySuffix) ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩ ⟨out,[]⟩) pos)
          outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (ready xs (queryTape batches querySuffix)
            ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩ ⟨(outputBatch pad batches rs).reverse++out,[]⟩)
            (advance pos (NormalizedBatch.inputBatch rs).length (outputBatch pad batches rs).length)) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=batch_trace small pad xs hp batches hw rs hr querySuffix pre suffix out pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program small pad K) target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.FilteredBatch


namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

def selectedRecords (pad : ℕ) (batches : Fin K → List (List Bool × List Bool)) (rs : List (List Bool × List Bool)) :=
  (rs.map (paddedPair pad)).filter (fun p => !found batches p)

theorem output_bits_encoding (pad : ℕ) (batches : Fin K → List (List Bool × List Bool)) (rs : List (List Bool × List Bool)) :
    outputBits pad batches rs=NormalizedBatch.inputBits (selectedRecords pad batches rs) := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    cases h : found batches (paddedPair pad p) <;>
      simp only [outputBits,List.flatMap_cons,recordBits,emitted,h,Bool.false_eq_true,ite_false,ite_true,
        selectedRecords,List.map_cons,List.filter_cons,Bool.not_false,Bool.not_true,
        NormalizedBatch.inputBits,List.nil_append] at ih ⊢ <;> rw [ih]

theorem output_encoding (pad : ℕ) (batches : Fin K → List (List Bool × List Bool)) (rs : List (List Bool × List Bool)) :
    outputBatch pad batches rs=NormalizedBatch.inputBatch (selectedRecords pad batches rs) := by
  rw [outputBatch,output_bits_encoding,NormalizedBatch.inputBatch]

theorem padded_pair_value (pad : ℕ) (p : List Bool × List Bool) :
    RowEnumeration.decodePair (paddedPair pad p)=RowEnumeration.decodePair p := by
  unfold RowEnumeration.decodePair paddedPair
  simp only [← NativeCounter.word_value,NativePaddedField.padded_value]

theorem found_false_iff (batches : Fin K → List (List Bool × List Bool)) (a : List Bool × List Bool) :
    found batches a=false ↔ ∀ i,RowEnumeration.decodePair a ∉ (batches i).map RowEnumeration.decodePair := by
  have he:=PrefixMembership.result_iff a batches
  constructor
  · intro hf i hi
    have ht:=he.mpr ⟨i,hi⟩
    change found batches a=true at ht
    rw [hf] at ht;cases ht
  · intro h
    cases hf : found batches a with
    | false => rfl
    | true =>
      obtain ⟨i,hi⟩:=he.mp hf
      exact False.elim (h i hi)

theorem selected_records_spec (pad : ℕ) (batches : Fin K → List (List Bool × List Bool))
    (rs : List (List Bool × List Bool)) (p : ℕ × ℕ) :
    p ∈ (selectedRecords pad batches rs).map RowEnumeration.decodePair ↔
      p ∈ rs.map RowEnumeration.decodePair ∧ ∀ i,p ∉ (batches i).map RowEnumeration.decodePair := by
  constructor
  · intro h
    obtain ⟨a,ha,hap⟩:=List.mem_map.mp h
    obtain ⟨ham,haf⟩:=List.mem_filter.mp ha
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp ham
    have hf : found batches (paddedPair pad q)=false := by simpa using haf
    have hno:=(found_false_iff batches (paddedPair pad q)).mp hf
    rw [hap] at hno
    refine ⟨List.mem_map.mpr ⟨q,hq,?_⟩,hno⟩
    simpa only [padded_pair_value] using hap
  · rintro ⟨hm,hn⟩
    obtain ⟨q,hq,hqp⟩:=List.mem_map.mp hm
    have he : RowEnumeration.decodePair (paddedPair pad q)=p := (padded_pair_value pad q).trans hqp
    have hf : found batches (paddedPair pad q)=false := (found_false_iff batches _).mpr (by simpa only [he] using hn)
    exact List.mem_map.mpr ⟨paddedPair pad q,List.mem_filter.mpr ⟨List.mem_map.mpr ⟨q,hq,rfl⟩,by simp [hf]⟩,he⟩

theorem selected_values_nodup (pad : ℕ) (batches : Fin K → List (List Bool × List Bool)) (rs : List (List Bool × List Bool))
    (h : (rs.map RowEnumeration.decodePair).Nodup) :
    ((selectedRecords pad batches rs).map RowEnumeration.decodePair).Nodup := by
  have hs:=List.Sublist.map RowEnumeration.decodePair (List.filter_sublist (p:=fun p => !found batches p) (l:=rs.map (paddedPair pad)))
  have he : (rs.map (paddedPair pad)).map RowEnumeration.decodePair=rs.map RowEnumeration.decodePair := by
    simp only [List.map_map]
    congr 1
    funext p
    exact padded_pair_value pad p
  rw [he] at hs
  exact h.sublist hs

theorem selected_width (small pad : ℕ) (xs : List Bool) (batches : Fin K → List (List Bool × List Bool))
    (rs : List (List Bool × List Bool)) (h : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small) :
    ∀ p ∈ selectedRecords pad batches rs,p.1.length=2*xs.length+(small+pad) ∧ p.2.length=2*xs.length+(small+pad) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp (List.mem_filter.mp hp).1
  have hw:=h q hq
  simp only [paddedPair,NativePaddedField.padded_length,hw.1,hw.2,Nat.add_assoc,and_self]

end TransposeFollowup.FilteredBatch


/-! Least-map tagging is selection of the first batch containing an ordered
numeric pair. This does not identify reversed pairs or discard diagonals. -/
namespace TransposeFollowup.FirstWitness
open FixedTapeCompiler
set_option autoImplicit false
variable {r : ℕ}

def Occurs (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) (p : ℕ × ℕ) : Prop :=
  p ∈ (FamilyNormalization.normalizedRecords F xs k).map RowEnumeration.decodePair
def First (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) (p : ℕ × ℕ) : Prop :=
  Occurs F xs k p ∧ ∀ j : Fin (r+1),j<k → ¬Occurs F xs j p

theorem occurs_iff (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1))
    (i j : Fin (Counter.value xs)) : Occurs F xs k (i.val,j.val) ↔ j ∈ (F k).neighbors i := by
  unfold Occurs
  rw [RawNormalization.normalized_records_spec]
  constructor
  · rintro ⟨u,v,hv,he⟩
    have hu : u=i := Fin.ext (congrArg Prod.fst he).symm
    have hw : v=j := Fin.ext (congrArg Prod.snd he).symm
    subst u;subst v;exact hv
  · exact fun h => ⟨i,j,h,rfl⟩

theorem witness_iff {n : ℕ} (F : Fin (r+1) → RationalMobius) (i j : Fin n) (k : Fin (r+1)) :
    k ∈ rationalWitnessTags F i j ↔ j ∈ (F k).neighbors i := by
  simp only [rationalWitnessTags,Finset.mem_filter,Finset.mem_univ,true_and,RationalMobius.overlapTest_spec,RationalMobius.mem_neighbors]

theorem tag_minimal {n : ℕ} (F : Fin (r+1) → RationalMobius) (i j : Fin n) (k : Fin (r+1)) :
    rationalTag F i j=some k ↔ k ∈ rationalWitnessTags F i j ∧ ∀ q : Fin (r+1),q<k → q ∉ rationalWitnessTags F i j := by
  classical
  by_cases hn : (rationalWitnessTags F i j).Nonempty
  · rw [rationalTag,dite_eq_left hn,Option.some.injEq]
    constructor
    · intro he
      refine ⟨he ▸ Finset.min'_mem _ hn,?_⟩
      intro q hq hm
      have hle:=Finset.min'_le (rationalWitnessTags F i j) q hm
      rw [he] at hle
      exact (not_lt_of_ge hle) hq
    · rintro ⟨hk,hq⟩
      apply le_antisymm (Finset.min'_le _ _ hk)
      exact le_of_not_gt (fun h => hq _ h (Finset.min'_mem _ hn))
  · rw [rationalTag,dite_eq_right hn]
    constructor
    · intro h;cases h
    · rintro ⟨hk,_⟩;exact False.elim (hn ⟨k,hk⟩)

theorem first_iff_tag (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1))
    (i j : Fin (Counter.value xs)) : First F xs k (i.val,j.val) ↔ rationalTag F i j=some k := by
  rw [tag_minimal]
  simp only [First,occurs_iff,witness_iff]

theorem first_unique (F : Fin (r+1) → RationalMobius) (xs : List Bool) (p : ℕ × ℕ) (k q : Fin (r+1))
    (hk : First F xs k p) (hq : First F xs q p) : k=q := by
  rcases lt_trichotomy k q with h | h | h
  · exact False.elim (hq.2 k h hk.1)
  · exact h
  · exact False.elim (hk.2 q h hq.1)

theorem first_color (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1))
    (i j : Fin (Counter.value xs)) (h : First F xs k (i.val,j.val)) :
    rationalColor F i j=some (rationalResidueColor F i j k) := by
  rw [rationalColor,(first_iff_tag F xs k i j).mp h]
  rfl

end TransposeFollowup.FirstWitness


/-! The concrete prefix-query program tests precisely whether a candidate
has an earlier map witness. Its false return is the least-map selection
test, with the original stream and candidate physically restored. -/
namespace TransposeFollowup.FirstWitness
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def earlierBatches (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) (j : Fin k.val) :=
  FamilyNormalization.normalizedRecords F xs ⟨j.val,by omega⟩
def earlierFound (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) (a : List Bool × List Bool) :=
  (PrefixMembership.segments (earlierBatches F xs k) 0 k.val).any (NativePairEqual.samePair a)

theorem earlier_found_iff (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) (a : List Bool × List Bool) :
    earlierFound F xs k a=true ↔ ∃ j : Fin (r+1),j<k ∧ Occurs F xs j (RowEnumeration.decodePair a) := by
  rw [earlierFound,PrefixMembership.result_iff]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨⟨j.val,by omega⟩,j.isLt,hj⟩
  · rintro ⟨j,hjk,hj⟩
    exact ⟨⟨j.val,hjk⟩,hj⟩

theorem earlier_absent_iff (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) (a : List Bool × List Bool) :
    earlierFound F xs k a=false ↔ ∀ j : Fin (r+1),j<k → ¬Occurs F xs j (RowEnumeration.decodePair a) := by
  have he:=earlier_found_iff F xs k a
  cases hf : earlierFound F xs k a <;> simp only [hf,Bool.false_eq_true,false_iff,not_exists,not_and,true_iff] at he
  · simpa using he
  · constructor
    · intro h;cases h
    · intro h
      obtain ⟨j,hjk,hj⟩:=he
      exact False.elim (h j hjk hj)

theorem first_iff_query_false (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1))
    (a : List Bool × List Bool) (ha : Occurs F xs k (RowEnumeration.decodePair a)) :
    First F xs k (RowEnumeration.decodePair a) ↔ earlierFound F xs k a=false := by
  rw [First,earlier_absent_iff]
  exact and_iff_right ha

theorem earlier_width (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) :
    ∀ j,∀ p ∈ earlierBatches F xs k j,
      p.1.length=2*xs.length+FamilyNormalization.common F ∧ p.2.length=2*xs.length+FamilyNormalization.common F := by
  intro j p hp
  exact FamilyNormalization.normalized_width F xs ⟨j.val,by omega⟩ p hp

theorem query_trace (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+FamilyNormalization.common F) (ha2 : a.2.length=2*xs.length+FamilyNormalization.common F)
    (ha : Occurs F xs k (RowEnumeration.decodePair a)) (suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ found : Bool,∃ t ≤ 3*PrefixMembership.scanBudget (FamilyNormalization.common F) xs (earlierBatches F xs k) 0 k.val+3,
      PrefixMembership.Trace (FamilyNormalization.common F) k.val t
        (PrefixMembership.cfg (PrefixMembership.start (FamilyNormalization.common F) k.val)
          (BatchMembership.queryBank xs a ⟨[],PrefixMembership.stream (earlierBatches F xs k) 0 k.val++suffix⟩) pos)
        (PrefixMembership.cfg (.rewind found .done)
          (BatchMembership.queryBank xs a ⟨[],PrefixMembership.stream (earlierBatches F xs k) 0 k.val++suffix⟩) pos) ∧
      (found=false ↔ First F xs k (RowEnumeration.decodePair a)) := by
  have hp : 0<2*xs.length+FamilyNormalization.common F := by
    have h:=RowEnumeration.common_positive (F k) xs
    simp only [PaddedWord.word_length] at h
    have hc:=FamilyNormalization.le_common F k
    omega
  obtain ⟨t,ht,htr⟩:=PrefixMembership.complete_trace (FamilyNormalization.common F) xs a ha1 ha2 hp
    (earlierBatches F xs k) (earlier_width F xs k) suffix pos
  exact ⟨earlierFound F xs k a,t,ht,htr,(first_iff_query_false F xs k a ha).symm⟩

theorem earlier_records_count (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) :
    (PrefixMembership.segments (earlierBatches F xs k) 0 k.val).length≤
      Counter.value xs*(∑ j : Fin k.val,((F ⟨j.val,by omega⟩).distortion+1)) := by
  rw [PrefixMembership.segments_ofFn _ _ _ (by omega)]
  calc
    _ = ∑ j : Fin k.val,(earlierBatches F xs k j).length := by simp [Fin.sum_ofFn]
    _ ≤ ∑ j : Fin k.val,Counter.value xs*((F ⟨j.val,by omega⟩).distortion+1) :=
      Finset.sum_le_sum (fun j _ => FamilyNormalization.normalized_records_count F xs ⟨j.val,by omega⟩)
    _ = _ := by rw [Finset.mul_sum]

theorem query_budget_le (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) :
    3*PrefixMembership.scanBudget (FamilyNormalization.common F) xs (earlierBatches F xs k) 0 k.val+3≤
      3*((Counter.value xs*(∑ j : Fin k.val,((F ⟨j.val,by omega⟩).distortion+1))+k.val)*
        BatchMembership.recordBudget (FamilyNormalization.common F) xs+k.val)+3 := by
  unfold PrefixMembership.scanBudget
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (earlier_records_count F xs k) k.val)) k.val)) 3

end TransposeFollowup.FirstWitness


namespace TransposeFollowup.FirstWitness
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def selected (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) :=
  FilteredBatch.selectedRecords (FamilyNormalization.padding F k) (earlierBatches F xs k) (FamilyNormalization.records F xs k)

theorem selected_spec (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) (p : ℕ × ℕ) :
    p ∈ (selected F xs k).map RowEnumeration.decodePair ↔ First F xs k p := by
  rw [selected,FilteredBatch.selected_records_spec,← FamilyNormalization.normalized_values]
  constructor
  · rintro ⟨hc,he⟩
    refine ⟨hc,?_⟩
    intro j hj
    exact he ⟨j.val,hj⟩
  · rintro ⟨hc,he⟩
    refine ⟨hc,?_⟩
    intro j
    exact he ⟨j.val,by omega⟩ j.isLt

theorem selected_values_nodup (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) :
    ((selected F xs k).map RowEnumeration.decodePair).Nodup := by
  have hn:=RawNormalization.normalized_records_nodup F xs k
  rw [FamilyNormalization.normalized_values] at hn
  exact FilteredBatch.selected_values_nodup _ _ _ hn

theorem selected_tag_spec (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1))
    (i j : Fin (Counter.value xs)) :
    (i.val,j.val) ∈ (selected F xs k).map RowEnumeration.decodePair ↔ rationalTag F i j=some k := by
  rw [selected_spec,first_iff_tag]

theorem selected_batches_disjoint (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k q : Fin (r+1))
    (p : ℕ × ℕ) (hk : p ∈ (selected F xs k).map RowEnumeration.decodePair)
    (hq : p ∈ (selected F xs q).map RowEnumeration.decodePair) : k=q :=
  first_unique F xs p k q ((selected_spec F xs k p).mp hk) ((selected_spec F xs q p).mp hq)

theorem batch_trace (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1))
    (querySuffix pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ FilteredBatch.batchBudget (PaddedWord.commonConstant (F k)) (FamilyNormalization.padding F k) xs
        (earlierBatches F xs k) (FamilyNormalization.records F xs k),
      FilteredBatch.Trace (PaddedWord.commonConstant (F k)) (FamilyNormalization.padding F k) k.val t
        (FilteredBatch.cfg (FilteredBatch.start (PaddedWord.commonConstant (F k)) (FamilyNormalization.padding F k) k.val)
          (FilteredBatch.ready xs (FilteredBatch.queryTape (earlierBatches F xs k) querySuffix)
            ⟨pre,FamilyNormalization.inputBatch F xs k++suffix⟩ ⟨out,[]⟩) pos)
        (FilteredBatch.cfg .done (FilteredBatch.ready xs (FilteredBatch.queryTape (earlierBatches F xs k) querySuffix)
          ⟨(FamilyNormalization.inputBatch F xs k).reverse++pre,suffix⟩
          ⟨(NormalizedBatch.inputBatch (selected F xs k)).reverse++out,[]⟩)
          (FilteredBatch.advance pos (FamilyNormalization.inputBatch F xs k).length (NormalizedBatch.inputBatch (selected F xs k)).length)) := by
  have hC : PaddedWord.commonConstant (F k)+FamilyNormalization.padding F k=FamilyNormalization.common F := by
    exact Nat.add_sub_of_le (FamilyNormalization.le_common F k)
  have hp : 0<2*xs.length+PaddedWord.commonConstant (F k) := by
    simpa only [PaddedWord.word_length] using RowEnumeration.common_positive (F k) xs
  have hw := earlier_width F xs k
  rw [← hC] at hw
  have hr := RowEnumeration.rows_records_width (F k) xs (Counter.value xs) 0
  simp only [PaddedWord.word_length] at hr
  obtain ⟨t,ht,htr⟩:=FilteredBatch.batch_trace (PaddedWord.commonConstant (F k)) (FamilyNormalization.padding F k) xs hp
    (earlierBatches F xs k) hw (FamilyNormalization.records F xs k) hr querySuffix pre suffix out pos
  exact ⟨t,ht,by simpa only [FilteredBatch.output_encoding,selected,FamilyNormalization.inputBatch] using htr⟩

end TransposeFollowup.FirstWitness


namespace TransposeFollowup.FilteredBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

def linearCoefficient (small pad K D S : ℕ) := (D*(3*S+6*K+1)+1)*(39*(small+pad)+340)

theorem linear_budget (small pad n D S : ℕ) (hn : 1≤n) (xs : List Bool) (hx : xs.length≤(n+1).size)
    (batches : Fin K → List (List Bool × List Bool)) (rs : List (List Bool × List Bool))
    (hQ : (PrefixMembership.segments batches 0 K).length≤n*S) (hR : rs.length≤n*D) :
    batchBudget small pad xs batches rs≤linearCoefficient small pad K D S*Transpose.inputLength n := by
  let H:=84*xs.length+39*(small+pad)+88
  let A:=3*S+6*K+1
  have hH : 1≤H := by dsimp [H];omega
  have hcore : BatchMembership.recordBudget (small+pad) xs≤H := by
    unfold BatchMembership.recordBudget;dsimp [H];omega
  have hscan : PrefixMembership.scanBudget (small+pad) xs batches 0 K≤(n*S+K)*H+K := by
    exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.add_le_add_right hQ K) hcore) K
  have hbase : 80*xs.length+37*small+22*pad+88≤H := by dsimp [H];omega
  have hKH : K≤K*H := by simpa using Nat.mul_le_mul_left K hH
  have hcoef : 3*(n*S+K)+3*K+1≤n*A := by
    have hm:=Nat.mul_le_mul_right (6*K+1) hn
    dsimp [A]
    nlinarith
  have hrecord : recordBudget small pad xs batches≤n*A*H := by
    calc
      _ ≤ (3*(n*S+K)+3*K+1)*H := by unfold recordBudget;nlinarith
      _ ≤ _ := Nat.mul_le_mul_right H hcoef
  have hstop : PreparedPair.stopBudget small xs+1≤H := by unfold PreparedPair.stopBudget;dsimp [H];omega
  have hNN : 1≤n*n := by nlinarith
  have hpad : H≤(n*n)*H := by simpa using Nat.mul_le_mul_right H hNN
  have hbatch : batchBudget small pad xs batches rs≤(D*A+1)*(n*n)*H := by
    have hm:=Nat.mul_le_mul hR hrecord
    unfold batchBudget
    nlinarith
  have hbits:=grid_size_bits n
  have hb : 1≤Transpose.entryBits n := by unfold Transpose.entryBits;omega
  have hm:=Nat.mul_le_mul_left (39*(small+pad)+256) hb
  have hwidth : H≤(39*(small+pad)+340)*Transpose.entryBits n := by dsimp [H];nlinarith
  calc
    _ ≤ (D*A+1)*(n*n)*H := hbatch
    _ ≤ (D*A+1)*(n*n)*((39*(small+pad)+340)*Transpose.entryBits n) := Nat.mul_le_mul_left _ hwidth
    _ = _ := by unfold linearCoefficient Transpose.inputLength;dsimp [A];ring

theorem map_linear_budget {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1))
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size) :
    batchBudget (PaddedWord.commonConstant (F k)) (FamilyNormalization.padding F k) xs
      (FirstWitness.earlierBatches F xs k) (FamilyNormalization.records F xs k)≤
      linearCoefficient (PaddedWord.commonConstant (F k)) (FamilyNormalization.padding F k) k.val
        ((F k).distortion+1) (∑ j : Fin k.val,((F ⟨j.val,by omega⟩).distortion+1))*Transpose.inputLength (Counter.value xs) := by
  exact linear_budget _ _ _ _ _ hn xs hx _ _ (FirstWitness.earlier_records_count F xs k)
    (FamilyNormalization.sparse_rows_count (F k) xs (Counter.value xs) 0)

end TransposeFollowup.FilteredBatch


namespace TransposeFollowup.FirstWitness
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem segments_append {K : ℕ} {α : Type*} (V : Fin K → List α) (a b k : ℕ) (hk : k+a+b≤K) :
    PrefixMembership.segments V k (a+b)=PrefixMembership.segments V k a++PrefixMembership.segments V (k+a) b := by
  induction a generalizing k with
  | zero => simp [PrefixMembership.segments]
  | succ a ih =>
    have hkc : k<K := by omega
    rw [show a+1+b=(a+b)+1 by omega]
    simp only [PrefixMembership.segments,hkc,↓reduceDIte]
    rw [ih (k+1) (by omega)]
    have he : k+1+a=k+(a+1) := by omega
    simp only [he,List.append_assoc]

def normalizedBatch (F : Fin (r+1) → RationalMobius) (xs : List Bool) (i : Fin (r+1)) :=
  NormalizedBatch.inputBatch (FamilyNormalization.normalizedRecords F xs i)
def normalizedTail (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) :=
  PrefixMembership.segments (normalizedBatch F xs) k.val (r+1-k.val)

theorem normalized_stream_eq (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    FamilyNormalization.outputStream F xs=PrefixMembership.segments (normalizedBatch F xs) 0 (r+1) := by
  rw [FamilyNormalization.output_encoding,PrefixMembership.segments_ofFn _ _ _ (by omega)]
  simp only [Nat.zero_add,normalizedBatch,NormalizedBatch.inputBatch,NormalizedBatch.inputBits]

theorem earlier_stream_eq (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) :
    PrefixMembership.stream (earlierBatches F xs k) 0 k.val=
      PrefixMembership.segments (normalizedBatch F xs) 0 k.val := by
  rw [PrefixMembership.stream,PrefixMembership.segments_ofFn _ _ _ (by omega),PrefixMembership.segments_ofFn _ _ _ (by omega)]
  simp only [earlierBatches,normalizedBatch,Nat.zero_add]

theorem normalized_stream_split (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) :
    PrefixMembership.stream (earlierBatches F xs k) 0 k.val++normalizedTail F xs k=FamilyNormalization.outputStream F xs := by
  rw [earlier_stream_eq,normalized_stream_eq]
  unfold normalizedTail
  have hs:=segments_append (normalizedBatch F xs) k.val (r+1-k.val) 0 (by omega)
  have hk : k.val+(r+1-k.val)=r+1 := by omega
  simpa only [Nat.zero_add,hk] using hs.symm

theorem common_query_tape (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k : Fin (r+1)) :
    FilteredBatch.queryTape (earlierBatches F xs k) (normalizedTail F xs k)=⟨[],FamilyNormalization.outputStream F xs⟩ := by
  unfold FilteredBatch.queryTape
  rw [normalized_stream_split]

end TransposeFollowup.FirstWitness


/-! Fixed map phases share one normalized query stream. Each phase reads
its raw batch and appends exactly its least-witness records. -/
namespace TransposeFollowup.FamilySelector
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

inductive Label (F : Fin (r+1) → RationalMobius)
  | phase (i : Fin (r+1)) (pc : FilteredBatch.Label (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val)
  | done
  deriving DecidableEq,Fintype
def identityBinding : FinitePortBinding (Fin 9) (Fin 9) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intro p j;simp [eq_comm]
def entry (F : Fin (r+1) → RationalMobius) (k : ℕ) : Label F :=
  if h : k<r+1 then .phase ⟨k,h⟩ (FilteredBatch.start (PaddedWord.commonConstant (F ⟨k,h⟩)) (FamilyNormalization.padding F ⟨k,h⟩) k) else .done
def program (F : Fin (r+1) → RationalMobius) : Microcode.Program (Fin 9) (Label F)
  | .phase i .done => .jump (entry F (i.val+1))
  | .phase i pc => identityBinding.instruction (Label.phase i)
    (FilteredBatch.program (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val pc)
  | .done => .halt

theorem phase_code (F : Fin (r+1) → RationalMobius) (i : Fin (r+1))
    (pc : FilteredBatch.Label (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val)
    (hh : FilteredBatch.program (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val pc≠.halt)
    (_ : FilteredBatch.program (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val pc≠.reject) :
    program F (.phase i pc)=MicrocodeEmbedding.instruction identityBinding.ports (Label.phase i)
      (FilteredBatch.program (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : FilteredBatch.Bank) (pos : Fin 9 → ℤ) : NativeMicrocode.Config (Fin 9) (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
abbrev Trace (F : Fin (r+1) → RationalMobius) := OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))
def bank (F : Fin (r+1) → RationalMobius) (xs : List Bool) (raw out : Tape Bool) :=
  FilteredBatch.ready xs ⟨[],FamilyNormalization.outputStream F xs⟩ raw out
def outputBatch (F : Fin (r+1) → RationalMobius) (xs : List Bool) (i : Fin (r+1)) :=
  NormalizedBatch.inputBatch (FirstWitness.selected F xs i)
def phaseCoefficient (F : Fin (r+1) → RationalMobius) (i : Fin (r+1)) :=
  FilteredBatch.linearCoefficient (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val
    ((F i).distortion+1) (∑ j : Fin i.val,((F ⟨j.val,by omega⟩).distortion+1))

theorem embed_phase (F : Fin (r+1) → RationalMobius) (i : Fin (r+1))
    (pc : FilteredBatch.Label (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val)
    (s : FilteredBatch.Bank) (pos : Fin 9 → ℤ) (frame : MicrocodeEmbedding.Frame (Fin 9)) :
    MicrocodeEmbedding.embed identityBinding.ports (Label.phase i) (FilteredBatch.cfg pc s pos) frame=cfg (.phase i pc) s pos := by
  unfold MicrocodeEmbedding.embed FilteredBatch.cfg cfg
  simp only [← identityBinding.values_eq_extend]
  rfl

theorem phase_trace (F : Fin (r+1) → RationalMobius) (i : Fin (r+1)) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ (phaseCoefficient F i+1)*Transpose.inputLength (Counter.value xs),Trace F t
      (cfg (entry F i.val) (bank F xs ⟨pre,FamilyNormalization.inputBatch F xs i++suffix⟩ ⟨out,[]⟩) pos)
      (cfg (entry F (i.val+1)) (bank F xs ⟨(FamilyNormalization.inputBatch F xs i).reverse++pre,suffix⟩
        ⟨(outputBatch F xs i).reverse++out,[]⟩)
        (FilteredBatch.advance pos (FamilyNormalization.inputBatch F xs i).length (outputBatch F xs i).length)) := by
  obtain ⟨t,ht,htr⟩:=FirstWitness.batch_trace F xs i (FirstWitness.normalizedTail F xs i) pre suffix out pos
  rw [FirstWitness.common_query_tape] at htr
  have he:=MicrocodeEmbedding.trace_embed identityBinding.ports (Label.phase i)
    (FilteredBatch.program (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val) (program F)
    (FilteredBatch.frame (bank F xs ⟨pre,FamilyNormalization.inputBatch F xs i++suffix⟩ ⟨out,[]⟩) pos) (phase_code F i) htr
  simp only [embed_phase] at he
  have hi : entry F i.val=.phase i (FilteredBatch.start (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val) := by
    simp only [entry,dite_eq_left i.isLt]
  have hb:=ht.trans (FilteredBatch.map_linear_budget F xs i hn hx)
  have hL : 1≤Transpose.inputLength (Counter.value xs) := hn.trans (DimensionCandidate.dimension_le_length _ hn)
  rw [hi]
  refine ⟨t+1,?_,NativeCountedLoop.trace_trans he ?_⟩
  · change t≤phaseCoefficient F i*_ at hb
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,cfg,program]
    · exact .refl _

end TransposeFollowup.FamilySelector


namespace TransposeFollowup.FamilySelector
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def remainingCharge (F : Fin (r+1) → RationalMobius) (k q : ℕ) :=
  (PrefixMembership.segments (fun i => [phaseCoefficient F i+1]) k q).sum
def coefficient (F : Fin (r+1) → RationalMobius) := remainingCharge F 0 (r+1)
def outputStream (F : Fin (r+1) → RationalMobius) (xs : List Bool) :=
  FamilyNormalization.segments (outputBatch F xs) 0 (r+1)

theorem coefficient_eq (F : Fin (r+1) → RationalMobius) :
    coefficient F=∑ i : Fin (r+1),(phaseCoefficient F i+1) := by
  rw [coefficient,remainingCharge,PrefixMembership.segments_ofFn _ _ _ (by omega)]
  simp [Fin.sum_ofFn,Fin.sum_univ_succ]

theorem rest_trace (F : Fin (r+1) → RationalMobius) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (q k : ℕ) (hk : k+q=r+1) (pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ remainingCharge F k q*Transpose.inputLength (Counter.value xs),Trace F t
      (cfg (entry F k) (bank F xs ⟨pre,FamilyNormalization.segments (FamilyNormalization.inputBatch F xs) k q++suffix⟩ ⟨out,[]⟩) pos)
      (cfg .done (bank F xs ⟨(FamilyNormalization.segments (FamilyNormalization.inputBatch F xs) k q).reverse++pre,suffix⟩
        ⟨(FamilyNormalization.segments (outputBatch F xs) k q).reverse++out,[]⟩)
        (FilteredBatch.advance pos (FamilyNormalization.segments (FamilyNormalization.inputBatch F xs) k q).length
          (FamilyNormalization.segments (outputBatch F xs) k q).length)) := by
  induction q generalizing k pre out pos with
  | zero =>
    have he : k=r+1 := by omega
    subst k
    refine ⟨0,by simp [remainingCharge,PrefixMembership.segments],?_⟩
    simp only [entry,lt_self_iff_false,↓reduceDIte,FamilyNormalization.segments,List.nil_append,List.reverse_nil,List.length_nil,FilteredBatch.advance_zero]
    exact .refl _
  | succ q ih =>
    have hkc : k<r+1 := by omega
    let i : Fin (r+1):=⟨k,hkc⟩
    obtain ⟨a,ha,ta⟩:=phase_trace F i xs hn hx pre
      (FamilyNormalization.segments (FamilyNormalization.inputBatch F xs) (k+1) q++suffix) out pos
    obtain ⟨b,hb,tb⟩:=ih (k+1) (by omega) ((FamilyNormalization.inputBatch F xs i).reverse++pre) ((outputBatch F xs i).reverse++out)
      (FilteredBatch.advance pos (FamilyNormalization.inputBatch F xs i).length (outputBatch F xs i).length)
    refine ⟨a+b,?_,?_⟩
    · simp only [remainingCharge,PrefixMembership.segments,hkc,↓reduceDIte,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hb ⊢
      rw [Nat.add_mul]
      dsimp only [i] at ha
      omega
    · simpa only [FamilyNormalization.segments,hkc,↓reduceDIte,List.append_assoc,List.reverse_append,FilteredBatch.advance_add,List.length_append]
        using NativeCountedLoop.trace_trans ta tb

theorem complete_trace (F : Fin (r+1) → RationalMobius) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) :
    ∃ t ≤ coefficient F*Transpose.inputLength (Counter.value xs),Trace F t
      (cfg (entry F 0) (bank F xs ⟨pre,FamilyNormalization.inputStream F xs++suffix⟩ ⟨out,[]⟩) pos)
      (cfg .done (bank F xs ⟨(FamilyNormalization.inputStream F xs).reverse++pre,suffix⟩ ⟨(outputStream F xs).reverse++out,[]⟩)
        (FilteredBatch.advance pos (FamilyNormalization.inputStream F xs).length (outputStream F xs).length)) :=
  rest_trace F xs hn hx (r+1) 0 (by omega) pre suffix out pos

end TransposeFollowup.FamilySelector


namespace TransposeFollowup.FamilySelector
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) := NativeMicrocode.initialEncoding (T:=Fin 9) (entry F 0)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)
def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃
    (Σ i : Fin (r+1),FilteredBatch.Label (PaddedWord.commonConstant (F i)) (FamilyNormalization.padding F i) i.val) ⊕ Unit where
  toFun | .phase i pc => .inl ⟨i,pc⟩ | .done => .inr ()
  invFun | .inl ⟨i,pc⟩ => .phase i pc | .inr _ => .done
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (⟨i,pc⟩|⟨⟩) <;> rfl

theorem batch_label_card (small pad K : ℕ) :
    Fintype.card (FilteredBatch.Label small pad K)=small+2*pad+205+K*(2*(small+pad)+478) := by
  have h:=(FilteredBatch.fixed_resources small pad K).2.2.1
  change Fintype.card (FilteredBatch.Label small pad K)-1+1=_ at h
  have hp : 0<Fintype.card (FilteredBatch.Label small pad K) := Fintype.card_pos_iff.mpr ⟨.done⟩
  omega

theorem fixed_resources (F : Fin (r+1) → RationalMobius) : (nativeMachine F).k=9 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=1+∑ i : Fin (r+1),(PaddedWord.commonConstant (F i)+2*FamilyNormalization.padding F i+205+
      i.val*(2*(PaddedWord.commonConstant (F i)+FamilyNormalization.padding F i)+478)) ∧
    (nativeEncoding F).label (entry F 0)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label F)-1+1=_
  rw [Fintype.card_congr (labelEquiv F)]
  simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_unit,batch_label_card]
  omega

theorem native_complete (F : Fin (r+1) → RationalMobius) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ coefficient F*Transpose.inputLength (Counter.value xs),
      Transpose.stepN (nativeMachine F) input t
        ((cfg (entry F 0) (bank F xs ⟨pre,FamilyNormalization.inputStream F xs++suffix⟩ ⟨out,[]⟩) pos).denote
          (nativeEncoding F) (program F) ip outRev)=
        some ((cfg .done (bank F xs ⟨(FamilyNormalization.inputStream F xs).reverse++pre,suffix⟩ ⟨(outputStream F xs).reverse++out,[]⟩)
          (FilteredBatch.advance pos (FamilyNormalization.inputStream F xs).length (outputStream F xs).length)).denote
          (nativeEncoding F) (program F) ip outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg .done (bank F xs ⟨(FamilyNormalization.inputStream F xs).reverse++pre,suffix⟩ ⟨(outputStream F xs).reverse++out,[]⟩)
          (FilteredBatch.advance pos (FamilyNormalization.inputStream F xs).length (outputStream F xs).length)).denote
          (nativeEncoding F) (program F) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace F xs hn hx pre suffix out pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (F : Fin (r+1) → RationalMobius) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 9 ↪ U) (labels : Label F → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.halt → program F pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F pc))
    (xs : List Bool) (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Fin 9 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ coefficient F*Transpose.inputLength (Counter.value xs),
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (entry F 0) (bank F xs ⟨pre,FamilyNormalization.inputStream F xs++suffix⟩ ⟨out,[]⟩) pos) outerFrame).denote
          encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (bank F xs ⟨(FamilyNormalization.inputStream F xs).reverse++pre,suffix⟩ ⟨(outputStream F xs).reverse++out,[]⟩)
            (FilteredBatch.advance pos (FamilyNormalization.inputStream F xs).length (outputStream F xs).length)) outerFrame).denote
          encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace F xs hn hx pre suffix out pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F) target outerFrame input ip outRev hc htr⟩

theorem output_encoding (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    outputStream F xs=(List.ofFn (fun i : Fin (r+1) => NormalizedBatch.inputBatch (FirstWitness.selected F xs i))).flatten := by
  rw [outputStream,FamilyNormalization.segments_ofFn _ _ _ (by omega)]
  simp only [outputBatch,Nat.zero_add]

end TransposeFollowup.FamilySelector


namespace TransposeFollowup.FamilySelector
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def records (F : Fin (r+1) → RationalMobius) (xs : List Bool) :=
  PrefixMembership.segments (FirstWitness.selected F xs) 0 (r+1)

theorem first_exists (F : Fin (r+1) → RationalMobius) (xs : List Bool) (p : ℕ × ℕ)
    (h : ∃ i,FirstWitness.Occurs F xs i p) : ∃ i,FirstWitness.First F xs i p := by
  classical
  let hits:=(Finset.univ : Finset (Fin (r+1))).filter (fun i => FirstWitness.Occurs F xs i p)
  have hh : hits.Nonempty := by
    obtain ⟨i,hi⟩:=h
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  let i:=hits.min' hh
  have hi : i ∈ hits := Finset.min'_mem hits hh
  refine ⟨i,(Finset.mem_filter.mp hi).2,?_⟩
  intro j hj ho
  have hjh : j ∈ hits := Finset.mem_filter.mpr ⟨Finset.mem_univ j,ho⟩
  exact (not_lt_of_ge (Finset.min'_le hits j hjh)) hj

theorem records_spec (F : Fin (r+1) → RationalMobius) (xs : List Bool) (p : ℕ × ℕ) :
    p ∈ (records F xs).map RowEnumeration.decodePair ↔ ∃ i,FirstWitness.Occurs F xs i p := by
  rw [records,PrefixMembership.mapped_segments_mem]
  simp only [FirstWitness.selected_spec]
  constructor
  · rintro ⟨i,hi⟩;exact ⟨i,hi.1⟩
  · exact first_exists F xs p

theorem records_values (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    (records F xs).map RowEnumeration.decodePair=
      (List.ofFn (fun i : Fin (r+1) => (FirstWitness.selected F xs i).map RowEnumeration.decodePair)).flatten := by
  rw [records,PrefixMembership.segments_ofFn _ _ _ (by omega)]
  simp only [Nat.zero_add,List.map_flatten,List.map_ofFn,Function.comp_def]

theorem records_nodup (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    ((records F xs).map RowEnumeration.decodePair).Nodup := by
  rw [records_values,List.nodup_flatten]
  constructor
  · intro l hl
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hl
    exact FirstWitness.selected_values_nodup F xs i
  · rw [List.pairwise_ofFn]
    intro i j hij
    apply List.disjoint_left.mpr
    intro p hi hj
    have he:=FirstWitness.selected_batches_disjoint F xs i j p hi hj
    exact (ne_of_lt hij) he

theorem directed_union_spec (F : Fin (r+1) → RationalMobius) (xs : List Bool) (i j : Fin (Counter.value xs)) :
    (i.val,j.val) ∈ (records F xs).map RowEnumeration.decodePair ↔ ∃ k,j ∈ (F k).neighbors i := by
  rw [records_spec]
  simp only [FirstWitness.occurs_iff]

theorem output_nonblank (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    ∀ s ∈ outputStream F xs,s≠.blank := by
  rw [output_encoding]
  intro s hs
  obtain ⟨b,hb,hs⟩:=List.mem_flatten.mp hs
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hb
  simp only [NormalizedBatch.inputBatch,List.mem_append,List.mem_singleton] at hs
  rcases hs with hs|rfl
  · obtain ⟨bit,_,rfl⟩:=List.mem_map.mp hs
    simp
  · simp

end TransposeFollowup.FamilySelector
