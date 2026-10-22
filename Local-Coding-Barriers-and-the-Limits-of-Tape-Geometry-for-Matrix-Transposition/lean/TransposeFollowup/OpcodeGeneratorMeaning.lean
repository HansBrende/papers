import TransposeFollowup.NativeBatchSkipRun
import TransposeFollowup.PageEventBatchCanonical
import TransposeFollowup.FamilySelectorMeaning
import TransposeFollowup.PortBindingFrame
import TransposeFollowup.RationalOpcodeWalk
import TransposeFollowup.SchedulerSeedRun
import TransposeFollowup.InPlaceAdd

/-! Skip preceding batches,test the specified batch,and restore the entire
stream/head. The return flag survives in finite control during rewind. -/
namespace TransposeFollowup.PageQuery
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}
abbrev Bank := PageEventBatch.Bank
abbrev queryBank := PageEventBatch.queryBank
abbrev advance := PageEventBatch.advance
abbrev tapeBinding := PrefixMembership.rewindBinding
abbrev identityBinding := PrefixMembership.identityBinding

inductive Label (F : Fin c → RationalMobius) (small K : ℕ)
  | skip (pc : NativeBatchSkip.Label K)
  | batch (pc : PageEventBatch.Label F small)
  | rewind (found : Bool) (pc : NativeSpanRewind.Label)
  deriving DecidableEq,Fintype
def start (F : Fin c → RationalMobius) (small K : ℕ) : Label F small K := .skip (NativeBatchSkip.entry K 0)
def program (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :
    Microcode.Program (Fin 7) (Label F small K)
  | .skip .done => .jump (.batch (PageEventBatch.start F small false))
  | .skip pc => tapeBinding.instruction Label.skip (NativeBatchSkip.program K pc)
  | .batch (.done found) => .jump (.rewind found .left)
  | .batch pc => identityBinding.instruction Label.batch (PageEventBatch.program F small tag incoming page pc)
  | .rewind found pc => tapeBinding.instruction (Label.rewind found) (NativeSpanRewind.program pc)

theorem skip_code (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (pc : NativeBatchSkip.Label K) (hh : NativeBatchSkip.program K pc≠.halt) (_ : NativeBatchSkip.program K pc≠.reject) :
    program F small K tag incoming page (.skip pc)=MicrocodeEmbedding.instruction tapeBinding.ports Label.skip (NativeBatchSkip.program K pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem batch_code (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (pc : PageEventBatch.Label F small) (hh : PageEventBatch.program F small tag incoming page pc≠.halt)
    (_ : PageEventBatch.program F small tag incoming page pc≠.reject) :
    program F small K tag incoming page (.batch pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.batch
      (PageEventBatch.program F small tag incoming page pc) := by
  cases pc with
  | done _ => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem rewind_code (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (pc : NativeSpanRewind.Label) (_ : NativeSpanRewind.program pc≠.halt) (_ : NativeSpanRewind.program pc≠.reject) :
    program F small K tag incoming page (.rewind found pc)=MicrocodeEmbedding.instruction tapeBinding.ports
      (Label.rewind found) (NativeSpanRewind.program pc) := by
  simp only [program,FinitePortBinding.instruction_eq]

def cfg {F : Fin c → RationalMobius} {small K : ℕ} (pc : Label F small K) (s : Bank) (pos : Fin 7 → ℤ) :
    NativeMicrocode.Config (Fin 7) (Label F small K) := ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
abbrev Trace (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :=
  OperationalTrace.Trace (NativeMicrocode.step (program F small K tag incoming page)) (NativeMicrocode.Active (program F small K tag incoming page))

theorem bank_update (xs q : List Bool) (input word : Tape Bool) :
    Function.update (queryBank xs q input) 2 word=queryBank xs q word := by
  funext p;fin_cases p <;> rfl
theorem advanced_positions (pos : Fin 7 → ℤ) (m : ℕ) : Function.update pos 2 (pos 2+m)=advance pos m := by
  funext p;fin_cases p <;> simp [advance,PageEventBatch.advance,BatchMembership.advance]

theorem embed_skip (F : Fin c → RationalMobius) (small K : ℕ) (pc : NativeBatchSkip.Label K)
    (word : Tape Bool) (base : Bank) (pos : Fin 7 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed tapeBinding.ports (Label.skip (F:=F) (small:=small))
      (NativeBatchSkip.cfg pc word (fun _ => z)).denote (BatchMembership.frame base pos)=
      cfg (.skip pc) (Function.update base 2 word) (Function.update pos 2 z) := by
  unfold MicrocodeEmbedding.embed NativeBatchSkip.cfg NativeZipper.Config.denote Microcode.Config.denote cfg BatchMembership.frame
  simp only [← tapeBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem skip_call (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (words : Fin K → List Bool) (xs q : List Bool) (left suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ 2*(NativeBatchSkip.stream words 0 K).length,Trace F small K tag incoming page t
      (cfg (start F small K) (queryBank xs q ⟨left,NativeBatchSkip.stream words 0 K++suffix⟩) pos)
      (cfg (.skip .done) (queryBank xs q ⟨(NativeBatchSkip.stream words 0 K).reverse++left,suffix⟩)
        (advance pos (NativeBatchSkip.stream words 0 K).length)) := by
  obtain ⟨t,ht,htr⟩:=NativeBatchSkip.complete_trace words left suffix (fun _ => pos 2)
  have he:=MicrocodeEmbedding.trace_embed tapeBinding.ports (Label.skip (F:=F) (small:=small)) (NativeBatchSkip.program K)
    (program F small K tag incoming page) (BatchMembership.frame (queryBank xs q ⟨left,NativeBatchSkip.stream words 0 K++suffix⟩) pos)
    (skip_code F small K tag incoming page) htr
  exact ⟨t,ht,by simpa only [embed_skip,bank_update,Function.update_eq_self,advanced_positions,start] using he⟩

theorem embed_batch (F : Fin c → RationalMobius) (small K : ℕ) (pc : PageEventBatch.Label F small)
    (s : Bank) (pos : Fin 7 → ℤ) (frame : MicrocodeEmbedding.Frame (Fin 7)) :
    MicrocodeEmbedding.embed identityBinding.ports (Label.batch (K:=K)) (PageEventBatch.cfg pc s pos) frame=cfg (.batch pc) s pos := by
  unfold MicrocodeEmbedding.embed PageEventBatch.cfg cfg
  simp only [← identityBinding.values_eq_extend]
  rfl

theorem batch_call (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (xs q : List Bool) (hq : q.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ PageEventBatch.batchBudget small xs rs,Trace F small K tag incoming page t
      (cfg (.batch (PageEventBatch.start F small false)) (queryBank xs q ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos)
      (cfg (.batch (.done (rs.any (PageEventBatch.matchesRecord F tag incoming page q))))
        (queryBank xs q ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBatch rs).length)) := by
  obtain ⟨t,ht,htr⟩:=PageEventBatch.batch_trace F small tag incoming page false xs q hq hp rs hw pre suffix pos
  have he:=MicrocodeEmbedding.trace_embed identityBinding.ports (Label.batch (K:=K)) (PageEventBatch.program F small tag incoming page)
    (program F small K tag incoming page) (BatchMembership.frame (queryBank xs q ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos)
    (batch_code F small K tag incoming page) htr
  exact ⟨t,ht,by simpa only [embed_batch,Bool.false_or] using he⟩

theorem jump_trace (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (pc next : Label F small K) (s : Bank) (pos : Fin 7 → ℤ)
    (h : program F small K tag incoming page pc=.jump next) : Trace F small K tag incoming page 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.PageQuery


namespace TransposeFollowup.PageQuery
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c K : ℕ}

theorem embed_rewind (F : Fin c → RationalMobius) (small K : ℕ) (found : Bool) (pc : NativeSpanRewind.Label)
    (word : Tape Bool) (base : Bank) (pos : Fin 7 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed tapeBinding.ports (Label.rewind (F:=F) (small:=small) (K:=K) found)
      (NativeSpanRewind.cfg pc word (fun _ => z)).denote (BatchMembership.frame base pos)=
      cfg (.rewind found pc) (Function.update base 2 word) (Function.update pos 2 z) := by
  unfold MicrocodeEmbedding.embed NativeSpanRewind.cfg NativeZipper.Config.denote Microcode.Config.denote cfg BatchMembership.frame
  simp only [← tapeBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem rewind_call (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (xs q : List Bool) (pre suffix : List (Sym Bool)) (h : ∀ s ∈ pre,s≠.blank) (pos : Fin 7 → ℤ) :
    ∃ t ≤ 2*pre.length+3,Trace F small K tag incoming page t
      (cfg (.rewind found .left) (queryBank xs q ⟨pre.reverse,suffix⟩) (advance pos pre.length))
      (cfg (.rewind found .done) (queryBank xs q ⟨[],pre++suffix⟩) pos) := by
  let adv:=advance pos pre.length
  obtain ⟨t,ht,htr⟩:=NativePrefixRewind.rewind_trace pre suffix h (fun _ => adv 2)
  have he:=MicrocodeEmbedding.trace_embed tapeBinding.ports (Label.rewind (F:=F) (small:=small) (K:=K) found)
    NativeSpanRewind.program (program F small K tag incoming page)
    (BatchMembership.frame (queryBank xs q ⟨pre.reverse,suffix⟩) adv) (rewind_code F small K tag incoming page found) htr
  have hz : adv 2-pre.length=pos 2 := by simp [adv,advance,PageEventBatch.advance,BatchMembership.advance]
  exact ⟨t,ht,by simpa only [embed_rewind,bank_update,Function.update_eq_self,hz,adv,PrefixMembership.restored_positions] using he⟩

def visited (words : Fin K → List Bool) (rs : List (List Bool × List Bool)) :=
  NativeBatchSkip.stream words 0 K++NormalizedBatch.inputBatch rs
def budget (small : ℕ) (xs : List Bool) (words : Fin K → List Bool) (rs : List (List Bool × List Bool)) :=
  4*(NativeBatchSkip.stream words 0 K).length+PageEventBatch.batchBudget small xs rs+2*(NormalizedBatch.inputBatch rs).length+5

theorem visited_nonblank (words : Fin K → List Bool) (rs : List (List Bool × List Bool)) :
    ∀ s ∈ visited words rs,s≠.blank := by
  intro s hs
  rcases List.mem_append.mp hs with hs|hs
  · exact NativeBatchSkip.stream_nonblank words 0 K s hs
  · simp only [NormalizedBatch.inputBatch,List.mem_append,List.mem_singleton] at hs
    rcases hs with hs|rfl
    · obtain ⟨b,_,rfl⟩:=List.mem_map.mp hs;simp
    · simp

theorem complete_trace (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (xs q : List Bool) (hq : q.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (words : Fin K → List Bool) (rs : List (List Bool × List Bool))
    (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ budget small xs words rs,Trace F small K tag incoming page t
      (cfg (start F small K) (queryBank xs q ⟨[],visited words rs++suffix⟩) pos)
      (cfg (.rewind (rs.any (PageEventBatch.matchesRecord F tag incoming page q)) .done)
        (queryBank xs q ⟨[],visited words rs++suffix⟩) pos) := by
  let pre:=NativeBatchSkip.stream words 0 K
  let batch:=NormalizedBatch.inputBatch rs
  let found:=rs.any (PageEventBatch.matchesRecord F tag incoming page q)
  obtain ⟨a,ha,ta⟩:=skip_call F small K tag incoming page words xs q [] (batch++suffix) pos
  simp only [List.append_nil] at ta
  have j1:=jump_trace F small K tag incoming page (.skip .done) (.batch (PageEventBatch.start F small false))
    (queryBank xs q ⟨pre.reverse,batch++suffix⟩) (advance pos pre.length) rfl
  obtain ⟨b,hb,tb⟩:=batch_call F small K tag incoming page xs q hq hp rs hw pre.reverse suffix (advance pos pre.length)
  have j2:=jump_trace F small K tag incoming page (.batch (.done found)) (.rewind found .left)
    (queryBank xs q ⟨batch.reverse++pre.reverse,suffix⟩) (advance (advance pos pre.length) batch.length) rfl
  have tf : Trace F small K tag incoming page (a+1+b+1)
      (cfg (start F small K) (queryBank xs q ⟨[],visited words rs++suffix⟩) pos)
      (cfg (.rewind found .left) (queryBank xs q ⟨(visited words rs).reverse,suffix⟩) (advance pos (visited words rs).length)) := by
    simpa only [visited,List.append_assoc,List.reverse_append,List.length_append,BatchMembership.advance_add]
      using NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta j1) tb) j2
  obtain ⟨d,hd,td⟩:=rewind_call F small K tag incoming page found xs q (visited words rs) suffix (visited_nonblank words rs) pos
  refine ⟨a+1+b+1+d,?_,NativeCountedLoop.trace_trans tf td⟩
  dsimp only [budget]
  simp only [visited,List.length_append] at hd
  omega

end TransposeFollowup.PageQuery


namespace TransposeFollowup.PageQuery
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c K : ℕ}

noncomputable def nativeEncoding (F : Fin c → RationalMobius) (small K : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 7) (start F small K)
noncomputable def nativeMachine (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :=
  NativeMicrocode.machine (nativeEncoding F small K) (program F small K tag incoming page)

def labelEquiv (F : Fin c → RationalMobius) (small K : ℕ) : Label F small K ≃
    NativeBatchSkip.Label K ⊕ PageEventBatch.Label F small ⊕ (Bool × NativeSpanRewind.Label) where
  toFun | .skip pc => .inl pc | .batch pc => .inr (.inl pc) | .rewind f pc => .inr (.inr (f,pc))
  invFun | .inl pc => .skip pc | .inr (.inl pc) => .batch pc | .inr (.inr (f,pc)) => .rewind f pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc|⟨f,pc⟩) <;> rfl

theorem label_card (F : Fin c → RationalMobius) (small K : ℕ) :
    Fintype.card (Label F small K)=3*K+Fintype.card (PageEventBatch.Label F small)+10 := by
  rw [Fintype.card_congr (labelEquiv F small K)]
  have hr : Fintype.card NativeSpanRewind.Label=4 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,NativeBatchSkip.label_card,hr]
  omega
theorem fixed_resources (F : Fin c → RationalMobius) (small K : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :
    (nativeMachine F small K tag incoming page).k=7 ∧ (nativeMachine F small K tag incoming page).g+1=5 ∧
    (nativeMachine F small K tag incoming page).q+1=3*K+Fintype.card (PageEventBatch.Label F small)+10 ∧
    (nativeEncoding F small K).label (start F small K)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label F small K)-1+1=_
  rw [label_card];omega

theorem native_complete (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (xs q : List Bool) (hq : q.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (words : Fin K → List Bool) (rs : List (List Bool × List Bool))
    (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget small xs words rs,
      Transpose.stepN (nativeMachine F small K tag incoming page) input t
        ((cfg (start F small K) (queryBank xs q ⟨[],visited words rs++suffix⟩) pos).denote
          (nativeEncoding F small K) (program F small K tag incoming page) ip outRev)=
        some ((cfg (.rewind (rs.any (PageEventBatch.matchesRecord F tag incoming page q)) .done)
          (queryBank xs q ⟨[],visited words rs++suffix⟩) pos).denote
          (nativeEncoding F small K) (program F small K tag incoming page) ip outRev) ∧
      Transpose.step (nativeMachine F small K tag incoming page) input
        ((cfg (.rewind (rs.any (PageEventBatch.matchesRecord F tag incoming page q)) .done)
          (queryBank xs q ⟨[],visited words rs++suffix⟩) pos).denote
          (nativeEncoding F small K) (program F small K tag incoming page) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace F small tag incoming page xs q hq hp words rs hw suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F small K) (program F small K tag incoming page) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F small K) (program F small K tag incoming page) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program,FinitePortBinding.instruction,NativeSpanRewind.program]

theorem native_call {U J : Type*} {k s : ℕ} (encoding : NativeMicrocode.Encoding U J k s)
    (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (ports : Fin 7 ↪ U) (labels : Label F small K → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F small K tag incoming page pc≠.halt → program F small K tag incoming page pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F small K tag incoming page pc))
    (xs q : List Bool) (hq : q.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (words : Fin K → List Bool) (rs : List (List Bool × List Bool))
    (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget small xs words rs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F small K)
          (queryBank xs q ⟨[],visited words rs++suffix⟩) pos) outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.rewind (rs.any (PageEventBatch.matchesRecord F tag incoming page q)) .done)
            (queryBank xs q ⟨[],visited words rs++suffix⟩) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace F small tag incoming page xs q hq hp words rs hw suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F small K tag incoming page) target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.PageQuery


namespace TransposeFollowup.PageQuery
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def beforeWords (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) : Fin tag.val → List Bool :=
  fun i => NormalizedBatch.inputBits (FirstWitness.selected F xs ⟨i.val,lt_trans i.isLt tag.isLt⟩)
def tail (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :=
  PrefixMembership.stream (FirstWitness.selected F xs) (tag.val+1) (r-tag.val)

theorem canonical_stream_eq (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    FamilySelector.outputStream F xs=PrefixMembership.stream (FirstWitness.selected F xs) 0 (r+1) := by
  rw [FamilySelector.output_encoding,PrefixMembership.stream,PrefixMembership.segments_ofFn _ _ _ (by omega)]
  simp only [Nat.zero_add]

theorem before_eq (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :
    NativeBatchSkip.stream (beforeWords F xs tag) 0 tag.val=PrefixMembership.stream (FirstWitness.selected F xs) 0 tag.val := by
  rw [NativeBatchSkip.stream,PrefixMembership.stream,PrefixMembership.segments_ofFn _ _ _ (by omega),
    PrefixMembership.segments_ofFn _ _ _ (by omega)]
  simp only [Nat.zero_add,beforeWords,NativeBatchSkip.block,NormalizedBatch.inputBatch]

theorem visited_eq (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :
    visited (beforeWords F xs tag) (FirstWitness.selected F xs tag)=
      PrefixMembership.stream (FirstWitness.selected F xs) 0 (tag.val+1) := by
  rw [visited,before_eq]
  unfold PrefixMembership.stream
  rw [FirstWitness.segments_append _ tag.val 1 0 (by omega)]
  simp only [Nat.zero_add,PrefixMembership.segments,tag.isLt,↓reduceDIte,List.append_nil]

theorem stream_split (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :
    visited (beforeWords F xs tag) (FirstWitness.selected F xs tag)++tail F xs tag=FamilySelector.outputStream F xs := by
  rw [visited_eq,canonical_stream_eq]
  unfold tail PrefixMembership.stream
  have hs:=FirstWitness.segments_append (fun i => NormalizedBatch.inputBatch (FirstWitness.selected F xs i))
    (tag.val+1) (r-tag.val) 0 (by omega)
  have hk : tag.val+1+(r-tag.val)=r+1 := by omega
  simpa only [Nat.zero_add,hk] using hs.symm

theorem before_length_le (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :
    (NativeBatchSkip.stream (beforeWords F xs tag) 0 tag.val).length≤(FamilySelector.outputStream F xs).length := by
  rw [← stream_split F xs tag]
  simp only [visited,List.length_append]
  omega
theorem batch_length_le (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :
    (NormalizedBatch.inputBatch (FirstWitness.selected F xs tag)).length≤(FamilySelector.outputStream F xs).length := by
  rw [← stream_split F xs tag]
  simp only [visited,List.length_append]
  omega

end TransposeFollowup.PageQuery


namespace TransposeFollowup.PageQuery
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem input_bits_length (m : ℕ) (rs : List (List Bool × List Bool))
    (hw : ∀ p ∈ rs,p.1.length=m ∧ p.2.length=m) :
    (NormalizedBatch.inputBits rs).length=2*m*rs.length := by
  induction rs with
  | nil => simp [NormalizedBatch.inputBits]
  | cons p rs ih =>
    have hp:=hw p (by simp)
    have hs:=ih (by intro q hq;exact hw q (by simp [hq]))
    simp only [NormalizedBatch.inputBits,List.flatMap_cons,List.length_append,List.length_cons]
    change p.1.length+p.2.length+(NormalizedBatch.inputBits rs).length=2*m*(rs.length+1)
    rw [hp.1,hp.2,hs]
    ring

theorem selected_batch_length (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :
    (NormalizedBatch.inputBatch (FirstWitness.selected F xs tag)).length=
      2*(2*xs.length+FamilyNormalization.common F)*(FirstWitness.selected F xs tag).length+1 := by
  have hw : ∀ p ∈ FirstWitness.selected F xs tag,
      p.1.length=2*xs.length+FamilyNormalization.common F ∧ p.2.length=2*xs.length+FamilyNormalization.common F := by
    intro p hp;exact NativeResidueColor.selected_width F xs tag p.1 p.2 hp
  simp only [NormalizedBatch.inputBatch,List.length_append,symbols,List.length_map,List.length_singleton,input_bits_length _ _ hw]

def neighborSum (F : Fin (r+1) → RationalMobius) := ∑ i : Fin (r+1),((F i).distortion+1)

theorem selected_total_count (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    (∑ i : Fin (r+1),(FirstWitness.selected F xs i).length)≤Counter.value xs*neighborSum F := by
  unfold neighborSum
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => PageEventBatch.selected_count F xs i)

theorem canonical_length_le (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    (FamilySelector.outputStream F xs).length≤
      2*(2*xs.length+FamilyNormalization.common F)*(Counter.value xs*neighborSum F)+(r+1) := by
  calc
    _ = ∑ i : Fin (r+1),(NormalizedBatch.inputBatch (FirstWitness.selected F xs i)).length := by
      rw [FamilySelector.output_encoding]
      simp [Fin.sum_ofFn,Fin.sum_univ_succ]
    _ = ∑ i : Fin (r+1),(2*(2*xs.length+FamilyNormalization.common F)*(FirstWitness.selected F xs i).length+1) :=
      Finset.sum_congr rfl (fun i _ => selected_batch_length F xs i)
    _ = 2*(2*xs.length+FamilyNormalization.common F)*(∑ i : Fin (r+1),(FirstWitness.selected F xs i).length)+(r+1) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ (selected_total_count F xs)) _

theorem map_density_le (F : Fin (r+1) → RationalMobius) (tag : Fin (r+1)) :
    (F tag).distortion+1≤neighborSum F := by
  exact Finset.single_le_sum (fun i _ => Nat.zero_le ((F i).distortion+1)) (Finset.mem_univ tag)

def canonicalBudget (F : Fin (r+1) → RationalMobius) (xs : List Bool) :=
  (Counter.value xs*neighborSum F+(r+1)+1)*(120*xs.length+60*FamilyNormalization.common F+140)

theorem budget_le (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :
    budget (FamilyNormalization.common F) xs (beforeWords F xs tag) (FirstWitness.selected F xs tag)≤canonicalBudget F xs := by
  let R:=Counter.value xs*neighborSum F
  let C:=FamilyNormalization.common F
  let L:=xs.length
  have hpre:=before_length_le F xs tag
  have hbatch:=batch_length_le F xs tag
  have hlen:=canonical_length_le F xs
  have hr : Counter.value xs*((F tag).distortion+1)≤R := Nat.mul_le_mul_left _ (map_density_le F tag)
  have hb : PageEventBatch.batchBudget C xs (FirstWitness.selected F xs tag)≤(R+1)*(90*L+42*C+92) :=
    (PageEventBatch.selected_budget_le F xs tag).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hr 1))
  have hforward : budget C xs (beforeWords F xs tag) (FirstWitness.selected F xs tag)≤
      6*(2*(2*L+C)*R+(r+1))+(R+1)*(90*L+42*C+92)+5 := by
    dsimp only [budget]
    change (FamilySelector.outputStream F xs).length≤2*(2*L+C)*R+(r+1) at hlen
    omega
  change _≤(R+(r+1)+1)*(120*L+60*C+140)
  apply hforward.trans
  nlinarith [Nat.zero_le (R*L),Nat.zero_le (R*C),Nat.zero_le ((r+1)*L),Nat.zero_le ((r+1)*C)]

end TransposeFollowup.PageQuery


namespace TransposeFollowup.PageQuery
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem canonical_trace (F : Fin (r+1) → RationalMobius) (xs q : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (hq : BinaryCompare.value q=v.val)
    (hw : q.length=2*xs.length+FamilyNormalization.common F) (page : Fin (rationalPageCount F)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ canonicalBudget F xs,
      Trace F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val (PageEventBatch.pageTag F page) incoming page t
        (cfg (start F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val)
          (queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) pos)
        (cfg (.rewind (PageEventBatch.event F xs incoming v page) .done)
          (queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) pos) := by
  let tag:=PageEventBatch.pageTag F page
  have hp : 0<2*xs.length+FamilyNormalization.common F := by
    have h:=(RowEnumeration.common_positive (F tag) xs)
    rw [PaddedWord.word_length] at h
    have hc:=FamilyNormalization.le_common F tag
    omega
  obtain ⟨t,ht,htr⟩:=complete_trace F (FamilyNormalization.common F) tag incoming page xs q hw hp
    (beforeWords F xs tag) (FirstWitness.selected F xs tag)
    (by intro p hp;exact NativeResidueColor.selected_width F xs tag p.1 p.2 hp) (tail F xs tag) pos
  exact ⟨t,ht.trans (budget_le F xs tag),by
    simpa only [stream_split,tag,PageEventBatch.result_eq F xs q incoming v hq page] using htr⟩

theorem native_canonical (F : Fin (r+1) → RationalMobius) (xs q : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (hq : BinaryCompare.value q=v.val)
    (hw : q.length=2*xs.length+FamilyNormalization.common F) (page : Fin (rationalPageCount F)) (pos : Fin 7 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ canonicalBudget F xs,
      Transpose.stepN (nativeMachine F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val
        (PageEventBatch.pageTag F page) incoming page) input t
        ((cfg (start F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val)
          (queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) pos).denote
          (nativeEncoding F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val)
          (program F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val (PageEventBatch.pageTag F page) incoming page) ip outRev)=
        some ((cfg (.rewind (PageEventBatch.event F xs incoming v page) .done)
          (queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) pos).denote
          (nativeEncoding F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val)
          (program F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val (PageEventBatch.pageTag F page) incoming page) ip outRev) ∧
      Transpose.step (nativeMachine F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val
        (PageEventBatch.pageTag F page) incoming page) input
        ((cfg (.rewind (PageEventBatch.event F xs incoming v page) .done)
          (queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) pos).denote
          (nativeEncoding F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val)
          (program F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val (PageEventBatch.pageTag F page) incoming page) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=canonical_trace F xs q incoming v hq hw page pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN _ _ input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff _ _ input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program,FinitePortBinding.instruction,NativeSpanRewind.program]

theorem canonical_call {U J : Type*} {k s : ℕ} (encoding : NativeMicrocode.Encoding U J k s)
    (F : Fin (r+1) → RationalMobius) (incoming : Bool) (page : Fin (rationalPageCount F))
    (ports : Fin 7 ↪ U) (labels : Label F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val (PageEventBatch.pageTag F page) incoming page pc≠.halt →
      program F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val (PageEventBatch.pageTag F page) incoming page pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels
        (program F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val (PageEventBatch.pageTag F page) incoming page pc))
    (xs q : List Bool) (v : Fin (Counter.value xs)) (hq : BinaryCompare.value q=v.val)
    (hw : q.length=2*xs.length+FamilyNormalization.common F) (pos : Fin 7 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ canonicalBudget F xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (start F (FamilyNormalization.common F) (PageEventBatch.pageTag F page).val)
            (queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) pos) outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.rewind (PageEventBatch.event F xs incoming v page) .done)
            (queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=canonical_trace F xs q incoming v hq hw page pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels _ target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.PageQuery


/-! The proved query costs for all2Nvertices and every fixed page fit the
original input-length allowance. This does not yet implement the outer
counter/page scheduler or pay for its separate work. -/
namespace TransposeFollowup.PageQuery
open FixedTapeCompiler
set_option autoImplicit false
variable {r : ℕ}

def iterationCoefficient (F : Fin (r+1) → RationalMobius) :=
  2*rationalPageCount F*(neighborSum F+(r+1)+1)*(60*FamilyNormalization.common F+500)

theorem all_vertex_page_budget (F : Fin (r+1) → RationalMobius) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size) :
    2*Counter.value xs*rationalPageCount F*canonicalBudget F xs≤
      iterationCoefficient F*Transpose.inputLength (Counter.value xs) := by
  let n:=Counter.value xs
  let S:=neighborSum F
  let C:=FamilyNormalization.common F
  let Q:=rationalPageCount F
  have hcount : n*S+(r+1)+1≤n*(S+(r+1)+1) := by
    have h:=Nat.mul_le_mul_right ((r+1)+1) hn
    dsimp only [n] at h ⊢
    nlinarith
  have hbits:=grid_size_bits n
  have hb : 1≤Transpose.entryBits n := by unfold Transpose.entryBits;omega
  have hw : 120*xs.length+60*C+140≤(60*C+500)*Transpose.entryBits n := by
    have hm:=Nat.mul_le_mul_right (60*C+380) hb
    nlinarith
  have hquery : canonicalBudget F xs≤n*(S+(r+1)+1)*((60*C+500)*Transpose.entryBits n) :=
    Nat.mul_le_mul hcount hw
  calc
    _ ≤ (2*n*Q)*(n*(S+(r+1)+1)*((60*C+500)*Transpose.entryBits n)) := Nat.mul_le_mul_left _ hquery
    _ = _ := by unfold iterationCoefficient Transpose.inputLength;dsimp [n,S,C,Q];ring

end TransposeFollowup.PageQuery


/-! A finite page loop calls the paid reusable query and physically writes
two opcode bits per page. The page set is fixed by F; the vertex is on tape. -/
namespace TransposeFollowup.PageLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

abbrev Page (F : Fin (r+1) → RationalMobius) := Fin (rationalPageCount F)
abbrev QueryLabel (F : Fin (r+1) → RationalMobius) (p : Page F) :=
  PageQuery.Label F (FamilyNormalization.common F) (PageEventBatch.pageTag F p).val

inductive Label (F : Fin (r+1) → RationalMobius)
  | query (page : Page F) (pc : QueryLabel F page)
  | write (page : Page F) (found second : Bool)
  | advance (page : Page F)
  | done
  deriving DecidableEq,Fintype

def queryBinding : FinitePortBinding (Fin 7) (Fin 8) where
  ports:=⟨![0,1,2,3,4,5,6],by decide +kernel⟩
  decode:=fun p => if h:p.val<7 then some ⟨p.val,h⟩ else none
  decode_spec:=by decide +kernel

def queryStart (F : Fin (r+1) → RationalMobius) (p : Page F) : QueryLabel F p :=
  PageQuery.start F (FamilyNormalization.common F) (PageEventBatch.pageTag F p).val
def entry (F : Fin (r+1) → RationalMobius) (k : ℕ) : Label F :=
  if h:k<rationalPageCount F then .query ⟨k,h⟩ (queryStart F ⟨k,h⟩) else .done
def queryProgram (F : Fin (r+1) → RationalMobius) (incoming : Bool) (p : Page F) :=
  PageQuery.program F (FamilyNormalization.common F) (PageEventBatch.pageTag F p).val
    (PageEventBatch.pageTag F p) incoming p
def program (F : Fin (r+1) → RationalMobius) (incoming : Bool) : Microcode.Program (Fin 8) (Label F)
  | .query p (.rewind found .done) => .jump (.write p found false)
  | .query p pc => queryBinding.instruction (Label.query p) (queryProgram F incoming p pc)
  | .write p found false => .act (Microcode.single 7 ⟨some (.data found),.right⟩) (.write p found true)
  | .write p found true => .act (Microcode.single 7 ⟨some (.data (found && incoming)),.right⟩) (.advance p)
  | .advance p => .jump (entry F (p.val+1))
  | .done => .halt

theorem query_code (F : Fin (r+1) → RationalMobius) (incoming : Bool) (p : Page F) (pc : QueryLabel F p)
    (hh : queryProgram F incoming p pc≠.halt) (_ : queryProgram F incoming p pc≠.reject) :
    program F incoming (.query p pc)=MicrocodeEmbedding.instruction queryBinding.ports (Label.query p) (queryProgram F incoming p pc) := by
  cases pc with
  | rewind found pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,FinitePortBinding.instruction_eq]
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def bank (s : PageQuery.Bank) (out : Tape Bool) : Fin 8 → Tape Bool := queryBinding.values s (fun _ => out)
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : PageQuery.Bank) (out : Tape Bool) (pos : Fin 8 → ℤ) :
    NativeMicrocode.Config (Fin 8) (Label F) := ⟨⟨pc,fun p => (bank s out p).denote⟩,pos⟩
def zipperCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : PageQuery.Bank) (out : Tape Bool) (pos : Fin 8 → ℤ) :
    NativeZipper.Config (Fin 8) (Label F) := ⟨⟨pc,bank s out⟩,pos⟩
def frame (s : PageQuery.Bank) (out : Tape Bool) (pos : Fin 8 → ℤ) : MicrocodeEmbedding.Frame (Fin 8) :=
  ⟨fun p => (bank s out p).denote,pos⟩
def advance (pos : Fin 8 → ℤ) (m : ℕ) : Fin 8 → ℤ := fun p => if p=7 then pos p+m else pos p
abbrev Trace (F : Fin (r+1) → RationalMobius) (incoming : Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program F incoming)) (NativeMicrocode.Active (program F incoming))

theorem advance_zero (pos : Fin 8 → ℤ) : advance pos 0=pos := by
  funext p;simp [advance]
theorem advance_add (pos : Fin 8 → ℤ) (a b : ℕ) : advance (advance pos a) b=advance pos (a+b) := by
  funext p;by_cases h:p=7 <;> simp [advance,h,add_assoc]

theorem embed_query (F : Fin (r+1) → RationalMobius) (p : Page F) (pc : QueryLabel F p)
    (s : PageQuery.Bank) (out : Tape Bool) (pos : Fin 8 → ℤ) :
    MicrocodeEmbedding.embed queryBinding.ports (Label.query p)
      (PageQuery.cfg pc s (fun t => pos (queryBinding.ports t))) (frame s out pos)=cfg (.query p pc) s out pos := by
  unfold MicrocodeEmbedding.embed PageQuery.cfg frame cfg
  simp only [← queryBinding.values_eq_extend,FinitePortBinding.values_project]
  congr 1
  simp only [bank,← FinitePortBinding.map_values,FinitePortBinding.values_overwrite]

theorem query_call (F : Fin (r+1) → RationalMobius) (incoming : Bool) (p : Page F)
    (xs q : List Bool) (v : Fin (Counter.value xs)) (hq : BinaryCompare.value q=v.val)
    (hw : q.length=2*xs.length+FamilyNormalization.common F) (out : Tape Bool) (pos : Fin 8 → ℤ) :
    ∃ t ≤ PageQuery.canonicalBudget F xs,Trace F incoming t
      (cfg (.query p (queryStart F p)) (PageQuery.queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) out pos)
      (cfg (.query p (.rewind (PageEventBatch.event F xs incoming v p) .done))
        (PageQuery.queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) out pos) := by
  obtain ⟨t,ht,htr⟩:=PageQuery.canonical_trace F xs q incoming v hq hw p (fun t => pos (queryBinding.ports t))
  have he:=MicrocodeEmbedding.trace_embed queryBinding.ports (Label.query p) (queryProgram F incoming p)
    (program F incoming) (frame (PageQuery.queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) out pos)
    (query_code F incoming p) htr
  exact ⟨t,ht,by simpa only [embed_query,queryStart] using he⟩

theorem jump_trace (F : Fin (r+1) → RationalMobius) (incoming : Bool) (pc next : Label F)
    (s : PageQuery.Bank) (out : Tape Bool) (pos : Fin 8 → ℤ) (h : program F incoming pc=.jump next) :
    Trace F incoming 1 (cfg pc s out pos) (cfg next s out pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.PageLoop


namespace TransposeFollowup.PageLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def opcodeBits : PageOpcode → List Bool
  | .idle => [false,false]
  | .openEdge => [true,false]
  | .closeEdge => [true,true]
def bits (incoming found : Bool) : List Bool := [found,found && incoming]
def record (F : Fin (r+1) → RationalMobius) (xs : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (p : Page F) := bits incoming (PageEventBatch.event F xs incoming v p)
def rowFrom (F : Fin (r+1) → RationalMobius) (xs : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (k q : ℕ) := PrefixMembership.segments (record F xs incoming v) k q
def row (F : Fin (r+1) → RationalMobius) (xs : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) := rowFrom F xs incoming v 0 (rationalPageCount F)

theorem opcodeBits_injective : Function.Injective opcodeBits := by
  intro a b h;cases a <;> cases b <;> simp_all [opcodeBits]
theorem bits_length (incoming found : Bool) : (bits incoming found).length=2 := rfl
theorem record_opcode (F : Fin (r+1) → RationalMobius) (xs : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (p : Page F) :
    record F xs incoming v p=opcodeBits (rationalPageOpcode F (if incoming then OrderedBipartite.right v else OrderedBipartite.left v) p) := by
  rw [PageEventBatch.event_opcode]
  unfold record bits
  cases incoming <;> cases PageEventBatch.event F xs _ v p <;> rfl

theorem rowFrom_length (F : Fin (r+1) → RationalMobius) (xs : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (q k : ℕ) (hk:k+q≤rationalPageCount F) :
    (rowFrom F xs incoming v k q).length=2*q := by
  induction q generalizing k with
  | zero => simp [rowFrom,PrefixMembership.segments]
  | succ q ih =>
    have h:k<rationalPageCount F:=by omega
    simp only [rowFrom,PrefixMembership.segments,h,↓reduceDIte,List.length_append,record,bits_length]
    have hi:=ih (k+1) (by omega)
    dsimp only [rowFrom] at hi
    omega
theorem row_length (F : Fin (r+1) → RationalMobius) (xs : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) : (row F xs incoming v).length=2*rationalPageCount F :=
  rowFrom_length F xs incoming v _ _ (by omega)
theorem row_eq_table (F : Fin (r+1) → RationalMobius) (xs : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) :
    row F xs incoming v=((rationalOpcodeTable F (Counter.value xs)).get
      (if incoming then OrderedBipartite.right v else OrderedBipartite.left v)).toList.flatMap opcodeBits := by
  unfold row rowFrom
  rw [PrefixMembership.segments_ofFn _ _ _ (by omega)]
  simp only [Nat.zero_add,record_opcode]
  simp [rationalOpcodeTable,List.Vector.toList_ofFn,List.ofFn_eq_map,List.flatMap_def,Function.comp_def]

end TransposeFollowup.PageLoop


namespace TransposeFollowup.PageLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem write_two_run (F : Fin (r+1) → RationalMobius) (incoming : Bool) (p : Page F) (found : Bool)
    (s : PageQuery.Bank) (pre : List (Sym Bool)) (pos : Fin 8 → ℤ) :
    NativeZipper.run (program F incoming) 2 (zipperCfg (.write p found false) s ⟨pre,[]⟩ pos)=
      zipperCfg (.advance p) s ⟨(symbols (bits incoming found)).reverse++pre,[]⟩ (advance pos 2) := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,zipperCfg]
  congr 1
  · congr 1
    funext t
    fin_cases t <;> simp [bank,queryBinding,FinitePortBinding.values,Microcode.single,Microcode.Action.apply,
      Tape.write,Tape.moveRight,Tape.read,symbols,bits]
  · funext t
    fin_cases t <;> simp [Microcode.single,NativeMicrocode.direction,Transpose.Dir.shift,advance]
    omega

theorem write_trace (F : Fin (r+1) → RationalMobius) (incoming : Bool) (p : Page F) (found : Bool)
    (s : PageQuery.Bank) (pre : List (Sym Bool)) (pos : Fin 8 → ℤ) :
    ∃ t ≤ 2,Trace F incoming t (cfg (.write p found false) s ⟨pre,[]⟩ pos)
      (cfg (.advance p) s ⟨(symbols (bits incoming found)).reverse++pre,[]⟩ (advance pos 2)) :=
  NativeZipper.trace_of_run (program F incoming) (write_two_run F incoming p found s pre pos)

theorem page_trace (F : Fin (r+1) → RationalMobius) (incoming : Bool) (p : Page F)
    (xs q : List Bool) (v : Fin (Counter.value xs)) (hq : BinaryCompare.value q=v.val)
    (hw : q.length=2*xs.length+FamilyNormalization.common F) (pre : List (Sym Bool)) (pos : Fin 8 → ℤ) :
    ∃ t ≤ PageQuery.canonicalBudget F xs+4,Trace F incoming t
      (cfg (entry F p.val) (PageQuery.queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩) ⟨pre,[]⟩ pos)
      (cfg (entry F (p.val+1)) (PageQuery.queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩)
        ⟨(symbols (record F xs incoming v p)).reverse++pre,[]⟩ (advance pos 2)) := by
  let s:=PageQuery.queryBank xs q ⟨[],FamilySelector.outputStream F xs⟩
  let found:=PageEventBatch.event F xs incoming v p
  obtain ⟨a,ha,ta⟩:=query_call F incoming p xs q v hq hw ⟨pre,[]⟩ pos
  have ja:=jump_trace F incoming (.query p (.rewind found .done)) (.write p found false) s ⟨pre,[]⟩ pos rfl
  obtain ⟨b,hb,tb⟩:=write_trace F incoming p found s pre pos
  have jb:=jump_trace F incoming (.advance p) (entry F (p.val+1)) s
    ⟨(symbols (bits incoming found)).reverse++pre,[]⟩ (advance pos 2) rfl
  refine ⟨a+1+b+1,by omega,?_⟩
  simpa only [entry,dite_eq_left p.isLt,record] using
    NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta ja) tb) jb

end TransposeFollowup.PageLoop


namespace TransposeFollowup.PageLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def budget (F : Fin (r+1) → RationalMobius) (xs : List Bool) :=
  rationalPageCount F*(PageQuery.canonicalBudget F xs+4)

theorem rest_trace (F : Fin (r+1) → RationalMobius) (incoming : Bool)
    (xs word : List Bool) (v : Fin (Counter.value xs)) (hq : BinaryCompare.value word=v.val)
    (hw : word.length=2*xs.length+FamilyNormalization.common F)
    (count k : ℕ) (hk:k+count=rationalPageCount F) (pre : List (Sym Bool)) (pos : Fin 8 → ℤ) :
    ∃ t ≤ count*(PageQuery.canonicalBudget F xs+4),Trace F incoming t
      (cfg (entry F k) (PageQuery.queryBank xs word ⟨[],FamilySelector.outputStream F xs⟩) ⟨pre,[]⟩ pos)
      (cfg .done (PageQuery.queryBank xs word ⟨[],FamilySelector.outputStream F xs⟩)
        ⟨(symbols (rowFrom F xs incoming v k count)).reverse++pre,[]⟩ (advance pos (2*count))) := by
  induction count generalizing k pre pos with
  | zero =>
    have he:k=rationalPageCount F:=by omega
    subst k
    refine ⟨0,by simp,?_⟩
    simp only [entry,lt_self_iff_false,↓reduceDIte,rowFrom,PrefixMembership.segments,
      symbols,List.map_nil,List.reverse_nil,List.nil_append,Nat.mul_zero,advance_zero]
    exact .refl _
  | succ count ih =>
    have hlt:k<rationalPageCount F:=by omega
    let p:Page F:=⟨k,hlt⟩
    obtain ⟨a,ha,ta⟩:=page_trace F incoming p xs word v hq hw pre pos
    obtain ⟨b,hb,tb⟩:=ih (k+1) (by omega) ((symbols (record F xs incoming v p)).reverse++pre) (advance pos 2)
    refine ⟨a+b,by nlinarith,?_⟩
    have hp:2+2*count=2*(count+1):=by omega
    simpa only [rowFrom,PrefixMembership.segments,hlt,↓reduceDIte,symbols,List.map_append,
      List.reverse_append,List.append_assoc,advance_add,hp] using NativeCountedLoop.trace_trans ta tb

theorem complete_trace (F : Fin (r+1) → RationalMobius) (incoming : Bool)
    (xs word : List Bool) (v : Fin (Counter.value xs)) (hq : BinaryCompare.value word=v.val)
    (hw : word.length=2*xs.length+FamilyNormalization.common F) (pre : List (Sym Bool)) (pos : Fin 8 → ℤ) :
    ∃ t ≤ budget F xs,Trace F incoming t
      (cfg (entry F 0) (PageQuery.queryBank xs word ⟨[],FamilySelector.outputStream F xs⟩) ⟨pre,[]⟩ pos)
      (cfg .done (PageQuery.queryBank xs word ⟨[],FamilySelector.outputStream F xs⟩)
        ⟨(symbols (row F xs incoming v)).reverse++pre,[]⟩ (advance pos (2*rationalPageCount F))) :=
  rest_trace F incoming xs word v hq hw _ 0 (by omega) pre pos

def allVerticesCoefficient (F : Fin (r+1) → RationalMobius) :=
  PageQuery.iterationCoefficient F+8*rationalPageCount F

/-- Includes every query, its return transfer, two output writes and the
next-page transfer. Vertex updates and initialization are separate. -/
theorem all_vertices_budget (F : Fin (r+1) → RationalMobius) (xs : List Bool)
    (hn:1≤Counter.value xs) (hx:xs.length≤(Counter.value xs+1).size) :
    2*Counter.value xs*budget F xs≤allVerticesCoefficient F*Transpose.inputLength (Counter.value xs) := by
  have hq:=PageQuery.all_vertex_page_budget F xs hn hx
  have hb:1≤Transpose.entryBits (Counter.value xs):=by unfold Transpose.entryBits;omega
  have hnP:Counter.value xs≤Transpose.inputLength (Counter.value xs):=by
    unfold Transpose.inputLength
    have h:=Nat.mul_le_mul_left (Counter.value xs*Counter.value xs) hb
    nlinarith
  have ho:=Nat.mul_le_mul_left (8*rationalPageCount F) hnP
  unfold budget allVerticesCoefficient
  nlinarith

end TransposeFollowup.PageLoop


namespace TransposeFollowup.PageLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) := NativeMicrocode.initialEncoding (T:=Fin 8) (entry F 0)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) (incoming : Bool) :=
  NativeMicrocode.machine (nativeEncoding F) (program F incoming)

theorem native_complete (F : Fin (r+1) → RationalMobius) (incoming : Bool)
    (xs word : List Bool) (v : Fin (Counter.value xs)) (hq : BinaryCompare.value word=v.val)
    (hw : word.length=2*xs.length+FamilyNormalization.common F) (pre : List (Sym Bool)) (pos : Fin 8 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget F xs,
      Transpose.stepN (nativeMachine F incoming) input t
        ((cfg (entry F 0) (PageQuery.queryBank xs word ⟨[],FamilySelector.outputStream F xs⟩) ⟨pre,[]⟩ pos).denote
          (nativeEncoding F) (program F incoming) ip outRev)=
        some ((cfg .done (PageQuery.queryBank xs word ⟨[],FamilySelector.outputStream F xs⟩)
          ⟨(symbols (row F xs incoming v)).reverse++pre,[]⟩ (advance pos (2*rationalPageCount F))).denote
          (nativeEncoding F) (program F incoming) ip outRev) ∧
      Transpose.step (nativeMachine F incoming) input
        ((cfg .done (PageQuery.queryBank xs word ⟨[],FamilySelector.outputStream F xs⟩)
          ⟨(symbols (row F xs incoming v)).reverse++pre,[]⟩ (advance pos (2*rationalPageCount F))).denote
          (nativeEncoding F) (program F incoming) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace F incoming xs word v hq hw pre pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN _ _ input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff _ _ input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (F : Fin (r+1) → RationalMobius) (incoming : Bool) (ports : Fin 8 ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F incoming pc≠.halt → program F incoming pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F incoming pc))
    (xs word : List Bool) (v : Fin (Counter.value xs)) (hq : BinaryCompare.value word=v.val)
    (hw : word.length=2*xs.length+FamilyNormalization.common F) (pre : List (Sym Bool)) (pos : Fin 8 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget F xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (entry F 0) (PageQuery.queryBank xs word ⟨[],FamilySelector.outputStream F xs⟩) ⟨pre,[]⟩ pos)
          outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (PageQuery.queryBank xs word ⟨[],FamilySelector.outputStream F xs⟩)
            ⟨(symbols (row F xs incoming v)).reverse++pre,[]⟩ (advance pos (2*rationalPageCount F)))
          outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace F incoming xs word v hq hw pre pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels _ target outerFrame input ip outRev hc htr⟩

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃
    (Σ p:Page F,QueryLabel F p) ⊕ (Page F × Bool × Bool) ⊕ Page F ⊕ Unit where
  toFun
    | .query p pc => .inl ⟨p,pc⟩
    | .write p a b => .inr (.inl (p,a,b))
    | .advance p => .inr (.inr (.inl p))
    | .done => .inr (.inr (.inr ()))
  invFun
    | .inl ⟨p,pc⟩ => .query p pc
    | .inr (.inl (p,a,b)) => .write p a b
    | .inr (.inr (.inl p)) => .advance p
    | .inr (.inr (.inr _)) => .done
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (⟨p,pc⟩|⟨p,a,b⟩|p|⟨⟩) <;> rfl

theorem label_card (F : Fin (r+1) → RationalMobius) :
    Fintype.card (Label F)=(∑ p:Page F,Fintype.card (QueryLabel F p))+5*rationalPageCount F+1 := by
  rw [Fintype.card_congr (labelEquiv F)]
  simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Fintype.card_unit]
  ring

theorem fixed_resources (F : Fin (r+1) → RationalMobius) (incoming : Bool) :
    (nativeMachine F incoming).k=8 ∧ (nativeMachine F incoming).g+1=5 ∧
    (nativeMachine F incoming).q+1=(∑ p:Page F,Fintype.card (QueryLabel F p))+5*rationalPageCount F+1 ∧
    (nativeEncoding F).label (entry F 0)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label F)-1+1=_
  rw [label_card];omega

end TransposeFollowup.PageLoop


/-! Exact interfaces exposed by the raw-input seed to the future outer
scheduler. These equalities identify stored data; the preceding run pays
its construction. The vertex traversal itself is not implemented here. -/
namespace TransposeFollowup.SchedulerSeed
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def vertexWord (F : Fin (r+1) → RationalMobius) (xs : List Bool) :=
  ArithmeticSeed.zeros (2*xs.length+FamilyNormalization.common F)
def pagePort : Fin 8 → Port :=
  ![.enumeration .source,RawEnumeration.sharedPort (.work 2),CanonicalReader.output,
    RawEnumeration.sharedPort (.work 3),RawEnumeration.sharedPort (.out 0),seedPort .zeroA,
    RawEnumeration.sharedPort (.out 1),RawEnumeration.sharedPort (.out 2)]
def pageBinding : FinitePortBinding (Fin 8) Port where
  ports:=⟨pagePort,by decide +kernel⟩
  decode:=fun p => if p=pagePort 0 then some 0 else if p=pagePort 1 then some 1 else if p=pagePort 2 then some 2 else
    if p=pagePort 3 then some 3 else if p=pagePort 4 then some 4 else if p=pagePort 5 then some 5 else
    if p=pagePort 6 then some 6 else if p=pagePort 7 then some 7 else none
  decode_spec:=by decide +kernel

theorem ready_seed (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (p : ArithmeticSeed.Port) :
    readyBank F w xs (seedPort p)=(ArithmeticSeed.ready (FamilyNormalization.common F) xs).tapes p :=
  seedBinding.values_at _ _ p
theorem ready_payload (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    readyBank F w xs .payload=Counter.marked w := rfl
theorem ready_raw (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    readyBank F w xs RawSelector.rawOutput=⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ := rfl
theorem ready_normalized (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    readyBank F w xs RawSelector.normalizedOutput=⟨[],FamilyNormalization.outputStream F xs⟩ := rfl
theorem ready_canonical (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    readyBank F w xs CanonicalReader.output=⟨[],FamilySelector.outputStream F xs⟩ := rfl
theorem vertex_length (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    (vertexWord F xs).length=2*xs.length+FamilyNormalization.common F := by simp [vertexWord,ArithmeticSeed.zeros]
theorem vertex_value (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    BinaryCompare.value (vertexWord F xs)=0 := by
  rw [← NativeCounter.word_value]
  exact PaddedWord.value_zeroes _
theorem ready_pages (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    (fun p => readyBank F w xs (pagePort p))=
      PageLoop.bank (PageQuery.queryBank xs (vertexWord F xs) ⟨[],FamilySelector.outputStream F xs⟩) ⟨[],[]⟩ := by
  funext p;fin_cases p <;> rfl

theorem page_positions (F : Fin (r+1) → RationalMobius) (xs : List Bool) (pos : Port → ℤ) (p : Fin 8) :
    CanonicalReader.finalPositions F xs pos (pagePort p)=pos (pagePort p) := by
  have h:pagePort p≠RawSelector.rawOutput:=by fin_cases p <;> decide +kernel
  simp [CanonicalReader.finalPositions,RawSelector.advance,h]

end TransposeFollowup.SchedulerSeed


/-! One fixed controller visits source vertices in increasing order,then
target vertices in decreasing order. All input-dependent indices stay on
tape. A paid erase/copy restores the zero vertex at completion. -/
namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}
abbrev Port := SchedulerSeed.Port
abbrev Bank := SchedulerSeed.Bank
abbrev indexPort := SchedulerSeed.seedPort .zeroA
abbrev outputPort := SchedulerSeed.pagePort 7
abbrev pageBinding := SchedulerSeed.pageBinding

def compareBinding : FinitePortBinding (Fin 2) Port where
  ports:=⟨![indexPort,SchedulerSeed.seedPort .number],by decide +kernel⟩
  decode:=fun p => if p=indexPort then some 0 else if p=SchedulerSeed.seedPort .number then some 1 else none
  decode_spec:=by decide +kernel
def singleBinding : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => indexPort,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=indexPort then some 0 else none
  decode_spec:=by decide +kernel
def resetBinding : FinitePortBinding (Fin 2) Port where
  ports:=⟨![SchedulerSeed.seedPort .zeroB,indexPort],by decide +kernel⟩
  decode:=fun p => if p=SchedulerSeed.seedPort .zeroB then some 0 else if p=indexPort then some 1 else none
  decode_spec:=by decide +kernel
def addPort : RepeatedAdd.Port → Port
  | .acc => indexPort
  | .factor => SchedulerSeed.seedPort .one
  | .fuel => SchedulerSeed.seedPort .fuel
  | .scratch => SchedulerSeed.seedPort .left
  | .zero => SchedulerSeed.seedPort .zeroB
def addBinding : FinitePortBinding RepeatedAdd.Port Port where
  ports:=⟨addPort,by decide +kernel⟩
  decode:=fun p => if p=addPort .acc then some .acc else if p=addPort .factor then some .factor else
    if p=addPort .fuel then some .fuel else if p=addPort .scratch then some .scratch else if p=addPort .zero then some .zero else none
  decode_spec:=by decide +kernel

inductive Label (F : Fin (r+1) → RationalMobius)
  | compare (pc : BinaryCompare.Label)
  | pages (incoming : Bool) (pc : PageLoop.Label F)
  | increment (pc : RepeatedAdd.Label)
  | decrement (pc : Microcode.DecrementFamily.Label)
  | erase (pc : NativeErase.Label)
  | reset (pc : NativeMappedCopy.Label)
  | done | reject
  deriving DecidableEq,Fintype
def start (F : Fin (r+1) → RationalMobius) : Label F := .compare (.scan .equal)
def program (F : Fin (r+1) → RationalMobius) : Microcode.Program Port (Label F)
  | .compare (.done .less) => .jump (.pages false (PageLoop.entry F 0))
  | .compare (.done .equal) => .jump (.decrement 0)
  | .compare (.done .greater) => .reject
  | .compare pc => compareBinding.instruction Label.compare (BinaryCompare.program pc)
  | .pages incoming .done => .jump (if incoming then .decrement 0 else .increment (.counter 0))
  | .pages incoming pc => pageBinding.instruction (Label.pages incoming) (PageLoop.program F incoming pc)
  | .increment pc => if pc=.counter 12 then .jump (start F) else addBinding.instruction Label.increment (RepeatedAdd.program pc)
  | .decrement pc => if pc=11 then .jump (.pages true (PageLoop.entry F 0)) else
      if pc=12 then .jump (.erase 2) else singleBinding.instruction Label.decrement (Microcode.DecrementFamily.program pc)
  | .erase pc => if pc=0 then .jump (.reset (.init (.erase 0))) else singleBinding.instruction Label.erase (NativeErase.program pc)
  | .reset pc => if pc=.seal .done then .jump .done else resetBinding.instruction Label.reset (NativeMappedCopy.program id pc)
  | .done => .halt
  | .reject => .reject

theorem compare_code (F : Fin (r+1) → RationalMobius) (pc : BinaryCompare.Label)
    (hh:BinaryCompare.program pc≠.halt) (_:BinaryCompare.program pc≠.reject) :
    program F (.compare pc)=MicrocodeEmbedding.instruction compareBinding.ports Label.compare (BinaryCompare.program pc) := by
  cases pc with
  | done _ => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem pages_code (F : Fin (r+1) → RationalMobius) (incoming : Bool) (pc : PageLoop.Label F)
    (hh:PageLoop.program F incoming pc≠.halt) (_:PageLoop.program F incoming pc≠.reject) :
    program F (.pages incoming pc)=MicrocodeEmbedding.instruction pageBinding.ports (Label.pages incoming) (PageLoop.program F incoming pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem increment_code (F : Fin (r+1) → RationalMobius) (pc : RepeatedAdd.Label)
    (hh:RepeatedAdd.program pc≠.halt) (_:RepeatedAdd.program pc≠.reject) :
    program F (.increment pc)=MicrocodeEmbedding.instruction addBinding.ports Label.increment (RepeatedAdd.program pc) := by
  have h:pc≠.counter 12:=by intro h;subst pc;exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]
theorem decrement_code (F : Fin (r+1) → RationalMobius) (pc : Microcode.DecrementFamily.Label)
    (hh:Microcode.DecrementFamily.program pc≠.halt) (_:Microcode.DecrementFamily.program pc≠.reject) :
    program F (.decrement pc)=MicrocodeEmbedding.instruction singleBinding.ports Label.decrement (Microcode.DecrementFamily.program pc) := by
  have h1:pc≠11:=by intro h;subst pc;exact hh rfl
  have h2:pc≠12:=by intro h;subst pc;exact hh rfl
  simp [program,h1,h2,FinitePortBinding.instruction_eq]
theorem erase_code (F : Fin (r+1) → RationalMobius) (pc : NativeErase.Label)
    (hh:NativeErase.program pc≠.halt) (_:NativeErase.program pc≠.reject) :
    program F (.erase pc)=MicrocodeEmbedding.instruction singleBinding.ports Label.erase (NativeErase.program pc) := by
  have h:pc≠0:=by intro h;subst pc;exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]
theorem reset_code (F : Fin (r+1) → RationalMobius) (pc : NativeMappedCopy.Label)
    (hh:NativeMappedCopy.program id pc≠.halt) (_:NativeMappedCopy.program id pc≠.reject) :
    program F (.reset pc)=MicrocodeEmbedding.instruction resetBinding.ports Label.reset (NativeMappedCopy.program id pc) := by
  have h:pc≠.seal .done:=by intro h;subst pc;exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

def bank (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (iw out : Tape Bool) : Bank :=
  Function.update (Function.update (SchedulerSeed.readyBank F w xs) indexPort iw) outputPort out
def ready (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool) (pre : List (Sym Bool)) := bank F w xs (Counter.marked iw) ⟨pre,[]⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩
def advance (pos : Port → ℤ) (m : ℕ) : Port → ℤ := fun p => if p=outputPort then pos p+m else pos p
abbrev Trace (F : Fin (r+1) → RationalMobius) := OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

theorem advance_zero (pos : Port → ℤ) : advance pos 0=pos := by funext p;simp [advance]
theorem advance_add (pos : Port → ℤ) (a b : ℕ) : advance (advance pos a) b=advance pos (a+b) := by
  funext p;by_cases h:p=outputPort <;> simp [advance,h,add_assoc]
theorem seed_ready (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    ready F w xs (SchedulerSeed.vertexWord F xs) []=SchedulerSeed.readyBank F w xs := by
  funext p;fin_cases p <;> rfl

theorem jump_trace (F : Fin (r+1) → RationalMobius) (pc next : Label F) (s : Bank) (pos : Port → ℤ)
    (h:program F pc=.jump next) : Trace F 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.VertexScheduler


namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def width (F : Fin (r+1) → RationalMobius) (xs : List Bool) := 2*xs.length+FamilyNormalization.common F
def dimensionWord (F : Fin (r+1) → RationalMobius) (xs : List Bool) := PaddedWord.word (FamilyNormalization.common F) id xs
def incrementWord (F : Fin (r+1) → RationalMobius) (xs iw : List Bool) :=
  RepeatedAdd.addWord iw (ArithmeticSeed.one (width F xs))
def upFrom (F : Fin (r+1) → RationalMobius) (xs : List Bool) (k count : ℕ) :=
  PrefixMembership.segments (PageLoop.row F xs false) k count
def down (F : Fin (r+1) → RationalMobius) (xs : List Bool) : ℕ → List Bool
  | 0 => []
  | k+1 => if h:k<Counter.value xs then PageLoop.row F xs true ⟨k,h⟩++down F xs k else []
def outputBits (F : Fin (r+1) → RationalMobius) (xs : List Bool) :=
  upFrom F xs 0 (Counter.value xs)++down F xs (Counter.value xs)

theorem width_positive (F : Fin (r+1) → RationalMobius) (xs : List Bool) : 0<width F xs := by
  have h:=RowEnumeration.common_positive (F 0) xs
  rw [PaddedWord.word_length] at h
  have hc:=FamilyNormalization.le_common F 0
  unfold width
  omega
theorem dimension_length (F : Fin (r+1) → RationalMobius) (xs : List Bool) : (dimensionWord F xs).length=width F xs :=
  PaddedWord.word_length _ _ _
theorem dimension_value (F : Fin (r+1) → RationalMobius) (xs : List Bool) : BinaryCompare.value (dimensionWord F xs)=Counter.value xs := by
  rw [← NativeCounter.word_value]
  exact PaddedWord.identity_value _ _
theorem dimension_fits (F : Fin (r+1) → RationalMobius) (xs : List Bool) : Counter.value xs<2^width F xs := by
  simpa only [dimension_length,dimension_value] using BinaryCarry.value_lt (dimensionWord F xs)
theorem increment_length (F : Fin (r+1) → RationalMobius) (xs iw : List Bool) (hl:iw.length=width F xs) :
    (incrementWord F xs iw).length=width F xs := by
  have hu:=ArithmeticSeed.one_length (width F xs) (width_positive F xs)
  exact (RepeatedAdd.addWord_length _ _ (hl.trans hu.symm)).trans hu
theorem increment_value (F : Fin (r+1) → RationalMobius) (xs iw : List Bool) (hl:iw.length=width F xs)
    (hi:BinaryCompare.value iw<Counter.value xs) : BinaryCompare.value (incrementWord F xs iw)=BinaryCompare.value iw+1 := by
  have hu:=ArithmeticSeed.one_length (width F xs) (width_positive F xs)
  unfold incrementWord
  rw [RepeatedAdd.addWord_value _ _ (hl.trans hu.symm),← NativeCounter.word_value (ArithmeticSeed.one _),ArithmeticSeed.one_value,hu]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) (dimension_fits F xs))

theorem counter_cost (iw : List Bool) : 2*Counter.stepCost iw≤4*iw.length+4 := by
  have hz : Counter.trailingZeros iw ≤ iw.length := by
    induction iw with
    | nil => simp [Counter.trailingZeros]
    | cons b iw ih => cases b <;> simp [Counter.trailingZeros];omega
  unfold Counter.stepCost
  omega
theorem upFrom_length (F : Fin (r+1) → RationalMobius) (xs : List Bool) (count k : ℕ)
    (hk:k+count≤Counter.value xs) : (upFrom F xs k count).length=count*(2*rationalPageCount F) := by
  induction count generalizing k with
  | zero => simp [upFrom,PrefixMembership.segments]
  | succ count ih =>
    have h:k<Counter.value xs:=by omega
    simp only [upFrom,PrefixMembership.segments,h,↓reduceDIte,List.length_append,PageLoop.row_length]
    have hi:=ih (k+1) (by omega)
    dsimp only [upFrom] at hi
    nlinarith
theorem down_length (F : Fin (r+1) → RationalMobius) (xs : List Bool) (count : ℕ)
    (hc:count≤Counter.value xs) : (down F xs count).length=count*(2*rationalPageCount F) := by
  induction count with
  | zero => simp [down]
  | succ count ih =>
    have h:count<Counter.value xs:=by omega
    simp only [down,h,↓reduceDIte,List.length_append,PageLoop.row_length]
    have hi:=ih (by omega)
    nlinarith
theorem output_length (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    (outputBits F xs).length=4*Counter.value xs*rationalPageCount F := by
  rw [outputBits,List.length_append,upFrom_length F xs _ _ (by omega),down_length F xs _ le_rfl]
  ring

end TransposeFollowup.VertexScheduler


/-! The actual traversal's bit string is exactly the injective encoding
of the existing geometric opcode tape,including its reversed target half. -/
namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler
set_option autoImplicit false
variable {r : ℕ}

def rowAt (F : Fin (r+1) → RationalMobius) (xs : List Bool) (u : Fin (2*Counter.value xs)) :=
  ((rationalOpcodeTable F (Counter.value xs)).get u).toList.flatMap PageLoop.opcodeBits

theorem reverse_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).reverse=List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_reverse,List.length_ofFn,List.getElem_ofFn]
  congr 1
  apply Fin.ext
  simp only [Fin.rev]
  omega

theorem vertex_order (n : ℕ) :
    List.ofFn (fun i:Fin n => OrderedBipartite.left i)++
      List.ofFn (fun i:Fin n => OrderedBipartite.right i.rev)=List.finRange (2*n) := by
  apply List.ext_getElem (by simp;omega)
  intro i hi hi'
  have hilt:i<2*n:=by simpa using hi'
  rw [List.getElem_append]
  simp only [List.length_ofFn]
  split <;> rename_i h
  · apply Fin.ext
    simp [OrderedBipartite.left]
  · apply Fin.ext
    simp [OrderedBipartite.right,Fin.rev]
    omega

theorem down_ofFn (F : Fin (r+1) → RationalMobius) (xs : List Bool) (count : ℕ) (hc:count≤Counter.value xs) :
    down F xs count=(List.ofFn (fun i:Fin count => PageLoop.row F xs true ⟨i.val,lt_of_lt_of_le i.isLt hc⟩)).reverse.flatten := by
  induction count with
  | zero => simp [down]
  | succ count ih =>
    have h:count<Counter.value xs:=by omega
    rw [down,dite_eq_left h,List.ofFn_succ_last,List.reverse_append,List.reverse_singleton,List.flatten_append]
    simp only [List.flatten_singleton,Fin.val_last,Fin.val_castSucc]
    rw [ih (by omega)]

theorem up_order (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    upFrom F xs 0 (Counter.value xs)=(List.ofFn (fun i:Fin (Counter.value xs) => OrderedBipartite.left i)).flatMap (rowAt F xs) := by
  rw [upFrom,PrefixMembership.segments_ofFn _ _ _ (by omega),List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simpa only [rowAt,Function.comp_apply,Nat.zero_add,Bool.false_eq_true,ite_false] using PageLoop.row_eq_table F xs false i

theorem down_order (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    down F xs (Counter.value xs)=(List.ofFn (fun i:Fin (Counter.value xs) => OrderedBipartite.right i.rev)).flatMap (rowAt F xs) := by
  rw [down_ofFn F xs _ le_rfl,reverse_ofFn,List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simpa only [rowAt,Function.comp_apply,ite_true] using PageLoop.row_eq_table F xs true i.rev

theorem encoded_tape (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    (rationalOpcodeTape F (Counter.value xs)).flatMap PageLoop.opcodeBits=
      (List.finRange (2*Counter.value xs)).flatMap (rowAt F xs) := by
  unfold rowAt rationalOpcodeTape rationalOpcodeTable
  simp only [List.Vector.toList_ofFn,List.Vector.get_ofFn,List.flatten_eq_flatMap,
    List.flatMap_assoc,List.flatMap_map,List.ofFn_eq_map,Function.comp_def,List.map_map,id_eq]

theorem output_spec (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    outputBits F xs=(rationalOpcodeTape F (Counter.value xs)).flatMap PageLoop.opcodeBits := by
  rw [outputBits,up_order,down_order,← List.flatMap_append,vertex_order,encoded_tape]

end TransposeFollowup.VertexScheduler


namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem embed_pages (F : Fin (r+1) → RationalMobius) (incoming : Bool) (pc : PageLoop.Label F)
    (w xs iw base : List Bool) (out : Tape Bool) (pre : List (Sym Bool)) (ppos : Fin 8 → ℤ) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed pageBinding.ports (Label.pages incoming)
      (PageLoop.cfg pc (PageQuery.queryBank xs iw ⟨[],FamilySelector.outputStream F xs⟩) out ppos)
      (frame (ready F w xs base pre) pos)=
      cfg (.pages incoming pc) (bank F w xs (Counter.marked iw) out) (pageBinding.values ppos pos) := by
  unfold MicrocodeEmbedding.embed PageLoop.cfg cfg frame
  simp only [← pageBinding.values_eq_extend]
  congr 2
  funext p;fin_cases p <;> rfl

theorem page_final_positions (pos : Port → ℤ) (m : ℕ) :
    pageBinding.values (PageLoop.advance (fun p => pos (pageBinding.ports p)) m) pos=advance pos m := by
  funext p
  rw [pageBinding.values_eq_extend]
  by_cases hp:∃ j,pageBinding.ports j=p
  · obtain ⟨j,rfl⟩:=hp
    rw [MicrocodeEmbedding.extend_at]
    have ho:pageBinding.ports j=outputPort ↔ j=7:=by
      change pageBinding.ports j=pageBinding.ports (7 : Fin 8) ↔ j=7
      exact pageBinding.ports.injective.eq_iff
    simp only [PageLoop.advance,advance,ho]
  · rw [MicrocodeEmbedding.extend_outside _ _ hp]
    have ho:p≠outputPort:=by intro h;exact hp ⟨7,h.symm⟩
    simp [advance,ho]

theorem pages_call (F : Fin (r+1) → RationalMobius) (incoming : Bool)
    (w xs iw : List Bool) (v : Fin (Counter.value xs)) (hv:BinaryCompare.value iw=v.val)
    (hl:iw.length=width F xs) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ PageLoop.budget F xs,Trace F t
      (cfg (.pages incoming (PageLoop.entry F 0)) (ready F w xs iw pre) pos)
      (cfg (.pages incoming .done) (ready F w xs iw ((symbols (PageLoop.row F xs incoming v)).reverse++pre))
        (advance pos (2*rationalPageCount F))) := by
  obtain ⟨t,ht,htr⟩:=PageLoop.complete_trace F incoming xs iw v hv hl pre (fun p => pos (pageBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed pageBinding.ports (Label.pages incoming) (PageLoop.program F incoming)
    (program F) (frame (ready F w xs iw pre) pos) (pages_code F incoming) htr
  simp only [embed_pages,FinitePortBinding.values_project,page_final_positions] at he
  exact ⟨t,ht,by simpa only [ready] using he⟩

end TransposeFollowup.VertexScheduler


namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem embed_compare (F : Fin (r+1) → RationalMobius) (pc : BinaryCompare.Label)
    (w xs iw : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed compareBinding.ports (Label.compare (F:=F))
      (BinaryCompare.cfg pc (BinaryCompare.marked iw) (BinaryCompare.marked (dimensionWord F xs))
        (fun p => pos (compareBinding.ports p))).denote (frame (ready F w xs iw pre) pos)=
      cfg (.compare pc) (ready F w xs iw pre) pos := by
  unfold MicrocodeEmbedding.embed BinaryCompare.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← compareBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_increment (F : Fin (r+1) → RationalMobius) (pc : RepeatedAdd.Label)
    (w xs iw base : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed addBinding.ports (Label.increment (F:=F))
      (RepeatedAdd.cfg pc (RepeatedAdd.ready [true] iw (ArithmeticSeed.one (width F xs)))
        (fun p => pos (addPort p))) (frame (ready F w xs base pre) pos)=
      cfg (.increment pc) (ready F w xs iw pre) pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← addBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p
  all_goals try rfl
  all_goals simp only [RepeatedAdd.ready,RepeatedAdd.Bank.tapes,ArithmeticSeed.one_length _ (width_positive F xs)]
  all_goals rfl

theorem embed_decrement (F : Fin (r+1) → RationalMobius) (pc : Microcode.DecrementFamily.Label)
    (w xs iw base : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed singleBinding.ports (Label.decrement (F:=F))
      (NativeCounter.cfg pc iw (fun _ => pos indexPort)).denote (frame (ready F w xs base pre) pos)=
      cfg (.decrement pc) (ready F w xs iw pre) pos := by
  unfold MicrocodeEmbedding.embed NativeCounter.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← singleBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem compare_call (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool) (hl:iw.length=width F xs)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 5*width F xs+6,Trace F t
      (cfg (start F) (ready F w xs iw pre) pos)
      (cfg (.compare (.done (BinaryCompare.numeric .equal (BinaryCompare.value iw) (Counter.value xs)))) (ready F w xs iw pre) pos) := by
  obtain ⟨t,ht,htr⟩:=BinaryCompare.comparison_trace iw (dimensionWord F xs) (hl.trans (dimension_length F xs).symm)
    (fun p => pos (compareBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed compareBinding.ports (Label.compare (F:=F)) BinaryCompare.program
    (program F) (frame (ready F w xs iw pre) pos) (compare_code F) htr
  exact ⟨t,by simpa only [hl] using ht,by simpa only [embed_compare,start,dimension_value] using he⟩

theorem increment_call (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool) (hl:iw.length=width F xs)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 18*width F xs+51,Trace F t
      (cfg (.increment (.counter 0)) (ready F w xs iw pre) pos)
      (cfg (.increment (.counter 12)) (ready F w xs (incrementWord F xs iw) pre) pos) := by
  have hu:=ArithmeticSeed.one_length (width F xs) (width_positive F xs)
  obtain ⟨t,ht,htr⟩:=RepeatedAdd.single_add_trace iw (ArithmeticSeed.one (width F xs)) (hl.trans hu.symm) (fun p => pos (addPort p))
  have he:=MicrocodeEmbedding.trace_embed addBinding.ports (Label.increment (F:=F)) RepeatedAdd.program
    (program F) (frame (ready F w xs iw pre) pos) (increment_code F) htr
  exact ⟨t,by simpa only [hu] using ht,by simpa only [embed_increment,incrementWord] using he⟩

theorem decrement_call (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool) (hl:iw.length=width F xs)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 4*width F xs+4,Trace F t
      (cfg (.decrement 0) (ready F w xs iw pre) pos)
      (cfg (.decrement (NativeCounter.returnLabel iw)) (ready F w xs (Counter.decrement iw) pre) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeCounter.decrement_trace iw (fun _ => pos indexPort)
  have he:=MicrocodeEmbedding.trace_embed singleBinding.ports (Label.decrement (F:=F)) Microcode.DecrementFamily.program
    (program F) (frame (ready F w xs iw pre) pos) (decrement_code F) htr
  exact ⟨t,by have hc:=counter_cost iw;omega,by simpa only [embed_decrement] using he⟩

end TransposeFollowup.VertexScheduler


namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem embed_erase (F : Fin (r+1) → RationalMobius) (pc : NativeErase.Label)
    (w xs : List Bool) (iw : Tape Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed singleBinding.ports (Label.erase (F:=F))
      (NativeErase.cfg pc iw (fun _ => pos indexPort)).denote (frame (ready F w xs [] pre) pos)=
      cfg (.erase pc) (bank F w xs iw ⟨pre,[]⟩) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← singleBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_reset (F : Fin (r+1) → RationalMobius) (pc : NativeMappedCopy.Label)
    (w xs : List Bool) (iw : Tape Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed resetBinding.ports (Label.reset (F:=F))
      (NativeMappedCopy.cfg pc (Counter.marked (SchedulerSeed.vertexWord F xs)) iw
        (fun p => pos (resetBinding.ports p))) (frame (ready F w xs [] pre) pos)=
      cfg (.reset pc) (bank F w xs iw ⟨pre,[]⟩) pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg cfg frame
  simp only [← resetBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem erase_call (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 4*iw.length+4,Trace F t (cfg (.erase 2) (ready F w xs iw pre) pos)
      (cfg (.erase 0) (bank F w xs ⟨[],[]⟩ ⟨pre,[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeErase.erase_trace iw (fun _ => pos indexPort)
  have he:=MicrocodeEmbedding.trace_embed singleBinding.ports (Label.erase (F:=F)) NativeErase.program
    (program F) (frame (ready F w xs [] pre) pos) (erase_code F) htr
  simp only [embed_erase] at he
  exact ⟨t,ht,by simpa only [ready] using he⟩

theorem reset_call (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 6*width F xs+14,Trace F t
      (cfg (.reset (.init (.erase 0))) (bank F w xs ⟨[],[]⟩ ⟨pre,[]⟩) pos)
      (cfg (.reset (.seal .done)) (ready F w xs (SchedulerSeed.vertexWord F xs) pre) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeMappedCopy.copy_trace id (SchedulerSeed.vertexWord F xs) (fun p => pos (resetBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed resetBinding.ports (Label.reset (F:=F)) (NativeMappedCopy.program id)
    (program F) (frame (ready F w xs [] pre) pos) (reset_code F) htr
  simp only [List.map_id,embed_reset] at he
  exact ⟨t,by simpa only [SchedulerSeed.vertex_length,width] using ht,by simpa only [ready] using he⟩

theorem finish_trace (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool) (hl:iw.length=width F xs)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 10*width F xs+21,Trace F t
      (cfg (.decrement 12) (ready F w xs iw pre) pos)
      (cfg .done (ready F w xs (SchedulerSeed.vertexWord F xs) pre) pos) := by
  have j0:=jump_trace F (.decrement 12) (.erase 2) (ready F w xs iw pre) pos rfl
  obtain ⟨a,ha,ta⟩:=erase_call F w xs iw pre pos
  have ja:=jump_trace F (.erase 0) (.reset (.init (.erase 0))) (bank F w xs ⟨[],[]⟩ ⟨pre,[]⟩) pos rfl
  obtain ⟨b,hb,tb⟩:=reset_call F w xs pre pos
  have jb:=jump_trace F (.reset (.seal .done)) .done (ready F w xs (SchedulerSeed.vertexWord F xs) pre) pos rfl
  exact ⟨1+a+1+b+1,by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans j0 ta) ja) tb) jb⟩

end TransposeFollowup.VertexScheduler


namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {r : ℕ}

def downBudget (F : Fin (r+1) → RationalMobius) (xs : List Bool) (count : ℕ) :=
  count*(PageLoop.budget F xs+4*width F xs+6)+14*width F xs+25

theorem down_terminal (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool) (hl:iw.length=width F xs)
    (hv:BinaryCompare.value iw=0) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 14*width F xs+25,Trace F t
      (cfg (.decrement 0) (ready F w xs iw pre) pos)
      (cfg .done (ready F w xs (SchedulerSeed.vertexWord F xs) pre) pos) := by
  have hz:Counter.isZero iw=true:=(NativeCounter.zero_iff iw).mpr hv
  obtain ⟨a,ha,ta⟩:=decrement_call F w xs iw hl pre pos
  simp only [NativeCounter.returnLabel,hz,ite_true] at ta
  obtain ⟨b,hb,tb⟩:=finish_trace F w xs (Counter.decrement iw) ((Counter.length_decrement iw).trans hl) pre pos
  exact ⟨a+b,by omega,trace_trans ta tb⟩

theorem down_body (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool) (hl:iw.length=width F xs)
    (v : Fin (Counter.value xs)) (hv:BinaryCompare.value iw=v.val+1)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ PageLoop.budget F xs+4*width F xs+6,Trace F t
      (cfg (.decrement 0) (ready F w xs iw pre) pos)
      (cfg (.decrement 0) (ready F w xs (Counter.decrement iw) ((symbols (PageLoop.row F xs true v)).reverse++pre))
        (advance pos (2*rationalPageCount F))) := by
  have hz:Counter.isZero iw=false:=by
    cases h:Counter.isZero iw with
    | false => rfl
    | true => have he:=(NativeCounter.zero_iff iw).mp h;omega
  have hd:BinaryCompare.value (Counter.decrement iw)=v.val:=by
    have h:=NativeCounter.decrement_value iw hz;omega
  obtain ⟨a,ha,ta⟩:=decrement_call F w xs iw hl pre pos
  simp only [NativeCounter.returnLabel,hz] at ta
  have ja:=jump_trace F (.decrement 11) (.pages true (PageLoop.entry F 0)) (ready F w xs (Counter.decrement iw) pre) pos rfl
  obtain ⟨b,hb,tb⟩:=pages_call F true w xs (Counter.decrement iw) v hd ((Counter.length_decrement iw).trans hl) pre pos
  have jb:=jump_trace F (.pages true .done) (.decrement 0)
    (ready F w xs (Counter.decrement iw) ((symbols (PageLoop.row F xs true v)).reverse++pre)) (advance pos (2*rationalPageCount F)) rfl
  exact ⟨a+1+b+1,by omega,trace_trans (trace_trans (trace_trans ta ja) tb) jb⟩

theorem down_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (count : ℕ) (hc:count≤Counter.value xs)
    (iw : List Bool) (hl:iw.length=width F xs) (hv:BinaryCompare.value iw=count)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ downBudget F xs count,Trace F t
      (cfg (.decrement 0) (ready F w xs iw pre) pos)
      (cfg .done (ready F w xs (SchedulerSeed.vertexWord F xs) ((symbols (down F xs count)).reverse++pre))
        (advance pos (count*(2*rationalPageCount F)))) := by
  induction count generalizing iw pre pos with
  | zero =>
    simpa only [downBudget,Nat.zero_mul,Nat.zero_add,down,symbols,List.map_nil,List.reverse_nil,List.nil_append,advance_zero]
      using down_terminal F w xs iw hl hv pre pos
  | succ count ih =>
    have h:count<Counter.value xs:=by omega
    let v:Fin (Counter.value xs):=⟨count,h⟩
    have hz:Counter.isZero iw=false:=by
      cases hh:Counter.isZero iw with
      | false => rfl
      | true => have he:=(NativeCounter.zero_iff iw).mp hh;omega
    have hd:BinaryCompare.value (Counter.decrement iw)=count:=by
      have he:=NativeCounter.decrement_value iw hz;omega
    obtain ⟨a,ha,ta⟩:=down_body F w xs iw hl v hv pre pos
    obtain ⟨b,hb,tb⟩:=ih (by omega) (Counter.decrement iw) ((Counter.length_decrement iw).trans hl) hd
      ((symbols (PageLoop.row F xs true v)).reverse++pre) (advance pos (2*rationalPageCount F))
    refine ⟨a+b,?_,?_⟩
    · unfold downBudget at hb ⊢;nlinarith
    · have hm:2*rationalPageCount F+count*(2*rationalPageCount F)=(count+1)*(2*rationalPageCount F):=by ring
      simpa only [down,h,↓reduceDIte,symbols,List.map_append,List.reverse_append,List.append_assoc,advance_add,hm]
        using trace_trans ta tb

end TransposeFollowup.VertexScheduler


namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {r : ℕ}

def upBudget (F : Fin (r+1) → RationalMobius) (xs : List Bool) (count : ℕ) :=
  count*(PageLoop.budget F xs+23*width F xs+60)+5*width F xs+7+downBudget F xs (Counter.value xs)
def budget (F : Fin (r+1) → RationalMobius) (xs : List Bool) := upBudget F xs (Counter.value xs)

theorem up_body (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool) (hl:iw.length=width F xs)
    (v : Fin (Counter.value xs)) (hv:BinaryCompare.value iw=v.val)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ PageLoop.budget F xs+23*width F xs+60,Trace F t
      (cfg (start F) (ready F w xs iw pre) pos)
      (cfg (start F) (ready F w xs (incrementWord F xs iw) ((symbols (PageLoop.row F xs false v)).reverse++pre))
        (advance pos (2*rationalPageCount F))) := by
  obtain ⟨a,ha,ta⟩:=compare_call F w xs iw hl pre pos
  simp only [hv,BinaryCompare.numeric,v.isLt,ite_true] at ta
  have ja:=jump_trace F (.compare (.done .less)) (.pages false (PageLoop.entry F 0)) (ready F w xs iw pre) pos rfl
  obtain ⟨b,hb,tb⟩:=pages_call F false w xs iw v hv hl pre pos
  let afterPre:=(symbols (PageLoop.row F xs false v)).reverse++pre
  let afterPos:=advance pos (2*rationalPageCount F)
  have jb:=jump_trace F (.pages false .done) (.increment (.counter 0)) (ready F w xs iw afterPre) afterPos rfl
  obtain ⟨c,hc,tc⟩:=increment_call F w xs iw hl afterPre afterPos
  have jc:=jump_trace F (.increment (.counter 12)) (start F) (ready F w xs (incrementWord F xs iw) afterPre) afterPos rfl
  exact ⟨a+1+b+1+c+1,by omega,trace_trans (trace_trans (trace_trans (trace_trans (trace_trans ta ja) tb) jb) tc) jc⟩

theorem up_terminal (F : Fin (r+1) → RationalMobius) (w xs iw : List Bool) (hl:iw.length=width F xs)
    (hv:BinaryCompare.value iw=Counter.value xs) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 5*width F xs+7+downBudget F xs (Counter.value xs),Trace F t
      (cfg (start F) (ready F w xs iw pre) pos)
      (cfg .done (ready F w xs (SchedulerSeed.vertexWord F xs) ((symbols (down F xs (Counter.value xs))).reverse++pre))
        (advance pos (Counter.value xs*(2*rationalPageCount F)))) := by
  obtain ⟨a,ha,ta⟩:=compare_call F w xs iw hl pre pos
  simp only [hv,BinaryCompare.numeric,Nat.lt_irrefl,ite_false] at ta
  have ja:=jump_trace F (.compare (.done .equal)) (.decrement 0) (ready F w xs iw pre) pos rfl
  obtain ⟨b,hb,tb⟩:=down_trace F w xs (Counter.value xs) le_rfl iw hl hv pre pos
  exact ⟨a+1+b,by omega,trace_trans (trace_trans ta ja) tb⟩

theorem up_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (count k : ℕ) (hk:k+count=Counter.value xs)
    (iw : List Bool) (hl:iw.length=width F xs) (hv:BinaryCompare.value iw=k)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ upBudget F xs count,Trace F t
      (cfg (start F) (ready F w xs iw pre) pos)
      (cfg .done (ready F w xs (SchedulerSeed.vertexWord F xs)
        ((symbols (upFrom F xs k count++down F xs (Counter.value xs))).reverse++pre))
        (advance pos ((count+Counter.value xs)*(2*rationalPageCount F)))) := by
  induction count generalizing k iw pre pos with
  | zero =>
    have hv':BinaryCompare.value iw=Counter.value xs:=by omega
    simpa only [upBudget,Nat.zero_mul,Nat.zero_add,upFrom,PrefixMembership.segments,List.nil_append]
      using up_terminal F w xs iw hl hv' pre pos
  | succ count ih =>
    have h:k<Counter.value xs:=by omega
    let v:Fin (Counter.value xs):=⟨k,h⟩
    obtain ⟨a,ha,ta⟩:=up_body F w xs iw hl v hv pre pos
    have hv':BinaryCompare.value (incrementWord F xs iw)=k+1:=by
      rw [increment_value F xs iw hl (by omega),hv]
    obtain ⟨b,hb,tb⟩:=ih (k+1) (by omega) (incrementWord F xs iw) (increment_length F xs iw hl) hv'
      ((symbols (PageLoop.row F xs false v)).reverse++pre) (advance pos (2*rationalPageCount F))
    refine ⟨a+b,?_,?_⟩
    · unfold upBudget at hb ⊢;nlinarith
    · have hm:2*rationalPageCount F+(count+Counter.value xs)*(2*rationalPageCount F)=
          (count+1+Counter.value xs)*(2*rationalPageCount F):=by ring
      simpa only [upFrom,PrefixMembership.segments,h,↓reduceDIte,List.append_assoc,symbols,List.map_append,
        List.reverse_append,advance_add,hm] using trace_trans ta tb

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ budget F xs,Trace F t
      (cfg (start F) (ready F w xs (SchedulerSeed.vertexWord F xs) pre) pos)
      (cfg .done (ready F w xs (SchedulerSeed.vertexWord F xs) ((symbols (outputBits F xs)).reverse++pre))
        (advance pos (4*Counter.value xs*rationalPageCount F))) := by
  have hm:(Counter.value xs+Counter.value xs)*(2*rationalPageCount F)=4*Counter.value xs*rationalPageCount F:=by ring
  simpa only [hm,outputBits,budget] using up_trace F w xs (Counter.value xs) 0 (by omega) (SchedulerSeed.vertexWord F xs)
    (SchedulerSeed.vertex_length F xs) (SchedulerSeed.vertex_value F xs) pre pos

end TransposeFollowup.VertexScheduler


namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler
set_option autoImplicit false
variable {r : ℕ}

theorem budget_eq (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    budget F xs=2*Counter.value xs*PageLoop.budget F xs+
      Counter.value xs*(27*width F xs+66)+19*width F xs+32 := by
  unfold budget upBudget downBudget
  ring
def coefficient (F : Fin (r+1) → RationalMobius) :=
  PageLoop.allVerticesCoefficient F+46*FamilyNormalization.common F+374

theorem budget_linear (F : Fin (r+1) → RationalMobius) (xs : List Bool)
    (hn:1≤Counter.value xs) (hx:xs.length≤(Counter.value xs+1).size) :
    budget F xs≤coefficient F*Transpose.inputLength (Counter.value xs) := by
  let n:=Counter.value xs
  let C:=FamilyNormalization.common F
  let b:=Transpose.entryBits n
  let P:=Transpose.inputLength n
  have hb:1≤b:=by unfold b Transpose.entryBits;omega
  have hs:=grid_size_bits n
  have hm:width F xs≤(C+6)*b:=by
    unfold width
    have hc:=Nat.mul_le_mul_right (C+4) hb
    dsimp only [C,b,n] at hc hs hb ⊢
    nlinarith
  have hnn:n≤n*n:=by dsimp [n];nlinarith
  have hnb:n*b≤P:=Nat.mul_le_mul_right b hnn
  have hnm:n*width F xs≤(C+6)*P:=by
    have h1:=Nat.mul_le_mul_left n hm
    have h2:=Nat.mul_le_mul_left (C+6) hnb
    nlinarith
  have hnP:n≤P:=DimensionCandidate.dimension_le_length n hn
  have hmN:width F xs≤n*width F xs:=by
    have h:=Nat.mul_le_mul_right (width F xs) hn
    simpa only [one_mul] using h
  have hp:=PageLoop.all_vertices_budget F xs hn hx
  rw [budget_eq]
  unfold coefficient
  dsimp only [n,C,P] at hnm hnP hmN
  nlinarith

end TransposeFollowup.VertexScheduler


namespace TransposeFollowup.VertexScheduler
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)

theorem native_complete (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget F xs,
      Transpose.stepN (nativeMachine F) input t
        ((cfg (start F) (ready F w xs (SchedulerSeed.vertexWord F xs) pre) pos).denote (nativeEncoding F) (program F) ip outRev)=
        some ((cfg .done (ready F w xs (SchedulerSeed.vertexWord F xs) ((symbols (outputBits F xs)).reverse++pre))
          (advance pos (4*Counter.value xs*rationalPageCount F))).denote (nativeEncoding F) (program F) ip outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg .done (ready F w xs (SchedulerSeed.vertexWord F xs) ((symbols (outputBits F xs)).reverse++pre))
          (advance pos (4*Counter.value xs*rationalPageCount F))).denote (nativeEncoding F) (program F) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace F w xs pre pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN _ _ input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff _ _ input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (F : Fin (r+1) → RationalMobius) (ports : Port ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc:∀ pc,program F pc≠.halt → program F pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F pc))
    (w xs : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget F xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F) (ready F w xs (SchedulerSeed.vertexWord F xs) pre) pos)
          outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (ready F w xs (SchedulerSeed.vertexWord F xs) ((symbols (outputBits F xs)).reverse++pre))
            (advance pos (4*Counter.value xs*rationalPageCount F))) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace F w xs pre pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels _ target outerFrame input ip outRev hc htr⟩

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃
    BinaryCompare.Label ⊕ (Bool × PageLoop.Label F) ⊕ RepeatedAdd.Label ⊕ Microcode.DecrementFamily.Label ⊕
      NativeErase.Label ⊕ NativeMappedCopy.Label ⊕ Bool where
  toFun
    | .compare pc => .inl pc
    | .pages b pc => .inr (.inl (b,pc))
    | .increment pc => .inr (.inr (.inl pc))
    | .decrement pc => .inr (.inr (.inr (.inl pc)))
    | .erase pc => .inr (.inr (.inr (.inr (.inl pc))))
    | .reset pc => .inr (.inr (.inr (.inr (.inr (.inl pc)))))
    | .done => .inr (.inr (.inr (.inr (.inr (.inr false)))))
    | .reject => .inr (.inr (.inr (.inr (.inr (.inr true)))))
  invFun
    | .inl pc => .compare pc
    | .inr (.inl (b,pc)) => .pages b pc
    | .inr (.inr (.inl pc)) => .increment pc
    | .inr (.inr (.inr (.inl pc))) => .decrement pc
    | .inr (.inr (.inr (.inr (.inl pc)))) => .erase pc
    | .inr (.inr (.inr (.inr (.inr (.inl pc))))) => .reset pc
    | .inr (.inr (.inr (.inr (.inr (.inr false))))) => .done
    | .inr (.inr (.inr (.inr (.inr (.inr true))))) => .reject
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by
    rintro (pc|⟨b,pc⟩|pc|pc|pc|pc|b)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · cases b <;> rfl

theorem label_card (F : Fin (r+1) → RationalMobius) : Fintype.card (Label F)=2*Fintype.card (PageLoop.Label F)+174 := by
  have hc:Fintype.card BinaryCompare.Label=28:=by decide +kernel
  have ha:Fintype.card RepeatedAdd.Label=99:=by decide +kernel
  have hd:Fintype.card Microcode.DecrementFamily.Label=13:=by decide +kernel
  have he:Fintype.card NativeErase.Label=8:=by decide +kernel
  have hr:Fintype.card NativeMappedCopy.Label=24:=by decide +kernel
  rw [Fintype.card_congr (labelEquiv F)]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,hc,ha,hd,he,hr]
  omega
theorem fixed_resources (F : Fin (r+1) → RationalMobius) : (nativeMachine F).k=42 ∧
    (nativeMachine F).g+1=5 ∧ (nativeMachine F).q+1=2*Fintype.card (PageLoop.Label F)+174 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42;decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [label_card];omega

end TransposeFollowup.VertexScheduler


/-! A fixed native program prepares its workspace from raw input and then
emits the complete geometric opcode tape. Its only phase transfer is paid. -/
namespace TransposeFollowup.OpcodeGenerator
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}
abbrev Port := SchedulerSeed.Port
abbrev Bank := SchedulerSeed.Bank

inductive Label (F : Fin (r+1) → RationalMobius)
  | prepare (pc : SchedulerSeed.Label F)
  | schedule (pc : VertexScheduler.Label F)
  deriving DecidableEq,Fintype
def start (F : Fin (r+1) → RationalMobius) : Label F := .prepare (SchedulerSeed.start F)
def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program Port (Label F)
  | .prepare (.seed .done) => .work (.jump (.schedule (VertexScheduler.start F)))
  | .prepare pc => NativeIOEmbedding.boundInstruction FamilyEnumeration.identityBinding Label.prepare (SchedulerSeed.program F pc)
  | .schedule pc => .work (FamilyEnumeration.identityBinding.instruction Label.schedule (VertexScheduler.program F pc))

theorem prepare_code (F : Fin (r+1) → RationalMobius) (pc : SchedulerSeed.Label F)
    (hh:SchedulerSeed.program F pc≠.work .halt) (_:SchedulerSeed.program F pc≠.work .reject) :
    program F (.prepare pc)=NativeIOEmbedding.instruction FamilyEnumeration.identityBinding.ports Label.prepare (SchedulerSeed.program F pc) := by
  cases pc with
  | seed pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
theorem schedule_code (F : Fin (r+1) → RationalMobius) (pc : VertexScheduler.Label F)
    (_:VertexScheduler.program F pc≠.halt) (_:VertexScheduler.program F pc≠.reject) :
    NativeIO.workProgram (program F) (.schedule pc)=MicrocodeEmbedding.instruction FamilyEnumeration.identityBinding.ports Label.schedule
      (VertexScheduler.program F pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) :=
  ⟨workCfg pc s pos,ip,outRev⟩
def finalBank (F : Fin (r+1) → RationalMobius) (w xs : List Bool) : Bank :=
  VertexScheduler.ready F w xs (SchedulerSeed.vertexWord F xs) (symbols (VertexScheduler.outputBits F xs)).reverse
def finalPositions (F : Fin (r+1) → RationalMobius) (xs : List Bool) (pos : Port → ℤ) :=
  VertexScheduler.advance (CanonicalReader.finalPositions F xs pos) (4*Counter.value xs*rationalPageCount F)
abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

theorem embed_prepare (F : Fin (r+1) → RationalMobius) (pc : SchedulerSeed.Label F)
    (s base : Bank) (pos basePos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed FamilyEnumeration.identityBinding.ports (Label.prepare (F:=F)) (SchedulerSeed.cfg pc s pos ip outRev)
      (RawEnumeration.frame base basePos)=cfg (.prepare pc) s pos ip outRev := by
  unfold NativeIOEmbedding.embed SchedulerSeed.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed SchedulerSeed.workCfg workCfg RawEnumeration.frame
  simp only [← FamilyEnumeration.identityBinding.values_eq_extend]
  rfl

theorem embed_schedule (F : Fin (r+1) → RationalMobius) (pc : VertexScheduler.Label F)
    (s base : Bank) (pos basePos : Port → ℤ) :
    MicrocodeEmbedding.embed FamilyEnumeration.identityBinding.ports (Label.schedule (F:=F)) (VertexScheduler.cfg pc s pos)
      (RawEnumeration.frame base basePos)=workCfg (.schedule pc) s pos := by
  unfold MicrocodeEmbedding.embed VertexScheduler.cfg workCfg RawEnumeration.frame
  simp only [← FamilyEnumeration.identityBinding.values_eq_extend]
  rfl

theorem schedule_call (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ VertexScheduler.budget F xs,Trace F w t
      (cfg (.schedule (VertexScheduler.start F)) (SchedulerSeed.readyBank F w xs) pos ip outRev)
      (cfg (.schedule .done) (finalBank F w xs) (VertexScheduler.advance pos (4*Counter.value xs*rationalPageCount F)) ip outRev) := by
  obtain ⟨t,ht,htr⟩:=VertexScheduler.complete_trace F w xs [] pos
  have he:=MicrocodeEmbedding.trace_embed FamilyEnumeration.identityBinding.ports (Label.schedule (F:=F)) (VertexScheduler.program F)
    (NativeIO.workProgram (program F)) (RawEnumeration.frame (SchedulerSeed.readyBank F w xs) pos) (schedule_code F) htr
  exact ⟨t,ht,by simpa only [embed_schedule,VertexScheduler.seed_ready,List.append_nil,finalBank,cfg]
    using NativeIO.lift_work_trace (program F) w ip outRev he⟩

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    Trace F w 1 (cfg (.prepare (.seed .done)) s pos ip outRev)
      (cfg (.schedule (VertexScheduler.start F)) s pos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

end TransposeFollowup.OpcodeGenerator


namespace TransposeFollowup.OpcodeGenerator
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def coefficient (F : Fin (r+1) → RationalMobius) := SchedulerSeed.coefficient F+VertexScheduler.coefficient F+1

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn:1≤n)
    (hw:w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,Trace F w t
      (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.schedule .done) (finalBank F w xs) (finalPositions F xs pos) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩:=SchedulerSeed.complete_trace F w n hn hw pos outRev
  have te:=NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports (Label.prepare (F:=F))
    (SchedulerSeed.program F) (program F) (RawEnumeration.frame (RawEnumeration.initial []) pos) w (prepare_code F) ta
  have te':Trace F w a (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.prepare (.seed .done)) (SchedulerSeed.readyBank F w xs) (CanonicalReader.finalPositions F xs pos) w.length outRev):=by
    simpa only [embed_prepare,start] using te
  have tj:=transfer_trace F w (SchedulerSeed.readyBank F w xs) (CanonicalReader.finalPositions F xs pos) w.length outRev
  obtain ⟨b,hb,tb⟩:=schedule_call F w xs (CanonicalReader.finalPositions F xs pos) w.length outRev
  have hl':xs.length≤(Counter.value xs+1).size:=by rw [hv,hl];exact Nat.size_le_size (by omega)
  have hbudget:=VertexScheduler.budget_linear F xs (by omega) hl'
  rw [hv,← hw] at hbudget
  have h1:1≤w.length:=by rw [hw];exact hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨xs,hx,hv,hl,a+1+b,?_,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans te' tj) tb⟩
  unfold coefficient
  nlinarith

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) := NativeIO.machine (nativeEncoding F) (program F)

theorem native_complete (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn:1≤n)
    (hw:w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (nativeMachine F) w t (Transpose.init (nativeMachine F))=
        some ((cfg (.schedule .done) (finalBank F w xs) (finalPositions F xs (fun _ => 0)) w.length []).denote
          (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w
        ((cfg (.schedule .done) (finalBank F w xs) (finalPositions F xs (fun _ => 0)) w.length []).denote
          (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw (fun _ => 0) []
  refine ⟨xs,hx,hv,hl,t,ht,?_,?_⟩
  · have hi:(cfg (start F) (RawEnumeration.initial []) (fun _ => 0) 0 []).denote (nativeEncoding F) (program F)=
        Transpose.init (nativeMachine F):=by
      rw [RawEnumeration.initial_nil]
      exact NativeIO.blank_denote (nativeEncoding F) (program F) (start F) (NativeMicrocode.initialEncoding_start _)
    rw [← hi]
    exact NativeIO.trace_stepN (nativeEncoding F) (program F) w htr
  · apply (NativeIO.step_none_iff (nativeEncoding F) (program F) w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program,FinitePortBinding.instruction,VertexScheduler.program]

theorem native_call {U J : Type*} {k q : ℕ} (F : Fin (r+1) → RationalMobius) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label F → J) (target : NativeIO.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc:∀ pc,program F pc≠.work .halt → program F pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (program F pc))
    (w : List Bool) (n : ℕ) (hn:1≤n) (hw:w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (NativeIO.machine encoding target) w t
        ((NativeIOEmbedding.embed ports labels (cfg (start F) (RawEnumeration.initial []) pos 0 outRev) outerFrame).denote encoding target)=
        some ((NativeIOEmbedding.embed ports labels
          (cfg (.schedule .done) (finalBank F w xs) (finalPositions F xs pos) w.length outRev) outerFrame).denote encoding target) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw pos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels (program F) target outerFrame w hc htr⟩

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃ SchedulerSeed.Label F ⊕ VertexScheduler.Label F where
  toFun | .prepare pc => .inl pc | .schedule pc => .inr pc
  invFun | .inl pc => .prepare pc | .inr pc => .schedule pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc) <;> rfl

theorem fixed_resources (F : Fin (r+1) → RationalMobius) : (nativeMachine F).k=42 ∧
    (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=Fintype.card (SchedulerSeed.Label F)+2*Fintype.card (PageLoop.Label F)+174 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42;decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F),Fintype.card_sum,VertexScheduler.label_card]
    omega

end TransposeFollowup.OpcodeGenerator


/-! The completed run changes exactly the opcode-output tape of the paid
seed bank. The vertex word is reset; all other stored data and heads survive. -/
namespace TransposeFollowup.OpcodeGenerator
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem final_bank_eq_update (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    finalBank F w xs=Function.update (SchedulerSeed.readyBank F w xs) VertexScheduler.outputPort
      ⟨(symbols ((rationalOpcodeTape F (Counter.value xs)).flatMap PageLoop.opcodeBits)).reverse,[]⟩ := by
  have h:Function.update (SchedulerSeed.readyBank F w xs) VertexScheduler.indexPort
      (Counter.marked (SchedulerSeed.vertexWord F xs))=SchedulerSeed.readyBank F w xs := by
    funext p;fin_cases p <;> rfl
  unfold finalBank VertexScheduler.ready VertexScheduler.bank
  rw [h,VertexScheduler.output_spec]

theorem output_tape (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    finalBank F w xs VertexScheduler.outputPort=
      ⟨(symbols ((rationalOpcodeTape F (Counter.value xs)).flatMap PageLoop.opcodeBits)).reverse,[]⟩ := by
  rw [final_bank_eq_update,Function.update_self]

theorem retained_tapes (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (p : Port) (hp:p≠VertexScheduler.outputPort) :
    finalBank F w xs p=SchedulerSeed.readyBank F w xs p := by
  rw [final_bank_eq_update,Function.update_of_ne hp]

theorem encoded_length (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    ((rationalOpcodeTape F (Counter.value xs)).flatMap PageLoop.opcodeBits).length=4*Counter.value xs*rationalPageCount F := by
  rw [← VertexScheduler.output_spec]
  exact VertexScheduler.output_length F xs

theorem output_head (F : Fin (r+1) → RationalMobius) (xs : List Bool) (pos : Port → ℤ) :
    finalPositions F xs pos VertexScheduler.outputPort=
      pos VertexScheduler.outputPort+(4*Counter.value xs*rationalPageCount F:ℕ) := by
  simp only [finalPositions,VertexScheduler.advance,ite_true]
  rw [SchedulerSeed.page_positions]

theorem retained_heads (F : Fin (r+1) → RationalMobius) (xs : List Bool) (pos : Port → ℤ)
    (p : Port) (hp:p≠VertexScheduler.outputPort) :
    finalPositions F xs pos p=CanonicalReader.finalPositions F xs pos p := by
  simp only [finalPositions,VertexScheduler.advance,hp,ite_false]

end TransposeFollowup.OpcodeGenerator
