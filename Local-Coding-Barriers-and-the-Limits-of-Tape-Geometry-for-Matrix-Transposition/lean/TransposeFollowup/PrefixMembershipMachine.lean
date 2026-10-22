import TransposeFollowup.BatchMembershipRun
import TransposeFollowup.NativePrefixRewind

/-! A fixed finite sequence of batch queries, followed by an actual
rewind. The number of batches is a program parameter; their lengths
and coordinate values are never given to finite control. -/
namespace TransposeFollowup.PrefixMembership
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

inductive Label (small K : ℕ)
  | phase (i : Fin K) (pc : BatchMembership.Label small)
  | rewind (found : Bool) (pc : NativeSpanRewind.Label)
  deriving DecidableEq,Fintype

def identityBinding : FinitePortBinding (Fin 7) (Fin 7) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intro p j;simp [eq_comm]
def rewindBinding : FinitePortBinding (Fin 1) (Fin 7) where
  ports:=⟨fun _ => 2,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=2 then some 0 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
def entry (small K k : ℕ) (found : Bool) : Label small K :=
  if h : k<K then .phase ⟨k,h⟩ (BatchMembership.start small found) else .rewind found .left
def start (small K : ℕ) := entry small K 0 false
def program (small K : ℕ) : Microcode.Program (Fin 7) (Label small K)
  | .phase i (.done found) => .jump (entry small K (i.val+1) found)
  | .phase i pc => identityBinding.instruction (Label.phase i) (BatchMembership.program small pc)
  | .rewind found pc => rewindBinding.instruction (Label.rewind found) (NativeSpanRewind.program pc)

theorem phase_code (small : ℕ) (i : Fin K) (pc : BatchMembership.Label small)
    (hh : BatchMembership.program small pc≠.halt) (_ : BatchMembership.program small pc≠.reject) :
    program small K (.phase i pc)=MicrocodeEmbedding.instruction identityBinding.ports (Label.phase i) (BatchMembership.program small pc) := by
  cases pc with
  | done b => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem rewind_code (small K : ℕ) (found : Bool) (pc : NativeSpanRewind.Label)
    (_ : NativeSpanRewind.program pc≠.halt) (_ : NativeSpanRewind.program pc≠.reject) :
    program small K (.rewind found pc)=MicrocodeEmbedding.instruction rewindBinding.ports (Label.rewind found) (NativeSpanRewind.program pc) := by
  simp only [program,FinitePortBinding.instruction_eq]

def cfg {small K : ℕ} (pc : Label small K) (s : BatchMembership.Bank) (pos : Fin 7 → ℤ) : NativeMicrocode.Config (Fin 7) (Label small K) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
abbrev Trace (small K : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program small K)) (NativeMicrocode.Active (program small K))

theorem embed_phase (small : ℕ) (i : Fin K) (pc : BatchMembership.Label small)
    (s : BatchMembership.Bank) (pos : Fin 7 → ℤ) (frame : MicrocodeEmbedding.Frame (Fin 7)) :
    MicrocodeEmbedding.embed identityBinding.ports (Label.phase i) (BatchMembership.cfg pc s pos) frame=cfg (.phase i pc) s pos := by
  unfold MicrocodeEmbedding.embed BatchMembership.cfg cfg
  simp only [← identityBinding.values_eq_extend]
  rfl

theorem phase_trace (small : ℕ) (i : Fin K) (found : Bool) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ BatchMembership.batchBudget small xs rs+1,Trace small K t
      (cfg (entry small K i.val found) (BatchMembership.queryBank xs a ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos)
      (cfg (entry small K (i.val+1) (found || rs.any (NativePairEqual.samePair a)))
        (BatchMembership.queryBank xs a ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩)
        (BatchMembership.advance pos (NormalizedBatch.inputBatch rs).length)) := by
  obtain ⟨t,ht,htr⟩:=BatchMembership.batch_trace small found xs a ha1 ha2 hp rs hw pre suffix pos
  have he:=MicrocodeEmbedding.trace_embed identityBinding.ports (Label.phase i) (BatchMembership.program small) (program small K)
    (BatchMembership.frame (BatchMembership.queryBank xs a ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos) (phase_code small i) htr
  simp only [embed_phase] at he
  have hi : entry small K i.val found=.phase i (BatchMembership.start small found) := by
    simp only [entry,dite_eq_left i.isLt]
  rw [hi]
  refine ⟨t+1,by omega,NativeCountedLoop.trace_trans he ?_⟩
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,program]
  · exact .refl _

theorem embed_rewind (small K : ℕ) (found : Bool) (pc : NativeSpanRewind.Label)
    (word : Tape Bool) (base : BatchMembership.Bank) (pos : Fin 7 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed rewindBinding.ports (Label.rewind (small:=small) (K:=K) found)
      (NativeSpanRewind.cfg pc word (fun _ => z)).denote (BatchMembership.frame base pos)=
      cfg (.rewind found pc) (Function.update base 2 word) (Function.update pos 2 z) := by
  unfold MicrocodeEmbedding.embed NativeSpanRewind.cfg NativeZipper.Config.denote Microcode.Config.denote cfg BatchMembership.frame
  simp only [← rewindBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl
theorem bank_update (xs : List Bool) (a : List Bool × List Bool) (input word : Tape Bool) :
    Function.update (BatchMembership.queryBank xs a input) 2 word=BatchMembership.queryBank xs a word := by
  funext p;fin_cases p <;> rfl
theorem restored_positions (pos : Fin 7 → ℤ) (m : ℕ) :
    Function.update (BatchMembership.advance pos m) 2 (pos 2)=pos := by
  funext p;fin_cases p <;> simp [BatchMembership.advance]

theorem rewind_call (small K : ℕ) (found : Bool) (xs : List Bool) (a : List Bool × List Bool)
    (pre suffix : List (Sym Bool)) (h : ∀ s ∈ pre,s≠.blank) (pos : Fin 7 → ℤ) :
    ∃ t ≤ 2*pre.length+3,Trace small K t
      (cfg (.rewind found .left) (BatchMembership.queryBank xs a ⟨pre.reverse,suffix⟩) (BatchMembership.advance pos pre.length))
      (cfg (.rewind found .done) (BatchMembership.queryBank xs a ⟨[],pre++suffix⟩) pos) := by
  let adv:=BatchMembership.advance pos pre.length
  obtain ⟨t,ht,htr⟩:=NativePrefixRewind.rewind_trace pre suffix h (fun _ => adv 2)
  have he:=MicrocodeEmbedding.trace_embed rewindBinding.ports (Label.rewind (small:=small) (K:=K) found)
    NativeSpanRewind.program (program small K) (BatchMembership.frame (BatchMembership.queryBank xs a ⟨pre.reverse,suffix⟩) adv)
    (rewind_code small K found) htr
  have hz : adv 2-pre.length=pos 2 := by simp [adv,BatchMembership.advance]
  exact ⟨t,ht,by simpa only [embed_rewind,bank_update,Function.update_eq_self,hz,adv,restored_positions] using he⟩

end TransposeFollowup.PrefixMembership
