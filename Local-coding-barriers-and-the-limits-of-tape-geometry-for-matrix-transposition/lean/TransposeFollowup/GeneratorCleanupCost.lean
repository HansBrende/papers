import TransposeFollowup.OpcodeGeneratorMeaning
import TransposeFollowup.GeneratorRowsPreparedGeometry
import TransposeFollowup.NativeBatchErase
import TransposeFollowup.NativeUnprepare
import TransposeFollowup.NativeSpanEraseInterface

/-! Exact dirty-tape inventory of the 42-tape generator endpoint.
This file identifies data to erase; it performs no implicit erasure. -/
namespace TransposeFollowup.GeneratorCleanup
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}
abbrev Port := OpcodeGenerator.Port
abbrev Bank := OpcodeGenerator.Bank

def markedPorts : Fin 7 ↪ Port where
  toFun:=![.payload,SchedulerSeed.seedPort .source,SchedulerSeed.seedPort .number,
    SchedulerSeed.seedPort .zeroA,SchedulerSeed.seedPort .zeroB,SchedulerSeed.seedPort .one,SchedulerSeed.seedPort .fuel]
  inj':=by decide +kernel

def markerPorts : Fin 2 ↪ Port where
  toFun:=![SchedulerSeed.seedPort .left,SchedulerSeed.seedPort .right]
  inj':=by decide +kernel

def streamPorts : Fin 4 ↪ Port where
  toFun:=![RawSelector.rawOutput,RawSelector.normalizedOutput,CanonicalReader.output,VertexScheduler.outputPort]
  inj':=by decide +kernel

def markedWords (F : Fin (r+1) → RationalMobius) (w xs : List Bool) : Fin 7 → List Bool :=
  ![w,xs,PaddedWord.word (FamilyNormalization.common F) id xs,SchedulerSeed.vertexWord F xs,
    SchedulerSeed.vertexWord F xs,ArithmeticSeed.one (2*xs.length+FamilyNormalization.common F),[true]]

def streams (F : Fin (r+1) → RationalMobius) (xs : List Bool) : Fin 4 → List (Sym Bool) :=
  ![FamilyEnumeration.stream F xs,FamilyNormalization.outputStream F xs,FamilySelector.outputStream F xs,
    symbols (GeneratedRowClock.bits F (Counter.value xs))]

def atEnd (j : Fin 4) : Bool:=j=0 ∨ j=3

def streamTape (j : Fin 4) (xs : List (Sym Bool)) : Tape Bool :=
  if atEnd j then ⟨xs.reverse,[]⟩ else ⟨[],xs⟩

theorem marked_at (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (j : Fin 7) :
    OpcodeGenerator.finalBank F w xs (markedPorts j)=Counter.marked (markedWords F w xs j) := by
  fin_cases j <;> rfl

theorem marker_at (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (j : Fin 2) :
    OpcodeGenerator.finalBank F w xs (markerPorts j)=BinaryCarry.preparedOutput := by
  fin_cases j <;> rfl

theorem stream_at (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (j : Fin 4) :
    OpcodeGenerator.finalBank F w xs (streamPorts j)=streamTape j (streams F xs j) := by
  fin_cases j
  · rfl
  · rfl
  · rfl
  · exact OpcodeGenerator.output_tape F w xs

theorem categories_disjoint :
    (∀ i j,markedPorts i≠markerPorts j) ∧ (∀ i j,markedPorts i≠streamPorts j) ∧
      (∀ i j,markerPorts i≠streamPorts j) := by decide +kernel

theorem outside_blank (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (p : Port)
    (hm : ¬∃ j,markedPorts j=p) (hu : ¬∃ j,markerPorts j=p) (hs : ¬∃ j,streamPorts j=p) :
    OpcodeGenerator.finalBank F w xs p=⟨[],[]⟩ := by
  fin_cases p <;> first | rfl | exact False.elim (hm (by decide +kernel)) |
    exact False.elim (hu (by decide +kernel)) | exact False.elim (hs (by decide +kernel))

end TransposeFollowup.GeneratorCleanup


namespace TransposeFollowup.GeneratorCleanup
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem head_eq (F : Fin (r+1) → RationalMobius) (xs : List Bool) (p : Port) :
    OpcodeGenerator.finalPositions F xs (fun _ => 0) p=
      (if p=RawSelector.rawOutput then ((FamilyEnumeration.stream F xs).length:ℤ) else 0)+
      (if p=VertexScheduler.outputPort then (4*Counter.value xs*rationalPageCount F:ℕ) else 0) := by
  by_cases ho : p=VertexScheduler.outputPort <;>
    simp [OpcodeGenerator.finalPositions,VertexScheduler.advance,CanonicalReader.finalPositions,RawSelector.advance,ho]

theorem marked_head_zero (F : Fin (r+1) → RationalMobius) (xs : List Bool) (j : Fin 7) :
    OpcodeGenerator.finalPositions F xs (fun _ => 0) (markedPorts j)=0 := by
  have hr : markedPorts j≠RawSelector.rawOutput:=categories_disjoint.2.1 j 0
  have ho : markedPorts j≠VertexScheduler.outputPort:=categories_disjoint.2.1 j 3
  simp only [head_eq,hr,ho,ite_false,Nat.cast_zero,zero_add]

theorem marker_head_zero (F : Fin (r+1) → RationalMobius) (xs : List Bool) (j : Fin 2) :
    OpcodeGenerator.finalPositions F xs (fun _ => 0) (markerPorts j)=0 := by
  have hr : markerPorts j≠RawSelector.rawOutput:=categories_disjoint.2.2 j 0
  have ho : markerPorts j≠VertexScheduler.outputPort:=categories_disjoint.2.2 j 3
  simp only [head_eq,hr,ho,ite_false,Nat.cast_zero,zero_add]

theorem stream_head (F : Fin (r+1) → RationalMobius) (xs : List Bool) (j : Fin 4) :
    OpcodeGenerator.finalPositions F xs (fun _ => 0) (streamPorts j)=
      if atEnd j then ((streams F xs j).length:ℤ) else 0 := by
  have hr : streamPorts j=RawSelector.rawOutput ↔ j=0:=by
    change streamPorts j=streamPorts 0 ↔ j=0
    exact streamPorts.injective.eq_iff
  have ho : streamPorts j=VertexScheduler.outputPort ↔ j=3:=by
    change streamPorts j=streamPorts 3 ↔ j=3
    exact streamPorts.injective.eq_iff
  simp only [head_eq,hr,ho]
  fin_cases j <;> simp [atEnd,streams,GeneratedRowClock.bits_length,symbols]

theorem outside_head_zero (F : Fin (r+1) → RationalMobius) (xs : List Bool) (p : Port)
    (hs : ¬∃ j,streamPorts j=p) : OpcodeGenerator.finalPositions F xs (fun _ => 0) p=0 := by
  have hr : p≠RawSelector.rawOutput:=by intro h;exact hs ⟨0,h.symm⟩
  have ho : p≠VertexScheduler.outputPort:=by intro h;exact hs ⟨3,h.symm⟩
  simp only [head_eq,hr,ho,ite_false,Nat.cast_zero,zero_add]

theorem streams_nonblank (F : Fin (r+1) → RationalMobius) (xs : List Bool) (j : Fin 4) :
    ∀ s ∈ streams F xs j,s≠.blank := by
  fin_cases j
  · exact FamilyReader.stream_nonblank F xs
  · exact RawNormalization.output_nonblank F xs
  · exact FamilySelector.output_nonblank F xs
  · intro s hs
    obtain ⟨b,_hb,rfl⟩:=List.mem_map.mp hs
    simp

end TransposeFollowup.GeneratorCleanup


/-! Fixed cleanup control for the generator's existing 42 tapes. The
seven marked words, two lone markers and four bare streams are erased in
that order. Every return to the next subroutine is a paid transition. -/
namespace TransposeFollowup.GeneratorCleanup
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label
  | batch (pc : NativeBatchErase.Label 7)
  | marker (j : Fin 2) (pc : NativeUnprepare.Label)
  | stream (j : Fin 4) (pc : NativeSpanErase.Label)
  | done
  deriving DecidableEq, Fintype

def streamEntry (k : ℕ) : Label :=
  if h : k<4 then .stream ⟨k,h⟩ (NativeSpanErase.start (atEnd ⟨k,h⟩)) else .done

def markerEntry (k : ℕ) : Label :=
  if h : k<2 then .marker ⟨k,h⟩ 0 else streamEntry 0

def start : Label := .batch (NativeBatchErase.entry 7 0)

def program : Microcode.Program Port Label
  | .batch pc => if pc=.done then .jump (markerEntry 0) else
      FamilyEnumeration.identityBinding.instruction Label.batch (NativeBatchErase.program markedPorts pc)
  | .marker j pc => if pc=2 then .jump (markerEntry (j.val+1)) else
      (NativeBatchErase.binding markerPorts j).instruction (Label.marker j) (NativeUnprepare.program pc)
  | .stream j pc => if pc=.done then .jump (streamEntry (j.val+1)) else
      (NativeBatchErase.binding streamPorts j).instruction (Label.stream j) (NativeSpanErase.program pc)
  | .done => .halt

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem batch_code (pc : NativeBatchErase.Label 7)
    (hh : NativeBatchErase.program markedPorts pc≠.halt) (_ : NativeBatchErase.program markedPorts pc≠.reject) :
    program (.batch pc)=MicrocodeEmbedding.instruction FamilyEnumeration.identityBinding.ports
      Label.batch (NativeBatchErase.program markedPorts pc) := by
  have hp : pc≠.done := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

theorem marker_code (j : Fin 2) (pc : NativeUnprepare.Label)
    (hh : NativeUnprepare.program pc≠.halt) (_ : NativeUnprepare.program pc≠.reject) :
    program (.marker j pc)=MicrocodeEmbedding.instruction (NativeBatchErase.binding markerPorts j).ports
      (Label.marker j) (NativeUnprepare.program pc) := by
  have hp : pc≠2 := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

theorem stream_code (j : Fin 4) (pc : NativeSpanErase.Label)
    (hh : NativeSpanErase.program pc≠.halt) (_ : NativeSpanErase.program pc≠.reject) :
    program (.stream j pc)=MicrocodeEmbedding.instruction (NativeBatchErase.binding streamPorts j).ports
      (Label.stream j) (NativeSpanErase.program pc) := by
  have hp : pc≠.done := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

theorem embed_batch (pc : NativeBatchErase.Label 7) (s base : Bank) (pos framePos : Port → ℤ) :
    MicrocodeEmbedding.embed FamilyEnumeration.identityBinding.ports Label.batch
      (NativeBatchErase.cfg pc s pos) (NativeBatchErase.frame base framePos)=cfg (.batch pc) s pos := by
  unfold MicrocodeEmbedding.embed NativeBatchErase.cfg NativeBatchErase.frame cfg
  simp only [← FamilyEnumeration.identityBinding.values_eq_extend]
  rfl

theorem batch_call (words : Fin 7 → List Bool) (s : Bank)
    (hs : ∀ j,s (markedPorts j)=Counter.marked (words j)) (pos : Port → ℤ) :
    ∃ t ≤ ∑ j : Fin 7,(4*(words j).length+5), Trace t (cfg start s pos)
      (cfg (.batch .done) (NativeBatchErase.stage markedPorts s 7) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeBatchErase.complete_trace markedPorts words s hs pos
  have he:=MicrocodeEmbedding.trace_embed FamilyEnumeration.identityBinding.ports Label.batch
    (NativeBatchErase.program markedPorts) program (NativeBatchErase.frame s pos) batch_code htr
  exact ⟨t,ht,by simpa only [embed_batch,start] using he⟩

theorem embed_single {m : ℕ} {J : Type*} (ports : Fin m ↪ Port) (j : Fin m)
    (labels : J → Label) (pc : J) (w : Tape Bool) (head : ℤ) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (NativeBatchErase.binding ports j).ports labels
      ((⟨⟨pc,fun _ : Fin 1 => w⟩,fun _ => head⟩ : NativeZipper.Config (Fin 1) J).denote)
      (NativeBatchErase.frame s pos)=
      cfg (labels pc) (Function.update s (ports j) w) (Function.update pos (ports j) head) := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    NativeBatchErase.frame cfg
  simp only [← (NativeBatchErase.binding ports j).values_eq_extend]
  congr 2 <;> funext p <;> by_cases hp : p=ports j
  all_goals simp [NativeBatchErase.binding,FinitePortBinding.values,Function.update,hp]

theorem marker_call (j : Fin 2) (s : Bank) (hs : s (markerPorts j)=BinaryCarry.preparedOutput)
    (pos : Port → ℤ) :
    ∃ t ≤ 2, Trace t (cfg (.marker j 0) s pos)
      (cfg (.marker j 2) (Function.update s (markerPorts j) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeUnprepare.complete_trace (fun _ => pos (markerPorts j))
  have he:=MicrocodeEmbedding.trace_embed (NativeBatchErase.binding markerPorts j).ports (Label.marker j)
    NativeUnprepare.program program (NativeBatchErase.frame s pos) (marker_code j) htr
  exact ⟨t,ht,by simpa only [NativeUnprepare.cfg,embed_single,← hs,Function.update_eq_self] using he⟩

theorem stream_call (j : Fin 4) (xs : List (Sym Bool)) (hx : ∀ a ∈ xs,a≠.blank)
    (s : Bank) (hs : s (streamPorts j)=streamTape j xs)
    (pos : Port → ℤ) (hp : pos (streamPorts j)=if atEnd j then (xs.length:ℤ) else 0) :
    ∃ t ≤ NativeSpanErase.budget (atEnd j) xs.length,
      Trace t (cfg (.stream j (NativeSpanErase.start (atEnd j))) s pos)
        (cfg (.stream j .done) (Function.update s (streamPorts j) ⟨[],[]⟩)
          (Function.update pos (streamPorts j) 0)) := by
  obtain ⟨t,ht,htr⟩:=NativeSpanErase.complete_trace (atEnd j) xs hx (fun _ => 0)
  have he:=MicrocodeEmbedding.trace_embed (NativeBatchErase.binding streamPorts j).ports (Label.stream j)
    NativeSpanErase.program program (NativeBatchErase.frame s pos) (stream_code j) htr
  have hpos : NativeSpanErase.inputPosition (atEnd j) xs (fun _ => 0)=
      (fun _ => pos (streamPorts j)) := by
    rw [hp];cases atEnd j <;> simp [NativeSpanErase.inputPosition]
  have htape : NativeSpanErase.inputTape (atEnd j) xs=streamTape j xs := rfl
  rw [hpos] at he
  exact ⟨t,ht,by simpa only [NativeSpanErase.cfg,embed_single,htape,← hs,Function.update_eq_self] using he⟩

theorem jump_trace (pc next : Label) (hc : program pc=.jump next) (s : Bank) (pos : Port → ℤ) :
    Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ hc

end TransposeFollowup.GeneratorCleanup


namespace TransposeFollowup.GeneratorCleanup
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def markedBank (s : Bank) : Bank := NativeBatchErase.stage markedPorts s 7
def markerBank (s : Bank) (k : ℕ) : Bank := NativeBatchErase.stage markerPorts (markedBank s) k
def streamBank (s : Bank) (k : ℕ) : Bank := NativeBatchErase.stage streamPorts (markerBank s 2) k

def resetPositions (pos : Port → ℤ) (k : ℕ) : Port → ℤ :=
  fun p => if ∃ j : Fin 4,j.val<k ∧ streamPorts j=p then 0 else pos p

theorem reset_zero (pos : Port → ℤ) : resetPositions pos 0=pos := by
  funext p;simp [resetPositions]

theorem reset_future (pos : Port → ℤ) (k : ℕ) (j : Fin 4) (hj : k≤j.val) :
    resetPositions pos k (streamPorts j)=pos (streamPorts j) := by
  have hn : ¬∃ i : Fin 4,i.val<k ∧ streamPorts i=streamPorts j := by
    rintro ⟨i,hi,hij⟩
    have := streamPorts.injective hij
    subst i;omega
  simp only [resetPositions,hn,ite_false]

theorem reset_step (pos : Port → ℤ) (j : Fin 4) :
    Function.update (resetPositions pos j.val) (streamPorts j) 0=resetPositions pos (j.val+1) := by
  funext p
  by_cases hp : p=streamPorts j
  · subst p
    have h : ∃ i : Fin 4,i.val<j.val+1 ∧ streamPorts i=streamPorts j := ⟨j,by omega,rfl⟩
    simp only [Function.update_self,resetPositions,h,ite_true]
  · have h : (∃ i : Fin 4,i.val<j.val+1 ∧ streamPorts i=p) ↔
        ∃ i : Fin 4,i.val<j.val ∧ streamPorts i=p := by
      constructor
      · rintro ⟨i,hi,hip⟩
        have hn : i.val≠j.val := by
          intro hv
          have := Fin.ext hv
          subst i;exact hp hip.symm
        exact ⟨i,by omega,hip⟩
      · rintro ⟨i,hi,hip⟩;exact ⟨i,by omega,hip⟩
    simp only [Function.update_of_ne hp,resetPositions,h]

theorem marker_from (s : Bank) (hu : ∀ j,s (markerPorts j)=BinaryCarry.preparedOutput)
    (pos : Port → ℤ) (k : ℕ) (hk : k≤2) :
    ∃ t ≤ 3*(2-k),Trace t (cfg (markerEntry k) (markerBank s k) pos)
      (cfg (streamEntry 0) (markerBank s 2) pos) := by
  induction h : 2-k generalizing k with
  | zero =>
    have he : k=2 := by omega
    subst k
    refine ⟨0,by omega,?_⟩
    simp only [markerEntry,lt_self_iff_false,↓reduceDIte]
    exact .refl _
  | succ d ih =>
    have hkr : k<2 := by omega
    let j : Fin 2 := ⟨k,hkr⟩
    have hm : ¬∃ i,markedPorts i=markerPorts j := by
      rintro ⟨i,hi⟩;exact categories_disjoint.1 i j hi
    have hw : markerBank s k (markerPorts j)=BinaryCarry.preparedOutput := by
      unfold markerBank
      rw [NativeBatchErase.stage_future markerPorts (markedBank s) k j (by rfl)]
      exact (NativeBatchErase.stage_outside markedPorts s 7 (markerPorts j) hm).trans (hu j)
    obtain ⟨a,ha,ta⟩:=marker_call j (markerBank s k) hw pos
    have he : Function.update (markerBank s k) (markerPorts j) ⟨[],[]⟩=markerBank s (k+1) :=
      NativeBatchErase.stage_step markerPorts (markedBank s) j
    rw [he] at ta
    have tj:=jump_trace (.marker j 2) (markerEntry (k+1)) rfl (markerBank s (k+1)) pos
    obtain ⟨b,hb,tb⟩:=ih (k+1) (by omega) (by omega)
    refine ⟨a+1+b,by omega,?_⟩
    have he : markerEntry k=.marker j 0 := by simp [markerEntry,hkr,j]
    rw [he]
    exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tj) tb

def streamBudget (words : Fin 4 → List (Sym Bool)) (k : ℕ) : ℕ :=
  ∑ j : Fin 4,if k≤j.val then NativeSpanErase.budget (atEnd j) (words j).length+1 else 0

theorem streamBudget_step (words : Fin 4 → List (Sym Bool)) (j : Fin 4) :
    streamBudget words j.val=NativeSpanErase.budget (atEnd j) (words j).length+1+
      streamBudget words (j.val+1) := by
  fin_cases j <;> simp [streamBudget,Fin.sum_univ_succ]

theorem streams_retained (s : Bank) (j : Fin 4) : markerBank s 2 (streamPorts j)=s (streamPorts j) := by
  have hm : ¬∃ i,markedPorts i=streamPorts j := by
    rintro ⟨i,hi⟩;exact categories_disjoint.2.1 i j hi
  have hu : ¬∃ i,markerPorts i=streamPorts j := by
    rintro ⟨i,hi⟩;exact categories_disjoint.2.2 i j hi
  exact (NativeBatchErase.stage_outside markerPorts (markedBank s) 2 (streamPorts j) hu).trans
    (NativeBatchErase.stage_outside markedPorts s 7 (streamPorts j) hm)

theorem stream_from (words : Fin 4 → List (Sym Bool)) (hx : ∀ j a,a ∈ words j → a≠.blank)
    (s : Bank) (hs : ∀ j,s (streamPorts j)=streamTape j (words j))
    (pos : Port → ℤ) (hp : ∀ j,pos (streamPorts j)=if atEnd j then ((words j).length:ℤ) else 0)
    (k : ℕ) (hk : k≤4) :
    ∃ t ≤ streamBudget words k,Trace t
      (cfg (streamEntry k) (streamBank s k) (resetPositions pos k))
      (cfg .done (streamBank s 4) (resetPositions pos 4)) := by
  induction h : 4-k generalizing k with
  | zero =>
    have he : k=4 := by omega
    subst k
    refine ⟨0,Nat.zero_le _,?_⟩
    simp only [streamEntry,lt_self_iff_false,↓reduceDIte]
    exact .refl _
  | succ d ih =>
    have hkr : k<4 := by omega
    let j : Fin 4 := ⟨k,hkr⟩
    have hw : streamBank s k (streamPorts j)=streamTape j (words j) := by
      unfold streamBank
      rw [NativeBatchErase.stage_future streamPorts (markerBank s 2) k j (by rfl),streams_retained,hs]
    have hpos : resetPositions pos k (streamPorts j)=if atEnd j then ((words j).length:ℤ) else 0 :=
      (reset_future pos k j (by rfl)).trans (hp j)
    obtain ⟨a,ha,ta⟩:=stream_call j (words j) (hx j) (streamBank s k) hw (resetPositions pos k) hpos
    have hs' : Function.update (streamBank s k) (streamPorts j) ⟨[],[]⟩=streamBank s (k+1) :=
      NativeBatchErase.stage_step streamPorts (markerBank s 2) j
    have hp' : Function.update (resetPositions pos k) (streamPorts j) 0=resetPositions pos (k+1) := reset_step pos j
    rw [hs',hp'] at ta
    have tj:=jump_trace (.stream j .done) (streamEntry (k+1)) rfl (streamBank s (k+1)) (resetPositions pos (k+1))
    obtain ⟨b,hb,tb⟩:=ih (k+1) (by omega) (by omega)
    refine ⟨a+1+b,?_,?_⟩
    · have hbnd:=streamBudget_step words j
      change streamBudget words k=NativeSpanErase.budget (atEnd j) (words j).length+1+streamBudget words (k+1) at hbnd
      omega
    · have he : streamEntry k=.stream j (NativeSpanErase.start (atEnd j)) := by simp [streamEntry,hkr,j]
      rw [he]
      exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tj) tb

def budget (F : Fin (r+1) → RationalMobius) (w xs : List Bool) : ℕ :=
  (∑ j : Fin 7,(4*(markedWords F w xs j).length+5))+7+streamBudget (streams F xs) 0

theorem final_bank_blank (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    streamBank (OpcodeGenerator.finalBank F w xs) 4=(fun _ => ⟨[],[]⟩) := by
  funext p
  by_cases hs : ∃ j,streamPorts j=p
  · obtain ⟨j,rfl⟩:=hs
    exact NativeBatchErase.final_at streamPorts _ j
  · rw [streamBank,NativeBatchErase.stage_outside streamPorts _ 4 p hs]
    by_cases hu : ∃ j,markerPorts j=p
    · obtain ⟨j,rfl⟩:=hu
      exact NativeBatchErase.final_at markerPorts _ j
    · rw [markerBank,NativeBatchErase.stage_outside markerPorts _ 2 p hu]
      by_cases hm : ∃ j,markedPorts j=p
      · obtain ⟨j,rfl⟩:=hm
        exact NativeBatchErase.final_at markedPorts _ j
      · rw [markedBank,NativeBatchErase.stage_outside markedPorts _ 7 p hm]
        exact outside_blank F w xs p hm hu hs

theorem final_positions_zero (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    resetPositions (OpcodeGenerator.finalPositions F xs (fun _ => 0)) 4=(fun _ => 0) := by
  funext p
  by_cases hs : ∃ j,streamPorts j=p
  · obtain ⟨j,rfl⟩:=hs
    have h : ∃ i : Fin 4,i.val<4 ∧ streamPorts i=streamPorts j := ⟨j,j.isLt,rfl⟩
    simp only [resetPositions,h,ite_true]
  · have h : ¬∃ j : Fin 4,j.val<4 ∧ streamPorts j=p := by rintro ⟨j,_,hj⟩;exact hs ⟨j,hj⟩
    simp only [resetPositions,h,ite_false]
    exact outside_head_zero F xs p hs

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    ∃ t ≤ budget F w xs,Trace t
      (cfg start (OpcodeGenerator.finalBank F w xs) (OpcodeGenerator.finalPositions F xs (fun _ => 0)))
      (cfg .done (fun _ => ⟨[],[]⟩) (fun _ => 0)) := by
  let s:=OpcodeGenerator.finalBank F w xs
  let pos:=OpcodeGenerator.finalPositions F xs (fun _ => 0)
  obtain ⟨a,ha,ta⟩:=batch_call (markedWords F w xs) s (marked_at F w xs) pos
  have tj:=jump_trace (.batch .done) (markerEntry 0) rfl (markedBank s) pos
  obtain ⟨b,hb,tb⟩:=marker_from s (marker_at F w xs) pos 0 (by omega)
  obtain ⟨c,hc,tc⟩:=stream_from (streams F xs) (streams_nonblank F xs) s (stream_at F w xs)
    pos (stream_head F xs) 0 (by omega)
  simp only [markerBank,NativeBatchErase.stage_zero] at tb
  simp only [streamBank,NativeBatchErase.stage_zero,reset_zero] at tc
  have htr:=NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tj) tb) tc
  refine ⟨a+1+b+c,?_,?_⟩
  · unfold budget;omega
  · change Trace _ _ (cfg .done (streamBank s 4) (resetPositions pos 4)) at htr
    simpa only [s,pos,final_bank_blank,final_positions_zero] using htr

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem native_complete (F : Fin (r+1) → RationalMobius) (w xs input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget F w xs,
      Transpose.stepN nativeMachine input t
        ((cfg start (OpcodeGenerator.finalBank F w xs) (OpcodeGenerator.finalPositions F xs (fun _ => 0))).denote
          nativeEncoding program ip outRev)=
        some ((cfg .done (fun _ => ⟨[],[]⟩) (fun _ => 0)).denote nativeEncoding program ip outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done (fun _ => ⟨[],[]⟩) (fun _ => 0)).denote nativeEncoding program ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace F w xs
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem fixed_resources : nativeMachine.k=42 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=92 ∧
    nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42
    decide +kernel
  · change Fintype.card Label-1+1=92
    decide +kernel

end TransposeFollowup.GeneratorCleanup


/-! The cleanup controller is fixed independently of the rational map
family. Its linear-time constant may depend on that fixed family. Stream
sizes are bounded using their already-paid generation, not a new runtime
oracle for their lengths. -/
namespace TransposeFollowup.GeneratorCleanup
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem word_eq_of_value_length (xs ys : List Bool) (hl : xs.length=ys.length)
    (hv : Counter.value xs=Counter.value ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => simpa using hl.symm
  | cons b xs ih =>
    cases ys with
    | nil => simp at hl
    | cons c ys =>
      simp only [List.length_cons] at hl
      cases b <;> cases c <;> simp only [Counter.value] at hv
      all_goals first | omega | exact congrArg (List.cons _) (ih ys (by omega) (by omega))

def lengthCoefficient (F : Fin (r+1) → RationalMobius) : Fin 4 → ℕ :=
  ![FamilyEnumeration.coefficient F,RawNormalization.coefficient F,RawSelector.coefficient F,4*rationalPageCount F]

theorem stream_lengths (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (n : ℕ)
    (hn : 1≤n) (hw : w.length=Transpose.inputLength n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (j : Fin 4) : (streams F xs j).length≤lengthCoefficient F j*w.length := by
  fin_cases j
  · change (FamilyEnumeration.stream F xs).length≤FamilyEnumeration.coefficient F*w.length
    obtain ⟨ys,_hy,hyv,hyl,t,ht,hlen,_htr⟩:=FamilyReader.generate_call F w n hn hw (fun _ => 0) []
    have he : ys=xs := word_eq_of_value_length ys xs (hyl.trans hl.symm) (hyv.trans hv.symm)
    subst ys
    exact hlen.trans ht
  · change (FamilyNormalization.outputStream F xs).length≤RawNormalization.coefficient F*w.length
    obtain ⟨ys,_hy,hyv,hyl,t,ht,htr⟩:=RawNormalization.complete_trace F w n hn hw (fun _ => 0) []
    have he : ys=xs := word_eq_of_value_length ys xs (hyl.trans hl.symm) (hyv.trans hv.symm)
    subst ys
    exact (RawNormalization.output_length_le_time F w xs t (fun _ => 0) [] htr).trans ht
  · change (FamilySelector.outputStream F xs).length≤RawSelector.coefficient F*w.length
    obtain ⟨ys,_hy,hyv,hyl,t,ht,htr⟩:=RawSelector.complete_trace F w n hn hw (fun _ => 0) []
    have he : ys=xs := word_eq_of_value_length ys xs (hyl.trans hl.symm) (hyv.trans hv.symm)
    subst ys
    exact (RawSelector.output_length_le_time F w xs t (fun _ => 0) [] htr).trans ht
  · change (symbols (GeneratedRowClock.bits F (Counter.value xs))).length≤4*rationalPageCount F*w.length
    simp only [symbols,List.length_map,GeneratedRowClock.bits_length,hv]
    have hnL : n≤w.length := by rw [hw];exact DimensionCandidate.dimension_le_length n hn
    calc
      4*n*rationalPageCount F=(4*rationalPageCount F)*n := by ring
      _≤_ := Nat.mul_le_mul_left _ hnL

theorem marked_lengths (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (hL : 1≤w.length) (hl : xs.length≤w.length) (j : Fin 7) :
    (markedWords F w xs j).length≤(FamilyNormalization.common F+3)*w.length := by
  have hC : FamilyNormalization.common F≤FamilyNormalization.common F*w.length := by nlinarith
  fin_cases j
  · change w.length≤_
    nlinarith
  · change xs.length≤_
    nlinarith
  · change (PaddedWord.word (FamilyNormalization.common F) id xs).length≤_
    rw [PaddedWord.word_length]
    nlinarith
  · change (SchedulerSeed.vertexWord F xs).length≤_
    rw [SchedulerSeed.vertex_length]
    nlinarith
  · change (SchedulerSeed.vertexWord F xs).length≤_
    rw [SchedulerSeed.vertex_length]
    nlinarith
  · change (ArithmeticSeed.one (2*xs.length+FamilyNormalization.common F)).length≤_
    simp only [ArithmeticSeed.one,ArithmeticSeed.zeros,List.length_cons,List.length_replicate]
    have h : 2*xs.length+FamilyNormalization.common F-1≤2*xs.length+FamilyNormalization.common F := Nat.sub_le _ _
    nlinarith
  · change 1≤_
    nlinarith

def coefficient (F : Fin (r+1) → RationalMobius) : ℕ :=
  7*(4*(FamilyNormalization.common F+3)+5)+7+
    ∑ j : Fin 4,(5*lengthCoefficient F j+5)

theorem budget_linear (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (n : ℕ)
    (hn : 1≤n) (hw : w.length=Transpose.inputLength n) (hv : Counter.value xs=n) (hl : xs.length=n.size) :
    budget F w xs≤coefficient F*w.length := by
  have hnL : n≤w.length := by rw [hw];exact DimensionCandidate.dimension_le_length n hn
  have hs : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hL : 1≤w.length := hn.trans hnL
  have hx : xs.length≤w.length := by omega
  have hm : (∑ j : Fin 7,(4*(markedWords F w xs j).length+5))≤
      (7*(4*(FamilyNormalization.common F+3)+5))*w.length := by
    calc
      _≤∑ j : Fin 7,((4*(FamilyNormalization.common F+3)+5)*w.length) := by
        apply Finset.sum_le_sum
        intro j _
        have h:=marked_lengths F w xs hL hx j
        nlinarith
      _=_ := by simp [Finset.sum_const,smul_eq_mul];ring
  have ht : streamBudget (streams F xs) 0≤(∑ j : Fin 4,(5*lengthCoefficient F j+5))*w.length := by
    unfold streamBudget
    simp only [Nat.zero_le,ite_true,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    have h:=stream_lengths F w xs n hn hw hv hl j
    have he : NativeSpanErase.budget (atEnd j) (streams F xs j).length≤5*(streams F xs j).length+4 := by
      unfold NativeSpanErase.budget
      split <;> omega
    nlinarith
  unfold budget coefficient
  nlinarith

theorem linear_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (n : ℕ)
    (hn : 1≤n) (hw : w.length=Transpose.inputLength n) (hv : Counter.value xs=n) (hl : xs.length=n.size) :
    ∃ t ≤ coefficient F*w.length,Trace t
      (cfg start (OpcodeGenerator.finalBank F w xs) (OpcodeGenerator.finalPositions F xs (fun _ => 0)))
      (cfg .done (fun _ => ⟨[],[]⟩) (fun _ => 0)) := by
  obtain ⟨t,ht,htr⟩:=complete_trace F w xs
  exact ⟨t,ht.trans (budget_linear F w xs n hn hw hv hl),htr⟩

theorem native_linear (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (n : ℕ)
    (hn : 1≤n) (hw : w.length=Transpose.inputLength n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN nativeMachine input t
        ((cfg start (OpcodeGenerator.finalBank F w xs) (OpcodeGenerator.finalPositions F xs (fun _ => 0))).denote
          nativeEncoding program ip outRev)=
        some ((cfg .done (fun _ => ⟨[],[]⟩) (fun _ => 0)).denote nativeEncoding program ip outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done (fun _ => ⟨[],[]⟩) (fun _ => 0)).denote nativeEncoding program ip outRev)=none := by
  obtain ⟨t,ht,htr,hh⟩:=native_complete F w xs input ip outRev
  exact ⟨t,ht.trans (budget_linear F w xs n hn hw hv hl),htr,hh⟩

end TransposeFollowup.GeneratorCleanup
