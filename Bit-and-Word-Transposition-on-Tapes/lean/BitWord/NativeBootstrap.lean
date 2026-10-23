import BitWord.NativeTapeCalls
import TransposeFollowup.RawDimensionLoader
import TransposeFollowup.EntryBitsRun

/-! Raw canonical input to a marked payload, its recovered dimension, and its
entry-width word. This is the shared beginning of the uniform reduction. -/
namespace BitWord.NativeBootstrap
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop

inductive Port
  | raw (p : RawDimensionLoader.Port)
  | scratchA | scratchB | hword
  deriving DecidableEq,Fintype
abbrev Bank := Port → Tape Bool

def dimension : Port := .raw (.loader (.work .candidate))
def payload : Port := .raw .payload

def rawBinding : FinitePortBinding RawDimensionLoader.Port Port where
  ports := ⟨Port.raw,by intro p q h; cases h; rfl⟩
  decode := fun p => match p with | .raw q => some q | _ => none
  decode_spec := by
    intro p q
    change (match p with | .raw r => some r | _ => none)=some q ↔ Port.raw q=p
    cases p <;> simp [eq_comm]

def entryBinding : FinitePortBinding (Fin 4) Port where
  ports := ⟨![dimension,.scratchA,.scratchB,.hword],by decide +kernel⟩
  decode := fun p => if p=dimension then some 0 else match p with
    | .scratchA => some 1 | .scratchB => some 2 | .hword => some 3 | _ => none
  decode_spec := by decide +kernel

inductive Label
  | raw (pc : RawDimensionLoader.Label)
  | entry (pc : EntryBits.Label)
  | done
  deriving DecidableEq,Fintype

def start : Label := .raw RawDimensionLoader.start
def program : NativeIO.Program Port Label
  | .raw (.load .done) => .work (.jump (.entry EntryBits.start))
  | .raw pc => NativeIOEmbedding.boundInstruction rawBinding Label.raw (RawDimensionLoader.program pc)
  | .entry .done => .work (.jump .done)
  | .entry pc => .work (entryBinding.instruction Label.entry (EntryBits.program pc))
  | .done => .work .halt

def initial : Bank := fun _ => ⟨[],[]⟩
def loaded (w xs : List Bool) : Bank
  | .raw p => RawDimensionLoader.finalBank w xs p
  | _ => ⟨[],[]⟩
def final (w xs : List Bool) : Bank := Function.update (loaded w xs) .hword
  (Counter.marked (MeasuredWord.result (Transpose.entryBits (Counter.value xs))))

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (out : List Bool) : NativeIO.Config Port Label :=
  NativeExpanderShearFrames.cfg pc s pos ip out
abbrev Trace (w : List Bool) := OperationalTrace.Trace (NativeIO.step program w) (NativeIO.Active program)

theorem raw_code (pc : RawDimensionLoader.Label) (hh : RawDimensionLoader.program pc≠.work .halt)
    (_ : RawDimensionLoader.program pc≠.work .reject) :
    program (.raw pc)=NativeIOEmbedding.instruction rawBinding.ports Label.raw (RawDimensionLoader.program pc) := by
  cases pc with
  | measure q => simp [program,NativeIOEmbedding.bound_instruction_eq]
  | load q => cases q <;> simp_all [program,RawDimensionLoader.program,DimensionLoader.program,
      FinitePortBinding.instruction,NativeIOEmbedding.bound_instruction_eq]

theorem entry_code (pc : EntryBits.Label) (hh : EntryBits.program pc≠.halt)
    (_ : EntryBits.program pc≠.reject) :
    NativeIO.workProgram program (.entry pc)=MicrocodeEmbedding.instruction entryBinding.ports Label.entry
      (EntryBits.program pc) := by
  cases pc <;> simp_all [program,NativeIO.workProgram,EntryBits.program,FinitePortBinding.instruction_eq]

@[simp] theorem raw_values {A : Type*} (x : RawDimensionLoader.Port → A) (s : Port → A) (p : Port) :
    rawBinding.values x s p = match p with | .raw q => x q | _ => s p := by cases p <;> rfl

theorem raw_call (w : List Bool) (d : ℕ) (hd : 1≤d) (hw : w.length=Transpose.inputLength d)
    (pos : Port → ℤ) (out : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
    ∃ t≤8300*w.length,Trace w t (cfg start initial pos 0 out)
      (cfg (.raw (.load .done)) (loaded w xs) pos w.length out) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := RawDimensionLoader.complete_trace w d hd hw
    (fun p => pos (.raw p)) out
  have he := NativeIOEmbedding.trace_embed rawBinding.ports Label.raw RawDimensionLoader.program program
    (frame initial pos) w raw_code htr
  change Trace w t
    (NativeIOEmbedding.embed rawBinding.ports Label.raw
      (NativeExpanderShearFrames.cfg RawDimensionLoader.start RawDimensionLoader.initial
        (fun p => pos (.raw p)) 0 out) _)
    (NativeIOEmbedding.embed rawBinding.ports Label.raw
      (NativeExpanderShearFrames.cfg (.load .done) (RawDimensionLoader.finalBank w xs)
        (fun p => pos (.raw p)) w.length out) _) at he
  rw [embed_io,embed_io] at he
  have hi : rawBinding.values RawDimensionLoader.initial initial=initial := by funext p; cases p <;> rfl
  have hf : rawBinding.values (RawDimensionLoader.finalBank w xs) initial=loaded w xs := by funext p; cases p <;> rfl
  have hp : rawBinding.values (fun p => pos (.raw p)) pos=pos := by funext p; cases p <;> rfl
  exact ⟨xs,hx,hv,hl,t,ht,by simpa only [hi,hf,hp,start,cfg] using he⟩

theorem entry_initial_values (w xs : List Bool) :
    entryBinding.values (EntryBits.initial xs) (loaded w xs)=loaded w xs := by
  funext p
  cases p with
  | raw p =>
    cases p with
    | payload => rfl
    | loader p =>
      cases p with
      | work p => cases p <;> rfl
      | source => rfl
      | extra => rfl
  | scratchA => rfl
  | scratchB => rfl
  | hword => rfl

theorem entry_final_values (w xs : List Bool) :
    entryBinding.values (EntryBits.final xs) (loaded w xs)=final w xs := by
  funext p
  cases p with
  | raw p =>
    cases p with
    | payload => rfl
    | loader p =>
      cases p with
      | work p => cases p <;> rfl
      | source => rfl
      | extra => rfl
  | scratchA => rfl
  | scratchB => rfl
  | hword => rfl

theorem entry_call (w xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) (ip : ℤ) (out : List Bool) :
    ∃ t≤50*xs.length+87,Trace w t (cfg (.entry EntryBits.start) (loaded w xs) pos ip out)
      (cfg (.entry .done) (final w xs) pos ip out) := by
  obtain ⟨t,ht,htr⟩ := EntryBits.complete_trace xs hx (fun p => pos (entryBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed entryBinding.ports Label.entry EntryBits.program
    (NativeIO.workProgram program) (frame (loaded w xs) pos) entry_code htr
  change OperationalTrace.Trace _ _ t
    (MicrocodeEmbedding.embed entryBinding.ports Label.entry
      (workCfg EntryBits.start (EntryBits.initial xs) (fun p => pos (entryBinding.ports p))) _)
    (MicrocodeEmbedding.embed entryBinding.ports Label.entry
      (workCfg .done (EntryBits.final xs) (fun p => pos (entryBinding.ports p))) _) at he
  rw [embed_work,embed_work,entry_initial_values,entry_final_values,entryBinding.values_project] at he
  exact ⟨t,ht,NativeIO.lift_work_trace program w ip out he⟩

theorem jump (w : List Bool) (pc next : Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (out : List Bool)
    (h : program pc=.work (.jump next)) : Trace w 1 (cfg pc s pos ip out) (cfg next s pos ip out) :=
  NativeIO.jump_trace program w (cfg pc s pos ip out) next h

theorem complete_trace (w : List Bool) (d : ℕ) (hd : 1≤d) (hw : w.length=Transpose.inputLength d)
    (pos : Port → ℤ) (out : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
    ∃ t≤8300*w.length+50*d.size+89,Trace w t (cfg start initial pos 0 out)
      (cfg .done (final w xs) pos w.length out) := by
  obtain ⟨xs,hx,hv,hl,t0,h0,tr0⟩ := raw_call w d hd hw pos out
  have j0 := jump w (.raw (.load .done)) (.entry EntryBits.start) (loaded w xs) pos w.length out rfl
  obtain ⟨t1,h1,tr1⟩ := entry_call w xs (by omega) pos w.length out
  have j1 := jump w (.entry .done) .done (final w xs) pos w.length out rfl
  have seg0 := trace_trans tr0 j0
  have seg1 := trace_trans tr1 j1
  exact ⟨xs,hx,hv,hl,_,by omega,trace_trans seg0 seg1⟩

end BitWord.NativeBootstrap
