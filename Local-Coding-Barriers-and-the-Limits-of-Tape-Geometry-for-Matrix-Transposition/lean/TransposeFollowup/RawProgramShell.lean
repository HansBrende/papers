import TransposeFollowup.ScheduledModeRawIO
import TransposeFollowup.RawRowBankInvariant
import Transpose.Tape.Run

/-! Shared raw-IO assembly for finite product controllers. The body is an
actual schedule, with its duration and activity supplied explicitly. This
shell can serve integer and trit operation words; it does not assume an
input-independent exact body path. Loading/emission and native compilation
are the existing proved routines. -/
namespace TransposeFollowup.RawProgramShell
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open NativeIOModeProduct
open CopyMachine (Sym)
set_option autoImplicit false
variable {F : Type*}

abbrev Mode (F : Type*) := MaskedStrideCell.Mode × F
abbrev State (F : Type*) := NativeIO.Config (Fin 2) (Mode F)

def initial (f : F) : State F := ScheduledModeRawIO.initial (Equiv.refl _) f
def prepared (f : F) (P : ℕ) (w : List Bool) : State F :=
  ScheduledModeRawIO.prepared (Equiv.refl _) f P w

def ticks (P N : ℕ) : ℕ := 3*P+P+(N+3*P)

noncomputable def schedule (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F)) :=
  append (ScheduledModeRawIO.prepareSchedule (Equiv.refl _) P)
    (append σ (ScheduledModeRawIO.outputSchedule (Equiv.refl _)) N) (3*P+P)

def ready (f : F) (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F)) (w : List Bool) :=
  trajectory σ w (prepared f P w) N

def result (f : F) (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F)) (w : List Bool) :=
  ScheduledModeRawIO.emitted (Equiv.refl _) w (ready f P N σ w) P

theorem ticks_eq (P N : ℕ) : ticks P N=7*P+N := by unfold ticks; omega

theorem schedule_active (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F))
    (ha : ∀ i c, NativeIO.Active (σ i) c) (i : ℕ) (c : State F) :
    NativeIO.Active (schedule P N σ i) c := by
  apply append_active
  · intro j; exact ScheduledModeRawIO.prepare_active _ P j c
  · intro j
    apply append_active
    · intro j; exact ha j c
    · intro j; exact ScheduledModeRawIO.output_active _ j c

theorem schedule_exact (f : F) (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F))
    (w : List Bool) :
    trajectory (schedule P N σ) w (initial f) (ticks P N)=result f P N σ w := by
  simp only [schedule,ticks,initial,append_exact,ScheduledModeRawIO.prepare_exact,
    ScheduledModeRawIO.output_exact,prepared,ready,result]

theorem prepared_symbol (f : F) (P : ℕ) (w : List Bool) (j : ℕ) (hj : j<P) :
    BankWord.input BankWord.symbols (prepared f P w) j=.data (ScheduledRawInput.inputBit w j) := by
  change cells (RawMaskedStride.prepared P w) 0 ((RawMaskedStride.prepared P w).work.pos 0+j)=_
  rw [RawMaskedStride.prepared_position,zero_add,RawMaskedStride.prepared,rewind_cells]
  simpa only [RawMaskedStride.initial,NativeMicrocode.blankConfig,zero_add] using
    ScheduledRawInput.loaded_written w RawMaskedStride.initial P j hj

theorem output_spec (f : F) (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F))
    (v : (ℕ → Sym Bool) → ℕ → Sym Bool)
    (hv : BankWord.Congruent P v)
    (hr : ∀ w c, BankWord.symbols.clean c →
      BankWord.Represents BankWord.symbols P c (trajectory σ w c N)
        (v (BankWord.input BankWord.symbols c))) (w : List Bool) :
    (result f P N σ w).outRev=
      ((List.range P).map (fun j : ℕ => MaskedStrideCell.bit
        (v (fun i : ℕ => .data (ScheduledRawInput.inputBit w i)) j))).reverse ∧
    ∀ z, cells (result f P N σ w) 1 z=.blank := by
  have hp := ScheduledModeRawIO.prepared_spec (Equiv.refl (Mode F)) f P w
  have h := hr w (prepared f P w) hp.2.2.1
  have he := ScheduledModeRawIO.emitted_spec (Equiv.refl (Mode F)) w (ready f P N σ w) P
  have hpos : (ready f P N σ w).work.pos 0=0 := (h.1 0).trans (hp.1 0)
  have hout : (ready f P N σ w).outRev=[] := h.2.2.2.2.trans hp.2.2.2.2.1
  refine ⟨?_,fun z => (he.2.1 1 z).trans (h.2.2.1 z)⟩
  change (ScheduledModeRawIO.emitted (Equiv.refl (Mode F)) w (ready f P N σ w) P).outRev=_
  rw [he.2.2.2.1,hpos,hout,List.append_nil]
  simp only [zero_add]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hbit := h.2.1 j (List.mem_range.mp hj)
  change cells (ready f P N σ w) 0 ((prepared f P w).work.pos 0+j)=_ at hbit
  have hp0 : (prepared f P w).work.pos 0=0 := hp.1 0
  rw [hp0,zero_add] at hbit
  rw [hbit,hv _ _ (fun i hi => prepared_symbol f P w i hi) j (List.mem_range.mp hj)]

noncomputable def encoding [Fintype F] (f : F) (P N : ℕ) :=
  NativeMicrocode.initialEncoding (T:=Fin 2)
    ((⟨0,by omega⟩,((false,false),f)) : Fin (ticks P N+1) × Mode F)

noncomputable def machine [Fintype F] (f : F) (P N : ℕ)
    (σ : ℕ → NativeIO.Program (Fin 2) (Mode F)) :=
  NativeIO.machine (encoding f P N) (program (schedule P N σ) (ticks P N))

theorem native_complete [Fintype F] (f : F) (P N : ℕ)
    (σ : ℕ → NativeIO.Program (Fin 2) (Mode F))
    (ha : ∀ i c, NativeIO.Active (σ i) c) (w : List Bool) :
    Transpose.stepN (machine f P N σ) w (ticks P N) (Transpose.init (machine f P N σ))=
      some ((lift (⟨ticks P N,by omega⟩ : Fin (ticks P N+1)) (result f P N σ w)).denote
        (encoding f P N) (program (schedule P N σ) (ticks P N))) ∧
    Transpose.step (machine f P N σ) w
      ((lift (⟨ticks P N,by omega⟩ : Fin (ticks P N+1)) (result f P N σ w)).denote
        (encoding f P N) (program (schedule P N σ) (ticks P N)))=none := by
  have h := native_run_and_halt (encoding f P N) (schedule P N σ) w (initial f)
    (fun i _ => schedule_active P N σ ha i _)
  rw [schedule_exact] at h
  have hb : (lift (⟨0,by omega⟩ : Fin (ticks P N+1)) (initial f)).denote
      (encoding f P N) (program (schedule P N σ) (ticks P N))=Transpose.init (machine f P N σ) :=
    NativeIO.blank_denote (encoding f P N) _ _ (NativeMicrocode.initialEncoding_start _)
  rw [hb] at h
  exact h

theorem fixed_resources [Fintype F] (f : F) (P N : ℕ)
    (σ : ℕ → NativeIO.Program (Fin 2) (Mode F)) :
    (machine f P N σ).k=2 ∧ (machine f P N σ).g+1=5 ∧
    (machine f P N σ).q+1=(ticks P N+1)*(4*Fintype.card F) := by
  refine ⟨rfl,rfl,?_⟩
  have h := native_state_count (schedule P N σ) (ticks P N) ((false,false),f)
  change (machine f P N σ).q+1=(ticks P N+1)*Fintype.card (Mode F) at h
  rw [show Fintype.card (Mode F)=4*Fintype.card F by simp [Mode,MaskedStrideCell.Mode]] at h
  exact h

/-- Combine native execution and the symbol-bank output invariant once,
so individual bank operations need not repeat the encoding/blank-scratch
argument. The native machine starts on genuinely blank work tapes. -/
theorem native_correct [Fintype F] (f : F) (P N : ℕ)
    (σ : ℕ → NativeIO.Program (Fin 2) (Mode F)) (ha : ∀ i c, NativeIO.Active (σ i) c)
    (v : (ℕ → Sym Bool) → ℕ → Sym Bool) (hv : BankWord.Congruent P v)
    (hr : ∀ w c, BankWord.symbols.clean c →
      BankWord.Represents BankWord.symbols P c (trajectory σ w c N)
        (v (BankWord.input BankWord.symbols c))) (w : List Bool) :
    ∃ d : Transpose.Config (machine f P N σ),
      Transpose.stepN (machine f P N σ) w (ticks P N) (Transpose.init (machine f P N σ))=some d ∧
      Transpose.step (machine f P N σ) w d=none ∧
      d.outRev=((List.range P).map (fun j : ℕ => MaskedStrideCell.bit
        (v (fun i : ℕ => .data (ScheduledRawInput.inputBit w i)) j))).reverse ∧
      ∀ z, d.work ((encoding f P N).port 1) z=0 := by
  have hn := native_complete f P N σ ha w
  have hd := output_spec f P N σ v hv hr w
  refine ⟨_,hn.1,hn.2,hd.1,?_⟩
  intro z
  change NativeMicrocode.symbolCode (cells (result f P N σ w)
    ((encoding f P N).port.symm ((encoding f P N).port 1)) z)=0
  rw [Equiv.symm_apply_apply,hd.2 z]
  rfl

end TransposeFollowup.RawProgramShell
