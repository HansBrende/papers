import TransposeFollowup.BankWordInvariant
import TransposeFollowup.RawMaskedStrideCorrectness
import Transpose.Tape.Run

/-! A shared raw-input/output wrapper for a proved binary-bank program.
The body supplies its actual schedule, semantics and paid duration; the
correctness interface requires execution and bank dependence proofs.
Loading, rewind, emission, native initialization and halting are shared. -/
namespace TransposeFollowup.RawBankProgram
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
set_option autoImplicit false

structure Body where
  cost : ℕ
  code : ℕ → NativeIO.Program (Fin 2) Mode
  run : List Bool → State → State
  value : (ℕ → Bool) → ℕ → Bool

structure Correct (P : ℕ) (B : Body) : Prop where
  active : ∀ i c, NativeIO.Active (B.code i) c
  exact : ∀ w c, trajectory B.code w c B.cost = B.run w c
  represents : ∀ w c, BankWord.binary.clean c →
    BankWord.Represents BankWord.binary P c (B.run w c) (B.value (BankWord.input BankWord.binary c))
  congr : BankWord.Congruent P B.value

def ticks (P : ℕ) (B : Body) : ℕ := 3*P+(P+(B.cost+3*P))

def schedule (P : ℕ) (B : Body) : ℕ → NativeIO.Program (Fin 2) Mode :=
  append ScheduledRawInput.schedule
    (append (fun _ => action 0 ⟨none,.left⟩)
      (append (B.code) ScheduledRawOutput.schedule (B.cost)) P)
    (3*P)

def ready (P : ℕ) (B : Body) (w : List Bool) : State :=
  B.run w (RawMaskedStride.prepared P w)

def result (P : ℕ) (B : Body) (w : List Bool) : State :=
  ScheduledRawOutput.emitted w (ready P B w) P

def outputWord (P : ℕ) (B : Body) (w : List Bool) : List Bool :=
  (List.range P).map (fun j : ℕ => B.value (fun i : ℕ => ScheduledRawInput.inputBit w i) j)

theorem schedule_active (P : ℕ) (B : Body)
    (ha : ∀ j d, NativeIO.Active (B.code j) d) (i : ℕ) (c : State) :
    NativeIO.Active (schedule P B i) c := by
  unfold schedule
  apply append_active
  · intro _; exact ScheduledRawInput.cell_active _ _
  · intro j
    apply append_active
    · intro _; exact ScheduledTapeAction.active _ _ _
    · intro j
      apply append_active
      · intro j; exact ha j c
      · intro _; exact ScheduledRawOutput.cell_active _ _

theorem schedule_exact (P : ℕ) (B : Body) (hc : Correct P B) (w : List Bool) :
    trajectory (schedule P B) w RawMaskedStride.initial (ticks P B) = result P B w := by
  simp only [schedule,ticks,append_exact,ScheduledRawInput.schedule_exact,
    hc.exact,ScheduledRawOutput.schedule_exact]
  rfl

theorem ticks_eq (P : ℕ) (B : Body) : ticks P B = 7*P+B.cost := by unfold ticks; omega

theorem ready_spec (P : ℕ) (B : Body) (hc : Correct P B) (w : List Bool) :
    (∀ t, (ready P B w).work.pos t = 0) ∧
    (∀ j < P, bit (cells (ready P B w) 0 j) =
      B.value (fun i : ℕ => ScheduledRawInput.inputBit w i) j) ∧
    (∀ z, cells (ready P B w) 1 z = .blank) ∧
    (ready P B w).inputPos = P ∧ (ready P B w).outRev = [] := by
  have h := hc.represents w (RawMaskedStride.prepared P w) (RawMaskedStride.prepared_scratch P w)
  refine ⟨fun t => (h.1 t).trans (RawMaskedStride.prepared_position P w t),?_,h.2.2.1,
    h.2.2.2.1.trans (RawMaskedStride.prepared_io P w).1,h.2.2.2.2.trans (RawMaskedStride.prepared_io P w).2⟩
  intro j hj
  have hb := h.2.1 j hj
  change bit (cells (ready P B w) 0 ((RawMaskedStride.prepared P w).work.pos 0+j)) = _ at hb
  rw [RawMaskedStride.prepared_position,zero_add] at hb
  exact hb.trans (hc.congr _ _ (fun k hk => RawMaskedStride.prepared_input P w k hk) j hj)

theorem result_output (P : ℕ) (B : Body) (hc : Correct P B) (w : List Bool) :
    (result P B w).outRev = (outputWord P B w).reverse := by
  have h := ready_spec P B hc w
  rw [result,ScheduledRawOutput.emitted_output,h.1 0,h.2.2.2.2,List.append_nil]
  simp only [zero_add]
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h.2.1 j (List.mem_range.mp hj)

noncomputable def encoding (P : ℕ) (B : Body) := NativeMicrocode.initialEncoding (T:=Fin 2)
  ((⟨0,by omega⟩,(false,false)) : Fin (ticks P B+1) × Mode)

noncomputable def machine (P : ℕ) (B : Body) :=
  NativeIO.machine (encoding P B) (program (schedule P B) (ticks P B))

theorem fixed_resources (P : ℕ) (B : Body) :
    (machine P B).k = 2 ∧ (machine P B).g+1 = 5 ∧ (machine P B).q+1 = (ticks P B+1)*4 := by
  refine ⟨rfl,rfl,?_⟩
  exact native_state_count (schedule P B) (ticks P B) (false,false)

theorem native_complete (P : ℕ) (B : Body) (hc : Correct P B) (w : List Bool) :
    Transpose.stepN (machine P B) w (ticks P B) (Transpose.init (machine P B)) =
      some ((lift (⟨ticks P B,by omega⟩ : Fin (ticks P B+1)) (result P B w)).denote
        (encoding P B) (program (schedule P B) (ticks P B))) ∧
    Transpose.step (machine P B) w
      ((lift (⟨ticks P B,by omega⟩ : Fin (ticks P B+1)) (result P B w)).denote
        (encoding P B) (program (schedule P B) (ticks P B))) = none := by
  have h := native_run_and_halt (encoding P B) (schedule P B) w RawMaskedStride.initial
    (fun i _ => schedule_active P B hc.active i _)
  rw [schedule_exact P B hc] at h
  have hb : (lift (⟨0,by omega⟩ : Fin (ticks P B+1)) RawMaskedStride.initial).denote
      (encoding P B) (program (schedule P B) (ticks P B)) = Transpose.init (machine P B) :=
    NativeIO.blank_denote (encoding P B) _ _ (NativeMicrocode.initialEncoding_start _)
  rw [hb] at h
  exact h

theorem native_halts (P : ℕ) (B : Body) (hc : Correct P B) (w : List Bool) :
    Transpose.Tape.HaltsAt (machine P B) w (ticks P B) := by
  obtain ⟨hs,hh⟩ := native_complete P B hc w
  have hr := (Transpose.Tape.Impl.stepN_init_eq_some_iff (ticks P B) _).mp hs
  refine ⟨hr.1,(Transpose.Tape.Impl.step_run_eq_none_iff (ticks P B)).mp ?_⟩
  rw [hr.2]
  exact hh

theorem native_correct (P : ℕ) (B : Body) (hc : Correct P B) (w : List Bool) :
    Transpose.Tape.HaltsAt (machine P B) w (ticks P B) ∧
    (Transpose.Tape.run (machine P B) w (ticks P B)).outRev.reverse = outputWord P B w ∧
    ∀ z, (Transpose.Tape.run (machine P B) w (ticks P B)).work ((encoding P B).port 1) z = 0 := by
  have hr := ((Transpose.Tape.Impl.stepN_init_eq_some_iff (ticks P B) _).mp
    (native_complete P B hc w).1).2
  refine ⟨native_halts P B hc w,?_,?_⟩
  · rw [hr]
    change (result P B w).outRev.reverse = _
    rw [result_output P B hc,List.reverse_reverse]
  · intro z
    rw [hr]
    change NativeMicrocode.symbolCode
      (cells (result P B w) ((encoding P B).port.symm ((encoding P B).port 1)) z) = 0
    rw [Equiv.symm_apply_apply,result,ScheduledRawOutput.emitted_cells,(ready_spec P B hc w).2.2.1]
    rfl

end TransposeFollowup.RawBankProgram
