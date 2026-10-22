import TransposeFollowup.RawRowProgram

/-! One raw native executor for a word of exact-symbol bank operations.
Input is loaded once and Boolean projection occurs only after the last
operation. Intermediate trits are never projected away. -/
namespace TransposeFollowup.RawSymbolWord
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
set_option autoImplicit false
variable {O : Type*}

structure Correct (P : ℕ) (cost : O → ℕ)
    (code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode)
    (value : O → (ℕ → Sym Bool) → ℕ → Sym Bool) : Prop where
  active : ∀ op i c, NativeIO.Active (code op i) c
  congruent : ∀ op, BankWord.Congruent P (value op)
  represents : ∀ op w c, BankWord.symbols.clean c →
    BankWord.Represents BankWord.symbols P c (trajectory (code op) w c (cost op))
      (value op (BankWord.input BankWord.symbols c))

def bodySchedule (cost : O → ℕ) (code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode)
    (ops : List O) := ScheduledWord.schedule cost code (ScheduledTapeAction.action 0 ⟨none,.stay⟩) ops

def transform (value : O → (ℕ → Sym Bool) → ℕ → Sym Bool) (ops : List O) :=
  ScheduledWord.transform value ops

def ticks (P : ℕ) (cost : O → ℕ) (ops : List O) : ℕ :=
  RawProgramShell.ticks P (ScheduledWord.ticks cost ops)

noncomputable def machine (P : ℕ) (cost : O → ℕ)
    (code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode) (ops : List O) :=
  RawProgramShell.machine SharedRowBank.initialRowMode P (ScheduledWord.ticks cost ops)
    (bodySchedule cost code ops)

def output (P : ℕ) (value : O → (ℕ → Sym Bool) → ℕ → Sym Bool)
    (ops : List O) (w : List Bool) : List Bool :=
  (List.range P).map (fun j => MaskedStrideCell.bit
    (transform value ops (fun i => .data (ScheduledRawInput.inputBit w i)) j))

theorem body_active {P : ℕ} {cost : O → ℕ}
    {code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode}
    {value : O → (ℕ → Sym Bool) → ℕ → Sym Bool}
    (h : Correct P cost code value) (ops : List O) (i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (bodySchedule cost code ops i) c :=
  ScheduledWord.schedule_active cost code _ ops c i (ScheduledTapeAction.active _ _ _)
    (fun op _ j => h.active op j c)

theorem transform_congr {P : ℕ} {cost : O → ℕ}
    {code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode}
    {value : O → (ℕ → Sym Bool) → ℕ → Sym Bool}
    (h : Correct P cost code value) (ops : List O) : BankWord.Congruent P (transform value ops) :=
  BankWord.transform_congr P value ops (fun op _ => h.congruent op)

theorem body_represents {P : ℕ} {cost : O → ℕ}
    {code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode}
    {value : O → (ℕ → Sym Bool) → ℕ → Sym Bool}
    (h : Correct P cost code value) (ops : List O) (w : List Bool)
    (c : SharedRowBank.State) (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols P c
      (trajectory (bodySchedule cost code ops) w c (ScheduledWord.ticks cost ops))
      (transform value ops (BankWord.input BankWord.symbols c)) := by
  rw [bodySchedule,ScheduledWord.schedule_exact cost code _
    (fun op d => trajectory (code op) w d (cost op)) ops w c (fun _ _ _ => rfl)]
  exact BankWord.word_spec BankWord.symbols P _ value ops c hc
    (fun op _ d hd => h.represents op w d hd) (fun op _ => h.congruent op)

theorem ticks_le (P : ℕ) (cost : O → ℕ) (ops : List O) (C : ℕ)
    (hc : ∀ op ∈ ops, cost op ≤ C*P) : ticks P cost ops ≤ (7+C*ops.length)*P := by
  have h := ScheduledWord.ticks_le cost ops (C*P) hc
  rw [ticks,RawProgramShell.ticks_eq]
  nlinarith

theorem native_correct {P : ℕ} {cost : O → ℕ}
    {code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode}
    {value : O → (ℕ → Sym Bool) → ℕ → Sym Bool}
    (h : Correct P cost code value) (ops : List O) (w : List Bool) :
    ∃ c : Transpose.Config (machine P cost code ops),
      Transpose.stepN (machine P cost code ops) w (ticks P cost ops)
        (Transpose.init (machine P cost code ops))=some c ∧
      Transpose.step (machine P cost code ops) w c=none ∧
      c.outRev=(output P value ops w).reverse ∧
      ∀ z, c.work ((RawProgramShell.encoding SharedRowBank.initialRowMode P
        (ScheduledWord.ticks cost ops)).port 1) z=0 :=
  RawProgramShell.native_correct SharedRowBank.initialRowMode P (ScheduledWord.ticks cost ops)
    (bodySchedule cost code ops) (body_active h ops) (transform value ops) (transform_congr h ops)
    (fun w c hc => body_represents h ops w c hc) w

theorem resources (P : ℕ) (cost : O → ℕ)
    (code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode) (ops : List O) :
    (machine P cost code ops).k=2 ∧ (machine P cost code ops).g+1=5 ∧
    (machine P cost code ops).q+1=(ticks P cost ops+1)*200 := by
  have h := RawProgramShell.fixed_resources SharedRowBank.initialRowMode P (ScheduledWord.ticks cost ops)
    (bodySchedule cost code ops)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

end TransposeFollowup.RawSymbolWord
