import TransposeFollowup.BinaryBankOperation

/-! Arbitrary finite mixed words on the same binary bank. All four
operation types use the shared schedule/fold compiler and the concrete
bank invariants already proved for each operation. -/
namespace TransposeFollowup.MixedBinaryWord
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
open BinaryBankOperation (Operation)
set_option autoImplicit false

def Valid (P : ℕ) (ops : List Operation) : Prop := ∀ op ∈ ops, BinaryBankOperation.Valid P op

def transform (P : ℕ) (ops : List Operation) (x : ℕ → Bool) : ℕ → Bool :=
  ScheduledWord.transform (BinaryBankOperation.value P) ops x

def ticks (P : ℕ) (ops : List Operation) : ℕ := ScheduledWord.ticks (BinaryBankOperation.ticks P) ops

def schedule (P : ℕ) (ops : List Operation) : ℕ → NativeIO.Program (Fin 2) Mode :=
  ScheduledWord.schedule (BinaryBankOperation.ticks P) (BinaryBankOperation.schedule P) (action 0 ⟨none,.stay⟩) ops

def result (P : ℕ) (ops : List Operation) (w : List Bool) (c : State) : State :=
  ScheduledWord.transform (fun op => BinaryBankOperation.result P op w) ops c

theorem transform_congr (P : ℕ) (ops : List Operation) (hv : Valid P ops) :
    BankWord.Congruent P (transform P ops) :=
  BankWord.transform_congr P _ ops (fun op hop => BinaryBankOperation.value_congr P op (hv op hop))

theorem schedule_active (P : ℕ) (ops : List Operation) (i : ℕ) (c : State) :
    NativeIO.Active (schedule P ops i) c :=
  ScheduledWord.schedule_active _ _ _ ops c i (ScheduledTapeAction.active _ _ _)
    (fun op _ j => BinaryBankOperation.schedule_active P op j c)

theorem schedule_exact (P : ℕ) (ops : List Operation) (hv : Valid P ops) (w : List Bool) (c : State) :
    trajectory (schedule P ops) w c (ticks P ops)=result P ops w c :=
  ScheduledWord.schedule_exact _ _ _ _ ops w c
    (fun op hop d => BinaryBankOperation.schedule_exact P op (hv op hop) w d)

theorem ticks_le {P : ℕ} (hP : 0<P) (ops : List Operation) (hv : Valid P ops) :
    ticks P ops≤27*P*ops.length :=
  ScheduledWord.ticks_le _ ops (27*P) (fun op hop => BinaryBankOperation.ticks_le hP op (hv op hop))

theorem result_spec (P : ℕ) (ops : List Operation) (hv : Valid P ops) (w : List Bool) (c : State)
    (hblank : ∀ z, cells c 1 z=.blank) :
    (∀ t, (result P ops w c).work.pos t=c.work.pos t) ∧
    (∀ j<P, bit (cells (result P ops w c) 0 (c.work.pos 0+j))=
      transform P ops (BankWord.input BankWord.binary c) j) ∧
    (∀ z, cells (result P ops w c) 1 z=.blank) ∧
    (result P ops w c).inputPos=c.inputPos ∧ (result P ops w c).outRev=c.outRev :=
  BankWord.word_spec BankWord.binary P (fun op => BinaryBankOperation.result P op w)
    (BinaryBankOperation.value P) ops c hblank
    (fun op hop d hd => BinaryBankOperation.result_spec P op (hv op hop) w d hd)
    (fun op hop => BinaryBankOperation.value_congr P op (hv op hop))

end TransposeFollowup.MixedBinaryWord
