import TransposeFollowup.BinaryBankOperation

/-! Finite words of forward masked-stride operations on one work bank.
The public parameters are unrestricted functions of the problem size.
The shared schedule and bank-invariant compiler also serves mixed words;
this specialization retains its prefix dependence and sharper time bound. -/
namespace TransposeFollowup.MaskedStrideWord
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
set_option autoImplicit false

structure Operation where
  isPrefix : Bool
  mask : ℕ → Bool
  stride : ℕ

def Valid (P : ℕ) (ops : List Operation) : Prop :=
  ∀ op ∈ ops, 0 < op.stride ∧ op.stride ≤ P

def transform (ops : List Operation) (x : ℕ → Bool) : ℕ → Bool :=
  ScheduledWord.transform (fun op => fun x => MaskedStrideScan.value op.isPrefix op.mask x op.stride) ops x

def ticks (P : ℕ) (ops : List Operation) : ℕ :=
  ScheduledWord.ticks (fun op => MaskedStrideBankStage.ticks P op.stride) ops

def schedule (P : ℕ) (ops : List Operation) : ℕ → NativeIO.Program (Fin 2) Mode :=
  ScheduledWord.schedule (fun op => MaskedStrideBankStage.ticks P op.stride)
    (fun op => MaskedStrideBankStage.schedule op.isPrefix op.mask P op.stride) (action 0 ⟨none,.stay⟩) ops

def result (P : ℕ) (ops : List Operation) (w : List Bool) (c : State) : State :=
  ScheduledWord.transform (fun op => MaskedStrideBankStage.result op.isPrefix op.mask P op.stride w) ops c

theorem transform_congr_upto {P : ℕ} {ops : List Operation} (hv : Valid P ops)
    (x y : ℕ → Bool) (n : ℕ) (hxy : ∀ j ≤ n, x j = y j) :
    transform ops x n = transform ops y n := by
  have h := ScheduledWord.transform_rel
    (fun op : Operation => fun z => MaskedStrideScan.value op.isPrefix op.mask z op.stride)
    (fun op : Operation => fun z => MaskedStrideScan.value op.isPrefix op.mask z op.stride)
    ops (fun a b => ∀ j≤n, a j=b j) x y hxy (by
      intro op hop a b hab j hj
      exact MaskedStrideScan.value_congr_upto op.isPrefix op.mask a b (hv op hop).1 j
        (fun k hk => hab k (hk.trans hj)))
  exact h n le_rfl

theorem schedule_active (P : ℕ) (ops : List Operation) (i : ℕ) (c : State) :
    NativeIO.Active (schedule P ops i) c := by
  exact ScheduledWord.schedule_active _ _ _ ops c i (ScheduledTapeAction.active _ _ _)
    (fun op _ j => MaskedStrideBankStage.schedule_active op.isPrefix op.mask P op.stride j c)

theorem schedule_exact (P : ℕ) (ops : List Operation) (hv : Valid P ops)
    (w : List Bool) (c : State) : trajectory (schedule P ops) w c (ticks P ops) = result P ops w c := by
  exact ScheduledWord.schedule_exact _ _ _ _ ops w c
    (fun op hop d => MaskedStrideBankStage.schedule_exact op.isPrefix op.mask P (hv op hop).1 w d)

theorem ticks_le (P : ℕ) (ops : List Operation) (hv : Valid P ops) :
    ticks P ops ≤ 11*P*ops.length := by
  exact ScheduledWord.ticks_le _ ops (11*P)
    (fun op hop => MaskedStrideBankStage.ticks_le P op.stride (hv op hop).2)

theorem result_spec (P : ℕ) (ops : List Operation) (hv : Valid P ops)
    (w : List Bool) (c : State) (hblank : ∀ z, cells c 1 z = .blank) :
    (∀ t, (result P ops w c).work.pos t = c.work.pos t) ∧
    (∀ j < P, bit (cells (result P ops w c) 0 (c.work.pos 0+j)) =
      transform ops (MaskedStrideScan.input c) j) ∧
    (∀ z, cells (result P ops w c) 1 z = .blank) ∧
    (result P ops w c).inputPos = c.inputPos ∧ (result P ops w c).outRev = c.outRev := by
  exact BankWord.word_spec BankWord.binary P
    (fun op : Operation => MaskedStrideBankStage.result op.isPrefix op.mask P op.stride w)
    (fun op : Operation => fun x => MaskedStrideScan.value op.isPrefix op.mask x op.stride) ops c hblank
    (fun op hop d hd => BinaryBankOperation.result_spec P (.forward op.isPrefix op.mask op.stride) (hv op hop) w d hd)
    (fun op hop => BinaryBankOperation.value_congr P (.forward op.isPrefix op.mask op.stride) (hv op hop))

end TransposeFollowup.MaskedStrideWord
