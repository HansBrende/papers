import TransposeFollowup.BankWordInvariant
import TransposeFollowup.BackwardMaskedStride
import TransposeFollowup.BankRotation

/-! Concrete interpretation of the complete binary operation palette.
Every case discharges the shared bank invariant using an actual proved
schedule; arbitrary public masks remain data-independent parameters. -/
namespace TransposeFollowup.BinaryBankOperation
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
set_option autoImplicit false

inductive Operation where
  | forward (isPrefix : Bool) (mask : ℕ → Bool) (stride : ℕ)
  | backward (isPrefix : Bool) (mask : ℕ → Bool) (stride : ℕ)
  | reverse
  | rotate (offset : ℕ)

def Valid (P : ℕ) : Operation → Prop
  | .forward _ _ S | .backward _ _ S => 0<S ∧ S≤P
  | .reverse => True
  | .rotate R => R≤P

def value (P : ℕ) : Operation → (ℕ → Bool) → ℕ → Bool
  | .forward pre mask S => fun x => MaskedStrideScan.value pre mask x S
  | .backward pre mask S => fun x => BackwardMaskedStride.value pre mask x P S
  | .reverse => BackwardMaskedStride.reflected P
  | .rotate R => BankRotation.value P R

def ticks (P : ℕ) : Operation → ℕ
  | .forward _ _ S => MaskedStrideBankStage.ticks P S
  | .backward _ _ S => BackwardMaskedStride.ticks P S
  | .reverse => BankReversal.ticks P
  | .rotate R => BankRotation.ticks P R

def schedule (P : ℕ) : Operation → ℕ → NativeIO.Program (Fin 2) Mode
  | .forward pre mask S => MaskedStrideBankStage.schedule pre mask P S
  | .backward pre mask S => BackwardMaskedStride.schedule pre mask P S
  | .reverse => BankReversal.schedule P
  | .rotate R => BankRotation.schedule P R

def result (P : ℕ) : Operation → List Bool → State → State
  | .forward pre mask S => MaskedStrideBankStage.result pre mask P S
  | .backward pre mask S => BackwardMaskedStride.result pre mask P S
  | .reverse => BankReversal.result P
  | .rotate R => BankRotation.result P R

theorem value_congr (P : ℕ) (op : Operation) (hv : Valid P op) : BankWord.Congruent P (value P op) := by
  intro x y hxy j hj
  cases op with
  | forward pre mask S =>
    exact MaskedStrideScan.value_congr_upto pre mask x y hv.1 j (fun k hk => hxy k (hk.trans_lt hj))
  | backward pre mask S => exact BackwardMaskedStride.value_congr pre mask x y P hv.1 j hj hxy
  | reverse => exact hxy (P-1-j) (by omega)
  | rotate R => exact BankRotation.value_congr (by omega) R x y hxy j

theorem schedule_active (P : ℕ) (op : Operation) (i : ℕ) (c : State) :
    NativeIO.Active (schedule P op i) c := by
  cases op with
  | forward pre mask S => exact MaskedStrideBankStage.schedule_active pre mask P S i c
  | backward pre mask S => exact BackwardMaskedStride.schedule_active pre mask P S i c
  | reverse => exact BankReversal.schedule_active P i c
  | rotate R => exact BankRotation.schedule_active P R i c

theorem schedule_exact (P : ℕ) (op : Operation) (hv : Valid P op) (w : List Bool) (c : State) :
    trajectory (schedule P op) w c (ticks P op)=result P op w c := by
  cases op with
  | forward pre mask S => exact MaskedStrideBankStage.schedule_exact pre mask P hv.1 w c
  | backward pre mask S => exact BackwardMaskedStride.schedule_exact pre mask P hv.1 w c
  | reverse => exact BankReversal.schedule_exact P w c
  | rotate R => exact BankRotation.schedule_exact P R w c

theorem ticks_le {P : ℕ} (hP : 0<P) (op : Operation) (hv : Valid P op) : ticks P op≤27*P := by
  cases op with
  | forward pre mask S => exact (MaskedStrideBankStage.ticks_le P S hv.2).trans (by omega)
  | backward pre mask S => exact BackwardMaskedStride.ticks_le P hv.1 hv.2
  | reverse => simp only [ticks,BankReversal.ticks_eq]; omega
  | rotate R => exact (BankRotation.ticks_le hP R hv).trans (by omega)

theorem result_spec (P : ℕ) (op : Operation) (hv : Valid P op) (w : List Bool) (c : State)
    (hblank : BankWord.binary.clean c) :
    BankWord.Represents BankWord.binary P c (result P op w c) (value P op (BankWord.input BankWord.binary c)) := by
  have lift (d : State) (f : ℕ → Bool)
      (h : (∀ t, d.work.pos t=c.work.pos t) ∧
        (∀ j<P, cells d 0 (c.work.pos 0+j)=.data (f j)) ∧
        (∀ z, cells d 1 z=.blank) ∧ d.inputPos=c.inputPos ∧ d.outRev=c.outRev) :
      BankWord.Represents BankWord.binary P c d f := by
    refine ⟨h.1,?_,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
    intro j hj
    change bit (cells d 0 (c.work.pos 0+j))=f j
    rw [h.2.1 j hj]; rfl
  cases op with
  | forward pre mask S => exact lift _ _ (MaskedStrideBankStage.result_spec pre mask P hv.1 w c hblank)
  | backward pre mask S => exact lift _ _ (BackwardMaskedStride.result_spec pre mask P hv.1 w c hblank)
  | reverse => exact lift _ _ (BankReversal.result_spec P w c hblank)
  | rotate R => exact lift _ _ (BankRotation.result_spec P R hv w c hblank)

end TransposeFollowup.BinaryBankOperation
