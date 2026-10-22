import TransposeFollowup.BankReversal
import TransposeFollowup.MaskedStrideBankStage

/-! Backward masked scans are implemented by two paid bank reversals
around the existing forward scan. Their recurrence refers to j+S, with
zero filling beyond the right bank boundary. -/
namespace TransposeFollowup.BackwardMaskedStride
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
set_option autoImplicit false

def reflected (P : ℕ) (x : ℕ → Bool) (j : ℕ) : Bool := x (P-1-j)

def value (isPrefix : Bool) (mask x : ℕ → Bool) (P S j : ℕ) : Bool :=
  MaskedStrideScan.value isPrefix (reflected P mask) (reflected P x) S (P-1-j)

theorem value_recurrence (isPrefix : Bool) (mask x : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0<S) (j : ℕ) (hj : j<P) :
    value isPrefix mask x P S j=MaskedStrideCell.output (mask j) (x j)
      (if j+S<P then if isPrefix then value isPrefix mask x P S (j+S) else x (j+S) else false) := by
  have he : P-1-(P-1-j)=j := Nat.sub_sub_self (by omega)
  rw [value,MaskedStrideScan.value_recurrence isPrefix (reflected P mask) (reflected P x) hS]
  simp only [reflected,he]
  by_cases h : j+S<P
  · rw [ite_eq_left h,ite_eq_right (by omega : ¬P-1-j<S)]
    have hk : P-1-j-S=P-1-(j+S) := by omega
    have he' : P-1-(P-1-(j+S))=j+S := Nat.sub_sub_self (by omega)
    cases isPrefix <;> simp [value,hk,he']
  · rw [ite_eq_right h,ite_eq_left (by omega : P-1-j<S)]

theorem value_congr (isPrefix : Bool) (mask x y : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0<S) (j : ℕ) (hj : j<P) (hxy : ∀ k<P, x k=y k) :
    value isPrefix mask x P S j=value isPrefix mask y P S j := by
  apply MaskedStrideScan.value_congr_upto isPrefix (reflected P mask) _ _ hS
  intro k _
  exact hxy (P-1-k) (by omega)

def ticks (P S : ℕ) : ℕ := BankReversal.ticks P+(MaskedStrideBankStage.ticks P S+BankReversal.ticks P)

def schedule (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  append (BankReversal.schedule P)
    (append (MaskedStrideBankStage.schedule isPrefix (reflected P mask) P S)
      (BankReversal.schedule P) (MaskedStrideBankStage.ticks P S)) (BankReversal.ticks P)

def result (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) (c : State) : State :=
  BankReversal.result P w
    (MaskedStrideBankStage.result isPrefix (reflected P mask) P S w (BankReversal.result P w c))

theorem schedule_active (isPrefix : Bool) (mask : ℕ → Bool) (P S i : ℕ) (c : State) :
    NativeIO.Active (schedule isPrefix mask P S i) c := by
  unfold schedule
  apply append_active
  · intro j; exact BankReversal.schedule_active P j c
  · intro j
    apply append_active
    · intro k; exact MaskedStrideBankStage.schedule_active _ _ _ _ k c
    · intro k; exact BankReversal.schedule_active P k c

theorem schedule_exact (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0<S) (w : List Bool) (c : State) :
    trajectory (schedule isPrefix mask P S) w c (ticks P S)=result isPrefix mask P S w c := by
  simp only [schedule,ticks,append_exact,BankReversal.schedule_exact,
    MaskedStrideBankStage.schedule_exact isPrefix (reflected P mask) P hS,result]

theorem ticks_le (P : ℕ) {S : ℕ} (hS : 0<S) (hSP : S≤P) : ticks P S≤27*P := by
  have h := MaskedStrideBankStage.ticks_le P S hSP
  simp only [ticks,BankReversal.ticks_eq]
  omega

theorem result_spec (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) (c : State) (hblank : ∀ z, cells c 1 z=.blank) :
    (∀ t, (result isPrefix mask P S w c).work.pos t=c.work.pos t) ∧
    (∀ j<P, cells (result isPrefix mask P S w c) 0 (c.work.pos 0+j)=
      .data (value isPrefix mask (MaskedStrideScan.input c) P S j)) ∧
    (∀ z, cells (result isPrefix mask P S w c) 1 z=.blank) ∧
    (result isPrefix mask P S w c).inputPos=c.inputPos ∧
    (result isPrefix mask P S w c).outRev=c.outRev := by
  have ha := BankReversal.result_spec P w c hblank
  have hb := MaskedStrideBankStage.result_spec isPrefix (reflected P mask) P hS w
    (BankReversal.result P w c) ha.2.2.1
  have hc := BankReversal.result_spec P w
    (MaskedStrideBankStage.result isPrefix (reflected P mask) P S w (BankReversal.result P w c)) hb.2.2.1
  refine ⟨fun t => (hc.1 t).trans ((hb.1 t).trans (ha.1 t)),?_,hc.2.2.1,
    hc.2.2.2.1.trans (hb.2.2.2.1.trans ha.2.2.2.1),
    hc.2.2.2.2.trans (hb.2.2.2.2.trans ha.2.2.2.2)⟩
  intro j hj
  have hout := hc.2.1 j hj
  rw [hb.1 0,ha.1 0] at hout
  rw [show cells (result isPrefix mask P S w c) 0 (c.work.pos 0+j)=_ from hout]
  have hmid := hb.2.1 (P-1-j) (by omega)
  rw [ha.1 0] at hmid
  rw [hmid]
  change CopyMachine.Sym.data (MaskedStrideScan.value isPrefix (reflected P mask)
    (MaskedStrideScan.input (BankReversal.result P w c)) S (P-1-j))=
    CopyMachine.Sym.data (MaskedStrideScan.value isPrefix (reflected P mask)
      (reflected P (MaskedStrideScan.input c)) S (P-1-j))
  congr 1
  apply MaskedStrideScan.value_congr_upto isPrefix (reflected P mask) _ _ hS
  intro k _
  change bit (cells (BankReversal.result P w c) 0 ((BankReversal.result P w c).work.pos 0+k))=_
  rw [ha.1 0,ha.2.1 k (by omega)]
  rfl

end TransposeFollowup.BackwardMaskedStride
