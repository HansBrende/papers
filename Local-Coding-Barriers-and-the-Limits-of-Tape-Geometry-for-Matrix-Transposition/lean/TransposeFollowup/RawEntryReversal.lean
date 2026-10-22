import TransposeFollowup.ScheduledBankRowsInvariant
import TransposeFollowup.RawBlockReversal

/-! Reverse the order of b-symbol entries separately inside each row.
This is the C operation in both exact palettes. The already verified
block reversal supplies the row update, and the shared sequential-row
wrapper pays for advances and the final rewind. All symbols survive. -/
namespace TransposeFollowup.RawEntryReversal
open Classical FixedTapeCompiler ScheduledNativeIO
open SharedBankSymbols
set_option autoImplicit false

def update (b d : ℕ) : ScheduledBankRows.Update SharedRowBank.Mode (d*b) where
  cost := BankBlockReversal.ticks b d
  code := RawBlockReversal.schedule b d
  value := BankBlockReversal.value b d
  congruent := BankBlockReversal.value_congr b d
  active := RawBlockReversal.schedule_active b d
  endpoint := by
    intro w c t
    rw [RawBlockReversal.schedule,BankBlockReversal.schedule_exact]
    exact BankBlockReversal.result_positions read write reset b d w c t
  represents := RawBlockReversal.represents b d
  frame := by
    intro w c z hz
    rw [RawBlockReversal.schedule,BankBlockReversal.schedule_exact]
    exact BankBlockReversal.result_bank_outside read write reset b d w c z hz

def internalTicks (b d r : ℕ) : ℕ := ScheduledBankRows.ticks (update b d) r

def schedule (b d r : ℕ) : ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode :=
  ScheduledBankRows.schedule (update b d) r

def index (b d j : ℕ) : ℕ := (j/(d*b))*(d*b)+BankBlockReversal.index b d (j%(d*b))

def value (b d : ℕ) (x : ℕ → CopyMachine.Sym Bool) (j : ℕ) : CopyMachine.Sym Bool :=
  x (index b d j)

theorem index_entry (b d k l j : ℕ) (hl : l<d) (hj : j<b) :
    index b d (k*(d*b)+(l*b+j))=k*(d*b)+(d-1-l)*b+j := by
  have hb : 0<b := Nat.zero_lt_of_lt hj
  have hW : 0<d*b := Nat.mul_pos (Nat.zero_lt_of_lt hl) hb
  have hu : l*b+j<d*b := by
    have := Nat.mul_le_mul_right b hl
    nlinarith
  have hdiv : (k*(d*b)+(l*b+j))/(d*b)=k := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hW,Nat.div_eq_of_lt hu,zero_add]
  have hmod : (k*(d*b)+(l*b+j))%(d*b)=l*b+j := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hu]
  have hdivb : (l*b+j)/b=l := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hb,Nat.div_eq_of_lt hj,zero_add]
  simp only [index,hdiv,hmod,BankBlockReversal.index,hdivb,Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt hj,add_assoc]

theorem value_congr (b d r : ℕ) : BankWord.Congruent (r*(d*b)) (value b d) :=
  ScheduledBankRows.value_congr (update b d) r

theorem schedule_active (b d r i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (schedule b d r i) c := ScheduledBankRows.schedule_active (update b d) r i c

theorem represents (b d r : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (r*(d*b)) c
      (trajectory (schedule b d r) w c (internalTicks b d r))
      (value b d (BankWord.input BankWord.symbols c)) := by
  rw [schedule,internalTicks,ScheduledBankRows.schedule_exact]
  exact ScheduledBankRows.represents (update b d) r w c hc

theorem internal_ticks_eq (b d r : ℕ) : internalTicks b d r=12*(r*(d*b)) := by
  simp only [internalTicks,ScheduledBankRows.ticks,update,BankBlockReversal.ticks_eq]
  ring

def ticks (b d r : ℕ) : ℕ := RawProgramShell.ticks (r*(d*b)) (internalTicks b d r)

noncomputable def machine (b d r : ℕ) :=
  RawProgramShell.machine SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r) (schedule b d r)

def output (b d r : ℕ) (w : List Bool) : List Bool :=
  (List.range (r*(d*b))).map (fun j => ScheduledRawInput.inputBit w (index b d j))

theorem ticks_eq (b d r : ℕ) : ticks b d r=19*(r*(d*b)) := by
  rw [ticks,RawProgramShell.ticks_eq,internal_ticks_eq]
  omega

theorem native_correct (b d r : ℕ) (w : List Bool) :
    ∃ c : Transpose.Config (machine b d r),
      Transpose.stepN (machine b d r) w (ticks b d r) (Transpose.init (machine b d r))=some c ∧
      Transpose.step (machine b d r) w c=none ∧ c.outRev=(output b d r w).reverse ∧
      ∀ z, c.work ((RawProgramShell.encoding SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)).port 1) z=0 := by
  exact RawProgramShell.native_correct SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)
    (schedule b d r) (schedule_active b d r) (value b d) (value_congr b d r)
    (fun w c hc => represents b d r w c hc) w

theorem resources (b d r : ℕ) :
    (machine b d r).k=2 ∧ (machine b d r).g+1=5 ∧ (machine b d r).q+1=(ticks b d r+1)*200 := by
  have h := RawProgramShell.fixed_resources SharedRowBank.initialRowMode (r*(d*b))
    (internalTicks b d r) (schedule b d r)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

end TransposeFollowup.RawEntryReversal
