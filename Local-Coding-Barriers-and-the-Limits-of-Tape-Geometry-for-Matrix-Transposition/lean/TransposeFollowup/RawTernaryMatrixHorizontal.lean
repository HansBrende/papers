import TransposeFollowup.BufferedRowUpdate
import TransposeFollowup.TernaryBufferCoordinates
import TransposeFollowup.ScheduledBankRowsInvariant

/-! Full b-trit-entry Q/q. Each physical row runs d paired entry updates
against a b-trit buffer, clears it, and restores its heads. The outer
scheduler then advances to the next row. Different lanes never mix. -/
namespace TransposeFollowup.RawTernaryMatrixHorizontal
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
set_option autoImplicit false

noncomputable def update (sub : Bool) (b d : ℕ) :=
  BufferedRowUpdate.update (TernaryBank.bufferRule sub) b d

def internalTicks (b d r : ℕ) : ℕ := r*(BufferedRowUpdate.ticks b d+d*b)+r*(d*b)

noncomputable def schedule (sub : Bool) (b d r : ℕ) := ScheduledBankRows.schedule (update sub b d) r

def value (sub : Bool) (b d : ℕ) (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool :=
  BufferedRows.bankValue (TernaryBank.bufferRule sub) b d
    (fun i => x ((j/(d*b))*(d*b)+i)) (j%(d*b))

theorem value_entry (sub : Bool) (b d : ℕ) (x : ℕ → Sym Bool)
    (k j l : ℕ) (hj : j<d) (hl : l<b) :
    value sub b d x (k*(d*b)+j*b+l)=
      TernaryBank.encode ((TernaryBank.rowResult sub 0
        (List.ofFn (fun a : Fin d => TernaryBank.decode (x (k*(d*b)+a*b+l))))).getI j) := by
  have hm : j*b+l<d*b := by nlinarith
  have hW : 0<d*b := Nat.zero_lt_of_lt hm
  have hdiv : (k*(d*b)+(j*b+l))/(d*b)=k := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hW,Nat.div_eq_of_lt hm,zero_add]
  rw [Nat.add_assoc,value,hdiv,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hm]
  simpa only [Nat.add_assoc] using TernaryBank.bank_coordinate sub b d
    (fun i => x (k*(d*b)+i)) j l hj hl

theorem value_congr (sub : Bool) (b d r : ℕ) : BankWord.Congruent (r*(d*b)) (value sub b d) :=
  ScheduledBankRows.value_congr (update sub b d) r

theorem schedule_active (sub : Bool) (b d r i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (schedule sub b d r i) c :=
  ScheduledBankRows.schedule_active (update sub b d) r i c

theorem represents (sub : Bool) (b d r : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (r*(d*b)) c
      (trajectory (schedule sub b d r) w c (internalTicks b d r))
      (value sub b d (BankWord.input BankWord.symbols c)) := by
  change BankWord.Represents BankWord.symbols (r*(d*b)) c
    (trajectory (ScheduledBankRows.schedule (update sub b d) r) w c
      (ScheduledBankRows.ticks (update sub b d) r)) _
  rw [ScheduledBankRows.schedule_exact]
  exact ScheduledBankRows.represents (update sub b d) r w c hc

theorem update_cost (sub : Bool) (b d : ℕ) (hb : 0<b) (hd : 0<d) :
    (update sub b d).cost+d*b=11*(d*b) := by
  change BufferedRowUpdate.ticks b d+d*b=11*(d*b)
  rw [BufferedRowUpdate.ticks_eq b d hb hd]
  omega

theorem internal_ticks_eq (b d r : ℕ) (hb : 0<b) (hd : 0<d) :
    internalTicks b d r=12*(r*(d*b)) := by
  rw [internalTicks,BufferedRowUpdate.ticks_eq b d hb hd]
  ring

def ticks (b d r : ℕ) : ℕ := RawProgramShell.ticks (r*(d*b)) (internalTicks b d r)

noncomputable def machine (sub : Bool) (b d r : ℕ) :=
  RawProgramShell.machine SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r) (schedule sub b d r)

def output (sub : Bool) (b d r : ℕ) (w : List Bool) : List Bool :=
  (List.range (r*(d*b))).map (fun j => MaskedStrideCell.bit
    (value sub b d (fun i => .data (ScheduledRawInput.inputBit w i)) j))

theorem ticks_eq (b d r : ℕ) (hb : 0<b) (hd : 0<d) : ticks b d r=19*(r*(d*b)) := by
  rw [ticks,RawProgramShell.ticks_eq,internal_ticks_eq b d r hb hd]
  omega

theorem native_correct (sub : Bool) (b d r : ℕ) (w : List Bool) :
    ∃ c : Transpose.Config (machine sub b d r),
      Transpose.stepN (machine sub b d r) w (ticks b d r) (Transpose.init (machine sub b d r))=some c ∧
      Transpose.step (machine sub b d r) w c=none ∧ c.outRev=(output sub b d r w).reverse ∧
      ∀ z, c.work ((RawProgramShell.encoding SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)).port 1) z=0 :=
  RawProgramShell.native_correct SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)
    (schedule sub b d r) (schedule_active sub b d r) (value sub b d) (value_congr sub b d r)
    (fun w c hc => represents sub b d r w c hc) w

theorem resources (sub : Bool) (b d r : ℕ) :
    (machine sub b d r).k=2 ∧ (machine sub b d r).g+1=5 ∧
    (machine sub b d r).q+1=(ticks b d r+1)*200 := by
  have h := RawProgramShell.fixed_resources SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r) (schedule sub b d r)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

end TransposeFollowup.RawTernaryMatrixHorizontal
