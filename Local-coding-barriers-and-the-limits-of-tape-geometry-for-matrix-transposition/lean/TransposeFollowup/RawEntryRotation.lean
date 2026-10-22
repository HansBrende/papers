import TransposeFollowup.BankSymbolRotation
import TransposeFollowup.IndexedBankRowsInvariant
import TransposeFollowup.IndexedBankRowsMotion

/-! Row k is rotated by k whole b-symbol entries, in either direction.
The indexed wrapper pays for every row update, advance and final rewind.
All symbols are preserved, so b=1 also supplies the ternary E/e pair. -/
namespace TransposeFollowup.RawEntryRotation
open Classical FixedTapeCompiler ScheduledNativeIO
set_option autoImplicit false

def offset (sub : Bool) (d k : ℕ) : ℕ :=
  if d=0 then 0 else if sub then d-k%d else k%d

theorem offset_le (sub : Bool) (d k : ℕ) : offset sub d k ≤ d := by
  unfold offset
  split
  · omega
  · split
    · exact Nat.sub_le _ _
    · exact (Nat.mod_lt _ (by omega)).le

def update (sub : Bool) (b d k : ℕ) : ScheduledBankRows.Update SharedRowBank.Mode (d*b) :=
  BankSymbolRotation.update (d*b) (offset sub d k*b)
    (Nat.mul_le_mul_right b (offset_le sub d k))

theorem update_cost (sub : Bool) (b d k : ℕ) : (update sub b d k).cost+d*b=23*(d*b) := by
  change BankSymbolRotation.ticks (d*b) (offset sub d k*b)+d*b=23*(d*b)
  rw [BankSymbolRotation.ticks_eq _ _ (Nat.mul_le_mul_right b (offset_le sub d k))]
  omega

def internalTicks (sub : Bool) (b d r : ℕ) : ℕ := IndexedBankRows.ticks (update sub b d) r

def schedule (sub : Bool) (b d r : ℕ) : ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode :=
  IndexedBankRows.schedule (update sub b d) r

def index (sub : Bool) (b d j : ℕ) : ℕ :=
  (j/(d*b))*(d*b)+(j%(d*b)+offset sub d (j/(d*b))*b)%(d*b)

def value (sub : Bool) (b d : ℕ) (x : ℕ → CopyMachine.Sym Bool) (j : ℕ) : CopyMachine.Sym Bool :=
  x (index sub b d j)

theorem index_entry (sub : Bool) (b d k l j : ℕ) (hl : l<d) (hj : j<b) :
    index sub b d (k*(d*b)+(l*b+j))=k*(d*b)+((l+offset sub d k)%d)*b+j := by
  have hb : 0<b := Nat.zero_lt_of_lt hj
  have hd : 0<d := Nat.zero_lt_of_lt hl
  have hW : 0<d*b := Nat.mul_pos hd hb
  have hu : l*b+j<d*b := by
    have := Nat.mul_le_mul_right b hl
    nlinarith
  have hdiv : (k*(d*b)+(l*b+j))/(d*b)=k := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hW,Nat.div_eq_of_lt hu,zero_add]
  have hmod : (k*(d*b)+(l*b+j))%(d*b)=l*b+j := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hu]
  have hrem : ((l+offset sub d k)%d)*b+j<d*b := by
    have := Nat.mul_le_mul_right b (Nat.mod_lt (l+offset sub d k) hd)
    nlinarith
  simp only [index,hdiv,hmod]
  rw [show l*b+j+offset sub d k*b=(l+offset sub d k)*b+j by ring,
    Nat.add_mod,Nat.mul_mod_mul_right,Nat.mod_eq_of_lt (hj.trans_le (Nat.le_mul_of_pos_left b hd)),
    Nat.mod_eq_of_lt hrem,add_assoc]

theorem index_entry_forward (b d k l j : ℕ) (hl : l<d) (hj : j<b) :
    index false b d (k*(d*b)+(l*b+j))=k*(d*b)+((l+k)%d)*b+j := by
  rw [index_entry false b d k l j hl hj]
  simp only [offset,show d≠0 by omega,ite_false,Bool.false_eq_true,Nat.add_mod_mod]

theorem index_entry_inverse (b d k l j : ℕ) (hl : l<d) (hj : j<b) :
    index true b d (k*(d*b)+(l*b+j))=k*(d*b)+((l+(d-k%d))%d)*b+j := by
  rw [index_entry true b d k l j hl hj]
  simp only [offset,show d≠0 by omega,ite_false,ite_true]

theorem value_congr (sub : Bool) (b d r : ℕ) :
    BankWord.Congruent (r*(d*b)) (value sub b d) :=
  IndexedBankRows.value_congr (update sub b d) r

theorem schedule_active (sub : Bool) (b d r i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (schedule sub b d r i) c :=
  IndexedBankRows.schedule_active (update sub b d) r i c

theorem represents (sub : Bool) (b d r : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (r*(d*b)) c
      (trajectory (schedule sub b d r) w c (internalTicks sub b d r))
      (value sub b d (BankWord.input BankWord.symbols c)) := by
  rw [schedule,internalTicks,IndexedBankRows.schedule_exact]
  exact IndexedBankRows.represents (update sub b d) r w c hc

theorem internal_ticks_eq (sub : Bool) (b d r : ℕ) : internalTicks sub b d r=24*(r*(d*b)) :=
  IndexedBankRows.linear_ticks (update sub b d) r 23 (update_cost sub b d)

def ticks (sub : Bool) (b d r : ℕ) : ℕ := RawProgramShell.ticks (r*(d*b)) (internalTicks sub b d r)

noncomputable def machine (sub : Bool) (b d r : ℕ) :=
  RawProgramShell.machine SharedRowBank.initialRowMode (r*(d*b)) (internalTicks sub b d r) (schedule sub b d r)

def output (sub : Bool) (b d r : ℕ) (w : List Bool) : List Bool :=
  (List.range (r*(d*b))).map (fun j => ScheduledRawInput.inputBit w (index sub b d j))

theorem ticks_eq (sub : Bool) (b d r : ℕ) : ticks sub b d r=31*(r*(d*b)) := by
  rw [ticks,RawProgramShell.ticks_eq,internal_ticks_eq]
  omega

theorem native_correct (sub : Bool) (b d r : ℕ) (w : List Bool) :
    ∃ c : Transpose.Config (machine sub b d r),
      Transpose.stepN (machine sub b d r) w (ticks sub b d r) (Transpose.init (machine sub b d r))=some c ∧
      Transpose.step (machine sub b d r) w c=none ∧ c.outRev=(output sub b d r w).reverse ∧
      ∀ z, c.work ((RawProgramShell.encoding SharedRowBank.initialRowMode (r*(d*b)) (internalTicks sub b d r)).port 1) z=0 := by
  exact RawProgramShell.native_correct SharedRowBank.initialRowMode (r*(d*b)) (internalTicks sub b d r)
    (schedule sub b d r) (schedule_active sub b d r) (value sub b d) (value_congr sub b d r)
    (fun w c hc => represents sub b d r w c hc) w

theorem resources (sub : Bool) (b d r : ℕ) :
    (machine sub b d r).k=2 ∧ (machine sub b d r).g+1=5 ∧
      (machine sub b d r).q+1=(ticks sub b d r+1)*200 := by
  have h := RawProgramShell.fixed_resources SharedRowBank.initialRowMode (r*(d*b))
    (internalTicks sub b d r) (schedule sub b d r)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

end TransposeFollowup.RawEntryRotation
