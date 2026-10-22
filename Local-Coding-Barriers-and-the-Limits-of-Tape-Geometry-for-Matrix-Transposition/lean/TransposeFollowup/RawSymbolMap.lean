import TransposeFollowup.BufferedSymbolMap
import TransposeFollowup.BufferedRowUpdate
import TransposeFollowup.IndexedBankRowsInvariant
import TransposeFollowup.IndexedBankRowsMotion

/-! Arbitrary public, position-dependent finite symbol maps. Each one-cell
update uses the existing paid executor; the indexed scheduler advances and
rewinds. Tables are public nonuniform clock data, not input-side oracles. -/
namespace TransposeFollowup.RawSymbolMap
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
set_option autoImplicit false

noncomputable def update (f : ℕ → Sym Bool → Sym Bool) (k : ℕ) :
    ScheduledBankRows.Update SharedRowBank.Mode 1 :=
  BufferedRowUpdate.update (BufferedRows.mapRule (f k)) 1 1

theorem update_cost (f : ℕ → Sym Bool → Sym Bool) (k : ℕ) :
    (update f k).cost+1=11 := by
  change BufferedRowUpdate.ticks 1 1+1=11
  rw [BufferedRowUpdate.ticks_eq 1 1 (by decide) (by decide)]

noncomputable def internalTicks (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) : ℕ :=
  IndexedBankRows.ticks (update f) P

noncomputable def schedule (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) :=
  IndexedBankRows.schedule (update f) P

def value (f : ℕ → Sym Bool → Sym Bool) (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool := f j (x j)

theorem indexed_value (f : ℕ → Sym Bool → Sym Bool) (x : ℕ → Sym Bool) (j : ℕ) :
    IndexedBankRows.value (update f) x j=value f x j := by
  simp only [IndexedBankRows.value,Nat.div_one,Nat.mul_one,Nat.mod_one]
  change BufferedRows.bankValue (BufferedRows.mapRule (f j)) 1 1 (fun i => x (j+i)) 0=f j (x j)
  rw [BufferedRows.map_bankValue _ _ _ _ _ (by decide),Nat.add_zero]

theorem value_congr (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) :
    BankWord.Congruent P (value f) := by
  intro x y h j hj
  exact congrArg (f j) (h j hj)

theorem schedule_active (f : ℕ → Sym Bool → Sym Bool) (P i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (schedule f P i) c := IndexedBankRows.schedule_active (update f) P i c

theorem represents (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) (w : List Bool)
    (c : SharedRowBank.State) (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols P c
      (trajectory (schedule f P) w c (internalTicks f P))
      (value f (BankWord.input BankWord.symbols c)) := by
  rw [schedule,internalTicks,IndexedBankRows.schedule_exact]
  have hv : IndexedBankRows.value (update f)=value f := by
    funext x j
    exact indexed_value f x j
  simpa only [Nat.mul_one,hv] using IndexedBankRows.represents (update f) P w c hc

theorem internal_ticks_eq (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) : internalTicks f P=12*P := by
  unfold internalTicks
  simpa only [Nat.mul_one] using IndexedBankRows.linear_ticks (update f) P 11 (update_cost f)

noncomputable def ticks (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) : ℕ :=
  RawProgramShell.ticks P (internalTicks f P)

noncomputable def machine (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) :=
  RawProgramShell.machine SharedRowBank.initialRowMode P (internalTicks f P) (schedule f P)

def output (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) (w : List Bool) : List Bool :=
  (List.range P).map (fun j => MaskedStrideCell.bit (f j (.data (ScheduledRawInput.inputBit w j))))

theorem ticks_eq (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) : ticks f P=19*P := by
  rw [ticks,RawProgramShell.ticks_eq,internal_ticks_eq]
  omega

theorem native_correct (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) (w : List Bool) :
    ∃ c : Transpose.Config (machine f P),
      Transpose.stepN (machine f P) w (ticks f P) (Transpose.init (machine f P))=some c ∧
      Transpose.step (machine f P) w c=none ∧ c.outRev=(output f P w).reverse ∧
      ∀ z, c.work ((RawProgramShell.encoding SharedRowBank.initialRowMode P (internalTicks f P)).port 1) z=0 :=
  RawProgramShell.native_correct SharedRowBank.initialRowMode P (internalTicks f P)
    (schedule f P) (schedule_active f P) (value f) (value_congr f P)
    (fun w c hc => represents f P w c hc) w

theorem resources (f : ℕ → Sym Bool → Sym Bool) (P : ℕ) :
    (machine f P).k=2 ∧ (machine f P).g+1=5 ∧ (machine f P).q+1=(ticks f P+1)*200 := by
  have h := RawProgramShell.fixed_resources SharedRowBank.initialRowMode P (internalTicks f P) (schedule f P)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

end TransposeFollowup.RawSymbolMap
