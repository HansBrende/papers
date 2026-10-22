import TransposeFollowup.BankSymbolRotation

/-! Whole-bank exact-symbol rotation through the shared raw native shell.
Offsets P-1 and 1 (with the empty-bank guard) shift single symbols.
RawEntryShift specializes arbitrary offsets to the full b-symbol S/s pair. -/
namespace TransposeFollowup.RawSymbolRotation
open Classical FixedTapeCompiler ScheduledNativeIO
set_option autoImplicit false

def ticks (P R : ℕ) : ℕ := RawProgramShell.ticks P (BankSymbolRotation.ticks P R)

noncomputable def machine (P R : ℕ) :=
  RawProgramShell.machine SharedRowBank.initialRowMode P (BankSymbolRotation.ticks P R)
    (BankSymbolRotation.schedule P R)

def output (P R : ℕ) (w : List Bool) : List Bool :=
  (List.range P).map (fun j => ScheduledRawInput.inputBit w ((j+R)%P : ℕ))

theorem ticks_eq (P R : ℕ) (hR : R ≤ P) : ticks P R=29*P := by
  rw [ticks,RawProgramShell.ticks_eq,BankSymbolRotation.ticks_eq P R hR]
  omega

theorem native_correct (P R : ℕ) (hR : R ≤ P) (w : List Bool) :
    ∃ c : Transpose.Config (machine P R),
      Transpose.stepN (machine P R) w (ticks P R) (Transpose.init (machine P R))=some c ∧
      Transpose.step (machine P R) w c=none ∧ c.outRev=(output P R w).reverse ∧
      ∀ z, c.work ((RawProgramShell.encoding SharedRowBank.initialRowMode P (BankSymbolRotation.ticks P R)).port 1) z=0 := by
  exact RawProgramShell.native_correct SharedRowBank.initialRowMode P (BankSymbolRotation.ticks P R)
    (BankSymbolRotation.schedule P R) (BankSymbolRotation.schedule_active P R)
    (BankSymbolRotation.value P R) (BankSymbolRotation.value_congr P R)
    (fun w c hc => by
      rw [BankSymbolRotation.schedule_exact]
      exact BankSymbolRotation.represents P R hR w c hc) w

theorem resources (P R : ℕ) :
    (machine P R).k=2 ∧ (machine P R).g+1=5 ∧ (machine P R).q+1=(ticks P R+1)*200 := by
  have h := RawProgramShell.fixed_resources SharedRowBank.initialRowMode P (BankSymbolRotation.ticks P R)
    (BankSymbolRotation.schedule P R)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

def shiftOffset (right : Bool) (P : ℕ) : ℕ := if right then P-1 else min 1 P

theorem shiftOffset_le (right : Bool) (P : ℕ) : shiftOffset right P ≤ P := by
  cases right
  · exact Nat.min_le_right _ _
  · exact Nat.sub_le _ _

theorem left_shift_index (P j : ℕ) (hj : j<P) :
    (j+shiftOffset false P)%P=(j+1)%P := by
  simp only [shiftOffset,Bool.false_eq_true,ite_false,Nat.min_eq_left (by omega : 1 ≤ P)]

theorem right_shift_index (P j : ℕ) (hj : j<P) :
    (j+shiftOffset true P)%P=if j=0 then P-1 else j-1 := by
  simp only [shiftOffset,ite_true]
  by_cases hz : j=0
  · subst j
    simp only [zero_add,ite_true,Nat.mod_eq_of_lt (by omega : P-1<P)]
  · rw [ite_eq_right hz,Nat.mod_eq_sub_mod (by omega : P ≤ j+(P-1)),
      Nat.mod_eq_of_lt (by omega : j+(P-1)-P<P)]
    omega

end TransposeFollowup.RawSymbolRotation
