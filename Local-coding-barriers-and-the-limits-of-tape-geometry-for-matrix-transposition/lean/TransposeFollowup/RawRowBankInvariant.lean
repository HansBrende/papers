import TransposeFollowup.RawRowArithmeticBank
import TransposeFollowup.TapeWindow
import TransposeFollowup.BankWordInvariant
import TransposeFollowup.BufferedRowBankInvariant

/-! Row arithmetic on arbitrary clean banks, not only a chosen list
representation. The finite-window representation preserves surrounding
cells. Its construction is an equality used in the proof, not machine work.
The shared word invariant uses exact symbols, so later trit routines can
reuse the same interface without applying a binary decoder. -/
namespace TransposeFollowup.RawRowArithmetic
open FixedTapeCompiler ScheduledTapeAction
open CopyMachine (Sym Tape)
open CoupledRowCell (Mode State cfg)
set_option autoImplicit false

def bankValue (sub : Bool) (W r : ℕ) (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool :=
  (bankOutput sub W (TapeWindow.rows W r x)).getI j

theorem bankValue_congr (sub : Bool) (W r : ℕ) : BankWord.Congruent (r*W) (bankValue sub W r) :=
  BufferedRows.bankValue_congr (rule sub) W r

theorem clean_representation {C : Type} (W r : ℕ) (c : State C) (hc : BankWord.symbols.clean c) :
    ∃ pre tail : List (Sym Bool),
      c=bankStart c.work.core.pc (TapeWindow.rows W r (BankWord.input BankWord.symbols c))
        pre tail c.work.pos c.inputPos c.outRev :=
  BufferedRows.clean_representation W r c hc

theorem bank_represents (sub : Bool) (W r : ℕ) (w : List Bool) (c : State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (r*W) c (bankRun sub W r w c)
      (bankValue sub W r (BankWord.input BankWord.symbols c)) :=
  BufferedRows.bank_represents (rule sub) W r w c hc

end TransposeFollowup.RawRowArithmetic
