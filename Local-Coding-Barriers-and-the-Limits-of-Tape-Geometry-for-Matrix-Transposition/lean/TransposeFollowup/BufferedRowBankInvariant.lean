import TransposeFollowup.BufferedRowBank
import TransposeFollowup.TapeWindow
import TransposeFollowup.BankWordInvariant

/-! Row arithmetic on arbitrary clean banks, not only a chosen list
representation. The finite-window representation preserves surrounding
cells. Its construction is an equality used in the proof, not machine work.
The shared word invariant uses exact symbols, so later trit routines can
reuse the same interface without applying a binary decoder. -/
namespace TransposeFollowup.BufferedRows
open FixedTapeCompiler ScheduledTapeAction
open CopyMachine (Sym Tape)
open CoupledRowCell (Mode State cfg)
set_option autoImplicit false
variable {C : Type}

def bankValue (u : Rule C) (W r : ℕ) (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool :=
  (bankOutput u W (TapeWindow.rows W r x)).getI j

theorem bankValue_congr (u : Rule C) (W r : ℕ) : BankWord.Congruent (r*W) (bankValue u W r) := by
  intro x y h j _
  rw [bankValue,bankValue,TapeWindow.rows_congr W r x y h]

theorem clean_representation (W r : ℕ) (c : State C) (hc : BankWord.symbols.clean c) :
    ∃ pre tail : List (Sym Bool),
      c=bankStart c.work.core.pc (TapeWindow.rows W r (BankWord.input BankWord.symbols c))
        pre tail c.work.pos c.inputPos c.outRev := by
  obtain ⟨pre,tail,ht⟩ := TapeWindow.rows_window (c.work.core.tapes 0) W r (c.work.pos 0)
  have hs : c.work.core.tapes 1=(⟨[],[]⟩ : Tape Bool).denote := by
    apply TapeWindow.cells_ext (c.work.pos 1)
    intro z
    exact (hc z).trans (AbsoluteTape.blank_cells (c.work.pos 1) z).symm
  refine ⟨pre,tail,?_⟩
  change c=cfg c.work.core.pc _ c.work.pos c.inputPos c.outRev
  have he : c.work.core.tapes=
      fun t => (![⟨pre,(TapeWindow.rows W r (BankWord.input BankWord.symbols c)).flatten++tail⟩,
        ⟨[],[]⟩] t : Tape Bool).denote := by
    funext t
    fin_cases t
    · exact ht
    · exact hs
  conv_lhs => rw [show c=(⟨⟨⟨c.work.core.pc,c.work.core.tapes⟩,c.work.pos⟩,c.inputPos,c.outRev⟩ : State C) from rfl]
  simp only [cfg,he]

theorem bank_represents (u : Rule C) (W r : ℕ) (w : List Bool) (c : State C)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (r*W) c (bankRun u W r w c)
      (bankValue u W r (BankWord.input BankWord.symbols c)) := by
  let rows := TapeWindow.rows W r (BankWord.input BankWord.symbols c)
  have hr : rows.length=r := TapeWindow.rows_length W r _
  have hw : ∀ xs ∈ rows, xs.length=W := TapeWindow.row_lengths W r _
  obtain ⟨pre,tail,he⟩ := clean_representation W r c hc
  have h := bank_spec u W rows hw c.work.core.pc pre tail c.work.pos c.inputPos c.outRev w
  dsimp only at h
  change c=bankStart c.work.core.pc rows pre tail c.work.pos c.inputPos c.outRev at he
  rw [hr,← he] at h
  refine ⟨h.1,?_,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  intro j hj
  have hl : (bankOutput u W rows).length=r*W := by
    exact (rows_lengths u W rows hw (List.replicate W .blank) (by simp)).1.trans (by rw [hr])
  change cells (bankRun u W r w c) 0 (c.work.pos 0+j)=_
  rw [h.2.1]
  exact TapeWindow.window_cell pre (bankOutput u W rows) tail (c.work.pos 0) j (by omega)

end TransposeFollowup.BufferedRows
