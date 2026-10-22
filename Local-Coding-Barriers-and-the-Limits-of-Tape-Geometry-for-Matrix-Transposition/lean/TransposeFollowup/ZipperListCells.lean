import TransposeFollowup.CoupledRowMoves
import FixedTapeCompiler.EraseStream

/-! Bridges from the existing finite zipper representation to absolute
cells. List reversals describe the head's location, not unpaid execution. -/
namespace TransposeFollowup.ZipperListCells
open FixedTapeCompiler
open CopyMachine (Sym Tape)
set_option autoImplicit false

theorem blank_front (W : ℕ) :
    (⟨[],List.replicate W .blank⟩ : Tape Bool).denote=AbsoluteTape.blank := by
  simp only [Tape.denote,Turing.Tape.mk₂,AbsoluteTape.blank,EraseStream.blanks_eq_nil]

theorem front_nat (xs : List (Sym Bool)) (p : ℤ) (j : ℕ) :
    AbsoluteTape.cells (⟨[],xs⟩ : Tape Bool).denote p (p+j)=xs.getI j := by
  simp [AbsoluteTape.cells,Tape.denote,Turing.Tape.mk₂]

theorem front_outside (xs : List (Sym Bool)) (p z : ℤ)
    (h : ¬(p≤z ∧ z<p+xs.length)) :
    AbsoluteTape.cells (⟨[],xs⟩ : Tape Bool).denote p z=.blank := by
  change (Turing.Tape.mk₂ [] xs).nth (z-p)=.blank
  generalize he : z-p=k
  cases k with
  | ofNat n =>
    change z-p=(n : ℤ) at he
    have hn : xs.length≤n := by omega
    rw [Int.ofNat_eq_natCast]
    simpa only [show (default : Sym Bool)=.blank from rfl] using
      (show (Turing.Tape.mk₂ [] xs).nth (n : ℤ)=default by
        simp [Turing.Tape.mk₂,List.getI_eq_default _ hn])
  | negSucc n =>
    simp only [Turing.Tape.mk₂,Turing.Tape.nth,Turing.Tape.mk',Turing.ListBlank.nth_mk]
    rfl

theorem right_iterate_cells (ts : Tape Bool) (n : ℕ) (p z : ℤ) :
    AbsoluteTape.cells ((Tape.moveRight^[n]) ts).denote (p+n) z=
      AbsoluteTape.cells ts.denote p z := by
  induction n generalizing ts p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have h := ih ts.moveRight (p+1)
    rw [show p+(n+1 : ℕ)=(p+1)+(n : ℤ) by push_cast; ring,h]
    simpa only [CopyMachine.denote_right,AbsoluteTape.move,Transpose.Dir.shift] using
      AbsoluteTape.move_cells .right ts.denote p z

theorem end_cells (xs pre suffix : List (Sym Bool)) (p z : ℤ) :
    AbsoluteTape.cells (⟨xs.reverse++pre,suffix⟩ : Tape Bool).denote (p+xs.length) z=
      AbsoluteTape.cells (⟨pre,xs++suffix⟩ : Tape Bool).denote p z := by
  rw [← CoupledRowMoves.right_word xs pre suffix]
  exact right_iterate_cells _ _ _ _

end TransposeFollowup.ZipperListCells
