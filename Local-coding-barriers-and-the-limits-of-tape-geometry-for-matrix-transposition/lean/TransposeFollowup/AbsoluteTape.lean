import Transpose.Statement
import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Tactic

/-! The original absolute-coordinate work tapes and Mathlib's relative tapes
agree under each native write and head movement. No simulation slowdown is
introduced at this layer. -/

namespace TransposeFollowup
namespace AbsoluteTape

set_option autoImplicit false
variable {Γ : Type*} [Inhabited Γ]

def cells (T : Turing.Tape Γ) (p : ℤ) : ℤ → Γ := fun z => T.nth (z - p)

def move : Transpose.Dir → Turing.Tape Γ → Turing.Tape Γ
  | .left, T => T.move .left
  | .stay, T => T
  | .right, T => T.move .right

theorem scanned (T : Turing.Tape Γ) (p : ℤ) : cells T p p = T.head := by
  simp [cells]

theorem move_cells (d : Transpose.Dir) (T : Turing.Tape Γ) (p z : ℤ) :
    cells (move d T) (d.shift p) z = cells T p z := by
  cases d with
  | stay => rfl
  | left =>
    simp only [cells, move, Transpose.Dir.shift, Turing.Tape.move_left_nth]
    congr 1
    omega
  | right =>
    simp only [cells, move, Transpose.Dir.shift, Turing.Tape.move_right_nth]
    congr 1
    omega

theorem write_cells (a : Γ) (T : Turing.Tape Γ) (p z : ℤ) :
    cells (T.write a) p z = if z = p then a else cells T p z := by
  simp [cells, Turing.Tape.write_nth, sub_eq_zero]

theorem write_move_cells (a : Γ) (d : Transpose.Dir) (T : Turing.Tape Γ) (p z : ℤ) :
    cells (move d (T.write a)) (d.shift p) z = if z = p then a else cells T p z := by
  rw [move_cells, write_cells]

def blank : Turing.Tape Γ := Turing.Tape.mk₂ [] []

theorem blank_nth (z : ℤ) : (blank : Turing.Tape Γ).nth z = default := by
  cases z with
  | ofNat n =>
    cases n <;> simp [blank, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth,
      Turing.ListBlank.nth_mk, Turing.ListBlank.head_mk]
  | negSucc n =>
    simp [blank, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth,
      Turing.ListBlank.nth_mk]

theorem blank_cells (p z : ℤ) : cells (blank : Turing.Tape Γ) p z = default :=
  blank_nth _

end AbsoluteTape
end TransposeFollowup
