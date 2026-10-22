import TransposeFollowup.AbsoluteTape
import Mathlib.Data.List.OfFn

/-! Finite windows of actual Mathlib tapes. These are representation
equalities only; no copying or motion is asserted to be a free operation.
Use Mathlib's quotient extensionality and list grouping theorem. -/
namespace TransposeFollowup.TapeWindow
set_option autoImplicit false
variable {A : Type*} [Inhabited A]

theorem tape_ext {a b : Turing.Tape A} (h : ∀ z, a.nth z=b.nth z) : a=b := by
  have hl : a.left=b.left := Turing.ListBlank.ext (fun n => h (Int.negSucc n))
  have hr : a.right₀=b.right₀ := Turing.ListBlank.ext (fun n => by
    rw [Turing.Tape.right₀_nth,Turing.Tape.right₀_nth]
    exact h n)
  rw [← Turing.Tape.mk'_left_right₀ a,← Turing.Tape.mk'_left_right₀ b,hl,hr]

theorem cells_ext {a b : Turing.Tape A} (p : ℤ)
    (h : ∀ z, AbsoluteTape.cells a p z=AbsoluteTape.cells b p z) : a=b := by
  apply tape_ext
  intro z
  simpa only [AbsoluteTape.cells,add_sub_cancel_left] using h (p+z)

theorem half_window (L : Turing.ListBlank A) (P : ℕ) :
    ∃ tail : List A, L=Turing.ListBlank.mk (List.ofFn (fun i : Fin P => L.nth i)++tail) := by
  induction P generalizing L with
  | zero =>
    induction L using Turing.ListBlank.induction_on with
    | h xs => exact ⟨xs,rfl⟩
  | succ P ih =>
    obtain ⟨tail,ht⟩ := ih L.tail
    refine ⟨tail,?_⟩
    rw [List.ofFn_succ,List.cons_append,← Turing.ListBlank.cons_mk]
    simp only [Fin.val_zero,Turing.ListBlank.nth_zero,Fin.val_succ,Turing.ListBlank.nth_succ]
    rw [← ht,Turing.ListBlank.cons_head_tail]

theorem tape_window (a : Turing.Tape A) (P : ℕ) :
    ∃ pre tail : List A,
      a=Turing.Tape.mk₂ pre (List.ofFn (fun i : Fin P => a.nth i)++tail) := by
  obtain ⟨tail,ht⟩ := half_window a.right₀ P
  have hl : ∃ pre : List A, a.left=Turing.ListBlank.mk pre := by
    induction a.left using Turing.ListBlank.induction_on with
    | h xs => exact ⟨xs,rfl⟩
  obtain ⟨pre,hpre⟩ := hl
  refine ⟨pre,tail,?_⟩
  conv_lhs => rw [← Turing.Tape.mk'_left_right₀ a,hpre,ht]
  simp only [Turing.Tape.mk₂,Turing.Tape.right₀_nth]

def rows (W r : ℕ) (x : ℕ → A) : List (List A) :=
  List.ofFn (fun i : Fin r => List.ofFn (fun j : Fin W => x (i*W+j)))

omit [Inhabited A] in
theorem rows_length (W r : ℕ) (x : ℕ → A) : (rows W r x).length=r := by
  simp [rows]

omit [Inhabited A] in
theorem row_lengths (W r : ℕ) (x : ℕ → A) : ∀ xs ∈ rows W r x, xs.length=W := by
  intro xs hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  simp

omit [Inhabited A] in
theorem rows_flatten (W r : ℕ) (x : ℕ → A) :
    (rows W r x).flatten=List.ofFn (fun i : Fin (r*W) => x i) :=
  (List.ofFn_mul (fun i : Fin (r*W) => x i)).symm

omit [Inhabited A] in
theorem rows_congr (W r : ℕ) (x y : ℕ → A) (h : ∀ j<r*W, x j=y j) :
    rows W r x=rows W r y := by
  unfold rows
  congr 1
  funext i
  congr 1
  funext j
  apply h
  calc
    i.val*W+j.val < (i.val+1)*W := by nlinarith [j.isLt]
    _ ≤ r*W := Nat.mul_le_mul_right W i.isLt

theorem rows_window (a : Turing.Tape A) (W r : ℕ) (p : ℤ) :
    ∃ pre tail : List A,
      a=Turing.Tape.mk₂ pre ((rows W r (fun j : ℕ => AbsoluteTape.cells a p (p+j))).flatten++tail) := by
  simpa only [rows_flatten,AbsoluteTape.cells,add_sub_cancel_left] using tape_window a (r*W)

theorem window_cell (pre xs tail : List A) (p : ℤ) (j : ℕ) (hj : j<xs.length) :
    AbsoluteTape.cells (Turing.Tape.mk₂ pre (xs++tail)) p (p+j)=xs.getI j := by
  simp only [AbsoluteTape.cells,add_sub_cancel_left,Turing.Tape.mk₂,Turing.Tape.mk'_nth_nat,
    Turing.ListBlank.nth_mk,List.getI_append _ _ _ hj]

end TransposeFollowup.TapeWindow
