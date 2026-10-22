import TransposeFollowup.BufferedRowBankInvariant

/-! A symbol map is a finite cell table in the existing buffered executor.
The second cell is cleared at every update. This adds no execution model. -/
namespace TransposeFollowup.BufferedRows
open FixedTapeCompiler
open CopyMachine (Sym)
set_option autoImplicit false

def mapTable (f : Sym Bool → Sym Bool) (m : CoupledRowCell.Mode) : CoupledRowCell.Mode :=
  (m.1,f m.2.1,.blank)

theorem map_evaluate (f : Sym Bool → Sym Bool) (c : Bool)
    (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    CoupledRowScan.evaluate (mapTable f) c xs ys=
      (c,xs.map f,List.replicate xs.length .blank) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [CoupledRowScan.evaluate,mapTable]
      rw [ih ys (by simpa using h)]
      rfl

def mapRule (f : Sym Bool → Sym Bool) : Rule Bool where
  table := mapTable f
  carry := false
  output := fun xs _ => xs.map f
  saved := fun xs _ => List.replicate xs.length .blank
  realizes := by
    intro xs ys h
    rw [map_evaluate f false xs.reverse ys.reverse (by simpa using h)]
    simp [List.map_reverse]

theorem map_rows (f : Sym Bool → Sym Bool) (rows : List (List (Sym Bool)))
    (ys : List (Sym Bool)) :
    (rowsResult (mapRule f) rows ys).1=rows.flatten.map f := by
  induction rows generalizing ys with
  | nil => rfl
  | cons xs rows ih =>
    change xs.map f++(rowsResult (mapRule f) rows _).1=(xs++rows.flatten).map f
    rw [ih,List.map_append]

theorem map_bankValue (f : Sym Bool → Sym Bool) (W r : ℕ)
    (x : ℕ → Sym Bool) (j : ℕ) (hj : j<r*W) :
    bankValue (mapRule f) W r x j=f (x j) := by
  rw [bankValue,bankOutput,map_rows,TapeWindow.rows_flatten,List.map_ofFn]
  rw [List.getI_eq_getElem _ (by simpa using hj),List.getElem_ofFn]
  rfl

end TransposeFollowup.BufferedRows
