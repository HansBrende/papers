import TransposeFollowup.TernaryBankData
import TransposeFollowup.BufferedRowBankInvariant

/-! Componentwise F3 addition/difference against a real retained buffer.
Every coordinate uses only the matching coordinate of that buffer. A row
buffer supplies P/p; an entry buffer, reset between rows, supplies Q/q. -/
namespace TransposeFollowup.TernaryBank
open FixedTapeCompiler
open CopyMachine (Sym)
set_option autoImplicit false

def bufferUpdate (sub : Bool) (m : CoupledRowCell.Mode) : CoupledRowCell.Mode :=
  (m.1,encode (digit sub (decode m.2.1) (decode m.2.2)),
    encode (stored sub (decode m.2.1) (decode m.2.2)))

def bufferOutput (sub : Bool) (xs ys : List (Sym Bool)) : List (Sym Bool) :=
  List.zipWith (fun a b => encode (digit sub (decode a) (decode b))) xs ys

def bufferSaved (sub : Bool) (xs ys : List (Sym Bool)) : List (Sym Bool) :=
  if sub then xs.map (fun a => encode (decode a)) else bufferOutput sub xs ys

theorem buffer_evaluate (sub c : Bool) (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    CoupledRowScan.evaluate (bufferUpdate sub) c xs ys=
      (c,bufferOutput sub xs ys,bufferSaved sub xs ys) := by
  induction xs generalizing ys with
  | nil => cases sub <;> rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [CoupledRowScan.evaluate,bufferUpdate]
      rw [ih ys (by simpa using h)]
      cases sub <;> simp [bufferOutput,bufferSaved,stored,digit]

theorem buffer_realizes (sub : Bool) (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    (CoupledRowScan.evaluate (bufferUpdate sub) false xs.reverse ys.reverse).2.1.reverse=bufferOutput sub xs ys ∧
    (CoupledRowScan.evaluate (bufferUpdate sub) false xs.reverse ys.reverse).2.2.reverse=bufferSaved sub xs ys := by
  rw [buffer_evaluate sub false xs.reverse ys.reverse (by simpa using h)]
  have ho : (bufferOutput sub xs.reverse ys.reverse).reverse=bufferOutput sub xs ys := by
    simp only [bufferOutput,← List.reverse_zipWith h,List.reverse_reverse]
  refine ⟨ho,?_⟩
  cases sub with
  | false => exact ho
  | true => simp [bufferSaved,List.map_reverse]

def bufferRule (sub : Bool) : BufferedRows.Rule Bool where
  table := bufferUpdate sub
  carry := false
  output := bufferOutput sub
  saved := bufferSaved sub
  realizes := buffer_realizes sub

theorem bufferOutput_encoded (sub : Bool) (xs ys : List Trit) :
    bufferOutput sub (xs.map encode) (ys.map encode)=
      (List.zipWith (digit sub) xs ys).map encode := by
  simp only [bufferOutput,List.zipWith_map,List.map_zipWith]
  congr 1
  funext a b
  rw [decode_encode a,decode_encode b]

end TransposeFollowup.TernaryBank
