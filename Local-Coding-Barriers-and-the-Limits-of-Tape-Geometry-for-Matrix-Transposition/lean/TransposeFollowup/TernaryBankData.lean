import TransposeFollowup.CoupledRowScan
import TransposeFollowup.SharedRowBank
import Mathlib.Data.ZMod.Basic

/-! Ternary values use the existing five work symbols; the retained trit
uses two existing control bits. Arithmetic is Mathlib's ZMod 3, and the
horizontal prefix/difference semantics reuse List.scanl/zipWith. -/
namespace TransposeFollowup.TernaryBank
open FixedTapeCompiler
open CopyMachine (Sym)
set_option autoImplicit false

abbrev Trit := ZMod 3
abbrev Carry := Bool × Bool

def encode (a : Trit) : Sym Bool := if a=0 then .data false else if a=1 then .data true else .start

def decode : Sym Bool → Trit
  | .data false => 0
  | .data true => 1
  | .start => 2
  | _ => 0

theorem decode_encode : Function.LeftInverse decode encode := by decide +kernel

def carry (a : Trit) : Carry := (decide (a=1),decide (a=2))

def uncarry (c : Carry) : Trit := if c.1 then 1 else if c.2 then 2 else 0

theorem uncarry_carry : Function.LeftInverse uncarry carry := by decide +kernel

theorem encode_bool (b : Bool) : encode (if b then 1 else 0)=.data b := by cases b <;> rfl

theorem decode_blank : decode .blank=0 := rfl

def digit (sub : Bool) (a prev : Trit) : Trit := if sub then a-prev else a+prev

def stored (sub : Bool) (a prev : Trit) : Trit := if sub then a else digit sub a prev

def rowResult (sub : Bool) (prev : Trit) (xs : List Trit) : List Trit :=
  if sub then List.zipWith (fun a b => a-b) xs (prev::xs)
  else (xs.scanl (fun b a => a+b) prev).tail

theorem rowResult_nil (sub : Bool) (prev : Trit) : rowResult sub prev []=[] := by
  cases sub <;> rfl

theorem rowResult_cons (sub : Bool) (prev a : Trit) (xs : List Trit) :
    rowResult sub prev (a::xs)=digit sub a prev::rowResult sub (stored sub a prev) xs := by
  cases sub <;> cases xs <;> simp [rowResult,digit,stored,List.scanl_cons]

theorem rowResult_length (sub : Bool) (prev : Trit) (xs : List Trit) :
    (rowResult sub prev xs).length=xs.length := by
  cases sub <;> simp [rowResult,List.length_scanl]

def horizontalUpdate (sub : Bool) (m : CoupledRowCell.Mode Carry) : CoupledRowCell.Mode Carry :=
  let a := decode m.2.1
  let prev := uncarry m.1
  (carry (stored sub a prev),encode (digit sub a prev),m.2.2)

theorem horizontal_evaluate (sub : Bool) (prev : Trit) (xs ys : List (Sym Bool))
    (h : xs.length=ys.length) :
    (CoupledRowScan.evaluate (horizontalUpdate sub) (carry prev) xs ys).2.1=
      (rowResult sub prev (xs.map decode)).map encode := by
  induction xs generalizing prev ys with
  | nil => simp [CoupledRowScan.evaluate,rowResult_nil]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [CoupledRowScan.evaluate,horizontalUpdate,uncarry_carry prev,List.map_cons,rowResult_cons]
      rw [ih (stored sub (decode a) prev) ys (by simpa using h)]

/-- Rearrange the same 200 control states; no extra state or instruction. -/
def modes : SharedRowBank.Mode ≃ CoupledRowCell.Mode Carry × Bool where
  toFun m := ((m.1,m.2.2.1,m.2.2.2),m.2.1)
  invFun m := (m.1.1,m.2,m.1.2.1,m.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

end TransposeFollowup.TernaryBank
