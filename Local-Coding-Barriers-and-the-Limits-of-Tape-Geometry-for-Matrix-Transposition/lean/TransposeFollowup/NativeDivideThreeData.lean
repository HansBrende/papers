import TransposeFollowup.NativeTrimRun

/-! Division by three from the most significant end of a little-endian
word. The only carried value is a member of Fin3, held in fixed control. -/
namespace TransposeFollowup.NativeDivideThree
open FixedTapeCompiler
set_option autoImplicit false

def remainder (r : Fin 3) (b : Bool) : Fin 3:=⟨(2*r.val+b.toNat)%3,Nat.mod_lt _ (by omega)⟩
def quotientBit (r : Fin 3) (b : Bool) : Bool:=decide (3 ≤ 2*r.val+b.toNat)

theorem digit_identity (r : Fin 3) (b : Bool) :
    3*(quotientBit r b).toNat+(remainder r b).val=2*r.val+b.toNat := by
  fin_cases r <;> cases b <;> decide +kernel

def divide : List Bool → Fin 3 → List Bool × Fin 3
  | [],r => ([],r)
  | b::xs,r => let d:=divide xs r;(quotientBit d.2 b::d.1,remainder d.2 b)

theorem divide_length (xs : List Bool) (r : Fin 3) : (divide xs r).1.length=xs.length := by
  induction xs generalizing r with
  | nil => rfl
  | cons b xs ih => simp [divide,ih]

theorem divide_identity (xs : List Bool) (r : Fin 3) :
    3*Counter.value (divide xs r).1+(divide xs r).2.val=Counter.value xs+2^xs.length*r.val := by
  induction xs generalizing r with
  | nil => simp [divide,Counter.value]
  | cons b xs ih =>
    have hd:=digit_identity (divide xs r).2 b
    have ht:=ih r
    cases hb : quotientBit (divide xs r).2 b <;> cases b <;>
      simp only [divide,Counter.value,List.length_cons,pow_succ,hb,Bool.toNat_false,Bool.toNat_true] at hd ⊢ <;> nlinarith

theorem divide_snoc (xs : List Bool) (b : Bool) (r : Fin 3) :
    divide (xs++[b]) r=((divide xs (remainder r b)).1++[quotientBit r b],(divide xs (remainder r b)).2) := by
  induction xs generalizing r with
  | nil => rfl
  | cons a xs ih => simp [divide,ih]

theorem divide_value (xs : List Bool) : Counter.value (divide xs 0).1=Counter.value xs/3 := by
  have h:=divide_identity xs 0
  have hr:=(divide xs 0).2.isLt
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  omega

theorem divide_remainder (xs : List Bool) : (divide xs 0).2.val=Counter.value xs%3 := by
  have h:=divide_identity xs 0
  have hr:=(divide xs 0).2.isLt
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  omega

end TransposeFollowup.NativeDivideThree
