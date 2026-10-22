import TransposeFollowup.RawSymbolMap
import TransposeFollowup.TernaryBankData
import Mathlib.Data.Nat.Bits

/-! The full b-trit phase D is a specialization of public symbol maps.
Population count uses mathlib's binary digits and List.count. The tables
are compiled into the nonuniform clock; no runtime popcount is assumed. -/
namespace TransposeFollowup.TernaryPhase
open FixedTapeCompiler TernaryBank
open CopyMachine (Sym)
set_option autoImplicit false

def sign (i j : ℕ) : Trit := (-1)^((i &&& j).bits.count true)

def table (b d k : ℕ) (a : Sym Bool) : Sym Bool :=
  encode (sign (k/(d*b)) ((k/b)%d)*decode a)

theorem value_entry (b d : ℕ) (x : ℕ → Sym Bool) (i j l : ℕ)
    (hj : j<d) (hl : l<b) :
    RawSymbolMap.value (table b d) x (i*(d*b)+j*b+l)=
      encode (sign i j*decode (x (i*(d*b)+j*b+l))) := by
  have hb : 0<b := Nat.zero_lt_of_lt hl
  have hu : j*b+l<d*b := by nlinarith
  have hW : 0<d*b := Nat.zero_lt_of_lt hu
  have hr : (i*(d*b)+j*b+l)/(d*b)=i := by
    rw [Nat.add_assoc,Nat.add_comm,Nat.add_mul_div_right _ _ hW,Nat.div_eq_of_lt hu,zero_add]
  have he : (i*(d*b)+j*b+l)/b=i*d+j := by
    rw [show i*(d*b)+j*b+l=l+(i*d+j)*b by ring,
      Nat.add_mul_div_right _ _ hb,Nat.div_eq_of_lt hl,zero_add]
  simp only [RawSymbolMap.value,table,hr,he,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hj]

theorem value_encoded_entry (b d : ℕ) (x : ℕ → Trit) (i j l : ℕ)
    (hj : j<d) (hl : l<b) :
    RawSymbolMap.value (table b d) (fun k => encode (x k)) (i*(d*b)+j*b+l)=
      encode (sign i j*x (i*(d*b)+j*b+l)) := by
  rw [value_entry b d _ i j l hj hl,decode_encode]

theorem sign_mul_self (i j : ℕ) : sign i j*sign i j=1 := by
  unfold sign
  rw [← mul_pow,neg_mul_neg,one_mul,one_pow]

theorem table_involutive_encoded (b d k : ℕ) (a : Trit) :
    table b d k (table b d k (encode a))=encode a := by
  simp only [table]
  rw [decode_encode,decode_encode,← mul_assoc,sign_mul_self,one_mul]

end TransposeFollowup.TernaryPhase
