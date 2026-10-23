import BitWord.GeometryPartitionData
import Transpose.Tape.CEHint

namespace BitWord.Geometry

/-- The actual canonical logarithmic-width word block. The endpoint may be any
whole-entry permutation, so a word transpose is included without inspecting its
internal tape computation. -/
def canonicalWordBlock (d : ℕ) (hd : 0 < d) (e : Equiv.Perm (Fin (d*d))) :
    BlockOperation :=
  .entries (Transpose.entryBits d) (d*d) (by unfold Transpose.entryBits; omega)
    (Nat.mul_pos hd hd) e

 theorem canonicalWordBlock_admissible (d : ℕ) (hd : 0 < d)
     (e : Equiv.Perm (Fin (d*d))) : (canonicalWordBlock d hd e).Admissible := by
   have hh := Transpose.Tape.Impl.le_two_pow_entryBits d
   have hs : d*d ≤ (2^Transpose.entryBits d)*(2^Transpose.entryBits d) :=
     Nat.mul_le_mul hh hh
   have he : (2^Transpose.entryBits d)*(2^Transpose.entryBits d) =
       4^Transpose.entryBits d := by rw [← Nat.mul_pow]
   rw [he] at hs
   exact Nat.mul_le_mul_left (Transpose.entryBits d) hs

end BitWord.Geometry
