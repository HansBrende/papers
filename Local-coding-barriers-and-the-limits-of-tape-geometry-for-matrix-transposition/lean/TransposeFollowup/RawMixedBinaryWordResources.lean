import TransposeFollowup.RawMixedBinaryWord
import TransposeFollowup.RawBankProgramResources
import Transpose.Tape.DefsTrace

/-! Fixed tapes/alphabet and the derived sublinear state-bit condition for
bounded words, with arbitrary size-dependent operation choices and masks. -/
namespace TransposeFollowup.RawMixedBinaryWord
open Classical Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
open BinaryBankOperation (Operation)
open MixedBinaryWord (Valid)
set_option autoImplicit false

theorem cellBits_eq (P : ℕ) (ops : List Operation) : cellBits (machine P ops) = 3 :=
  RawBankProgram.cellBits_eq P (body P ops)

theorem bounded_ticks (P K : ℕ) (hP : 0<P) (ops : List Operation) (hv : Valid P ops) (hK : ops.length ≤ K) :
    ticks P ops ≤ (7+27*K)*P :=
  (ticks_le P hP ops hv).trans (Nat.mul_le_mul_right P (by omega))

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {K : ℕ} (ops : ℕ → List Operation)
    (hv : ∀ᶠ i in atTop, Valid (inputLength (ns i)) (ops i))
    (hK : ∀ᶠ i in atTop, (ops i).length ≤ K) :
    Tendsto (fun i => (Nat.clog 2 ((machine (inputLength (ns i)) (ops i)).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) := by
  apply RawBankProgram.state_bits_vanish (C:=7+27*K) hns (fun i => body (inputLength (ns i)) (ops i))
  filter_upwards [hv,hK,(inputLength_tendsto hns).eventually_ge_atTop 1] with i hi hk hp
  have hP : 0 < inputLength (ns i) := by
    have hge : 1 ≤ inputLength (ns i) := by exact_mod_cast hp
    omega
  exact bounded_ticks (inputLength (ns i)) K hP (ops i) hi hk

end TransposeFollowup.RawMixedBinaryWord
