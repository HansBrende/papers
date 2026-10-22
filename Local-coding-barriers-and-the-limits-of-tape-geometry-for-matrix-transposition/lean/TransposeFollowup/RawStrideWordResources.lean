import TransposeFollowup.RawMaskedStrideWord
import TransposeFollowup.RawBankProgramResources
import Transpose.Tape.DefsTrace

/-! Fixed tapes/alphabet and the derived sublinear state-bit condition for
bounded words, with arbitrary size-dependent operation choices and masks. -/
namespace TransposeFollowup.RawMaskedStrideWord
open Classical Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
open MaskedStrideWord (Operation Valid)
set_option autoImplicit false

theorem cellBits_eq (P : ℕ) (ops : List Operation) : cellBits (machine P ops) = 3 :=
  RawBankProgram.cellBits_eq P (body P ops)

theorem bounded_ticks (P K : ℕ) (ops : List Operation) (hv : Valid P ops) (hK : ops.length ≤ K) :
    ticks P ops ≤ (7+11*K)*P :=
  (ticks_le P ops hv).trans (Nat.mul_le_mul_right P (by omega))

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {K : ℕ} (ops : ℕ → List Operation)
    (hv : ∀ᶠ i in atTop, Valid (inputLength (ns i)) (ops i))
    (hK : ∀ᶠ i in atTop, (ops i).length ≤ K) :
    Tendsto (fun i => (Nat.clog 2 ((machine (inputLength (ns i)) (ops i)).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) := by
  apply RawBankProgram.state_bits_vanish (C:=7+11*K) hns (fun i => body (inputLength (ns i)) (ops i))
  filter_upwards [hv,hK] with i hi hk
  exact bounded_ticks (inputLength (ns i)) K (ops i) hi hk

end TransposeFollowup.RawMaskedStrideWord
