import TransposeFollowup.RawBankProgram
import TransposeFollowup.LinearStateCount
import Transpose.Tape.DefsTrace

/-! The same native resource count and state-bit estimate serve every
binary bank program with a linear paid runtime. -/
namespace TransposeFollowup.RawBankProgram
open Classical Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false

theorem cellBits_eq (P : ℕ) (B : Body) : cellBits (machine P B) = 3 := by
  unfold cellBits
  rw [(fixed_resources P B).2.1]
  decide +kernel

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {C : ℕ} (B : ℕ → Body)
    (htime : ∀ᶠ i in atTop, ticks (inputLength (ns i)) (B i) ≤ C*inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 ((machine (inputLength (ns i)) (B i)).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) := by
  apply state_bits_of_linear_count (c:=4*((C : ℝ)+1)) hns
  filter_upwards [htime,(inputLength_tendsto hns).eventually_ge_atTop 1] with i ht hp
  have hP : 1 ≤ inputLength (ns i) := by exact_mod_cast hp
  have hq := (fixed_resources (inputLength (ns i)) (B i)).2.2
  have hb : (machine (inputLength (ns i)) (B i)).q+1 ≤ 4*(C+1)*inputLength (ns i) := by
    rw [hq]
    nlinarith
  exact_mod_cast hb

end TransposeFollowup.RawBankProgram
