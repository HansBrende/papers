import Transpose.Tape.MStarClass

/-! A linear number of states satisfies the original nonuniform state-bit
condition. This is a direct application of the original state-bit estimate,
shared by the single-operation and whole-word native executors. -/
namespace TransposeFollowup
open Filter Topology Transpose Transpose.Tape.Impl
set_option autoImplicit false

theorem state_bits_of_linear_count {ns Q : ℕ → ℕ} {c : ℝ}
    (hns : Tendsto ns atTop atTop)
    (hcount : ∀ᶠ i in atTop, (Q i : ℝ) ≤ c*inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 (Q i) : ℝ)/inputLength (ns i)) atTop (𝓝 0) := by
  have hbig : Tendsto (fun i => (Nat.clog 2 (2*Q i+1) : ℝ)/inputLength (ns i)) atTop (𝓝 0) := by
    simpa only [Nat.zero_add,Nat.one_mul,Nat.cast_zero,zero_div] using
      (stateBits_div_tendsto (k:=0) (qs:=fun _ => 0) hns hcount (by simp))
  apply squeeze_zero (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hbig
  intro i
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.clog_mono_right 2 (show Q i ≤ 2*Q i+1 by omega)

end TransposeFollowup
