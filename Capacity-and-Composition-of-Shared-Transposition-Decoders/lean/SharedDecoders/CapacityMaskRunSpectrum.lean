import SharedDecoders.CapacityMaskFinite

/-! # The actual three-stage run-spectrum inequality

The probabilistic application samples the mask; this deterministic theorem
already permits every field, every entry module, and nonlinear decoders.
-/

namespace SharedDecoders

open Module CapacityRuns

variable {d : ℕ} [NeZero d] {F A : Type*} [Field F] [AddCommGroup A]
  [Module F A] [FiniteDimensional F A]

theorem IsSharedCode.run_spectrum_three {p : ZMod d → Bool}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C) (hd : 1<d) :
    8*finrank F C ≤ 4*(d*d*finrank F A)+
      2*d*finrank F A*runCount p 1 1 + d*finrank F A*runCount p 1 4 +
      d*finrank F A*runCount p 1 13 + 6*d*finrank F A := by
  have hval : (1 : ZMod d).val=1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt hd
  have hg : Nat.gcd d (1 : ZMod d).val=1 := by rw [hval,Nat.gcd_one_right]
  have hh := h.eight_mul_finrank_le 1 (3 • (1 : ZMod d)) (9 • (1 : ZMod d))
  have h₁ := Nat.mul_le_mul_left (d*finrank F A) (componentCount_first_shift p (1 : ZMod d))
  have h₂ := Nat.mul_le_mul_left (d*finrank F A) (componentCount_second_shift p (1 : ZMod d))
  have h₃ := Nat.mul_le_mul_left (d*finrank F A) (componentCount_third_shift p (1 : ZMod d))
  rw [hg,← runCount_one] at h₁
  rw [hg] at h₂ h₃
  nlinarith only [hh,h₁,h₂,h₃]

theorem run_spectrum_mean_constant :
    (1/2 : ℚ)+(1/4)*(1/2)+(1/8)*(1/16)+(1/8)*(1/8192)=41473/65536 := by norm_num

theorem run_spectrum_lipschitz_constant :
    (1/4 : ℚ)*2+(1/8)*5+(1/8)*14=23/8 := by norm_num

end SharedDecoders
