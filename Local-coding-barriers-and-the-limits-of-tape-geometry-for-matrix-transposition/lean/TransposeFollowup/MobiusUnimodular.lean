import TransposeFollowup.RationalSeedWords
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.GroupTheory.Abelianization.Defs

/-! Haar inversion and right invariance for SL2(R), obtained from the
existing perfectness theorem and the modular character. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem modularCharacter_eq_one (g : Group) : Measure.modularCharacter g = 1 := by
  have hc : commutator Group = ⊤ :=
    Matrix.SL2.commutator_eq_top (a := (2 : ℝ)) (by norm_num) (by norm_num)
  have hg : g ∈ commutator Group := by rw [hc]; trivial
  have hk := Abelianization.commutator_subset_ker
    (Measure.modularCharacter (G := Group)).toHomUnits hg
  have he := MonoidHom.mem_ker.mp hk
  exact congrArg (fun x : ℝ≥0ˣ => (x : ℝ≥0)) he

variable [MeasurableSpace Group] [BorelSpace Group]

instance instMobiusHaarRightInvariant : Measure.IsMulRightInvariant (Measure.haar : Measure Group) where
  map_mul_right_eq_self g := by
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
    change Measure.modularCharacter g • (Measure.haar : Measure Group) = _
    rw [modularCharacter_eq_one, one_smul]

omit [MeasurableSpace Group] [BorelSpace Group] in
theorem mobiusIdentityBall_inv (η : ℝ) : (mobiusIdentityBall η)⁻¹ = mobiusIdentityBall η := by
  ext g
  change mobiusIdentityDistanceSq g⁻¹ < η ^ 2 ↔ mobiusIdentityDistanceSq g < η ^ 2
  rw [RationalFreePair.real_identityDistanceSq_inv]

instance instMobiusHaarInvInvariant : Measure.IsInvInvariant (Measure.haar : Measure Group) where
  inv_eq_self := by
    let H : Measure Group := Measure.haar
    let c := Measure.haarScalarFactor H.inv H
    have hc : H.inv = c • H := Measure.isMulLeftInvariant_eq_smul H.inv H
    have he := congrArg (fun μ : Measure Group => μ (mobiusIdentityBall 1)) hc
    have hb : H (mobiusIdentityBall 1) ≠ 0 := (mobiusIdentityBall_haar_pos (by norm_num)).ne'
    have hb' : H (mobiusIdentityBall 1) ≠ ∞ := (mobiusIdentityBall_haar_lt_top (by norm_num)).ne
    simp only [Measure.inv_apply, mobiusIdentityBall_inv, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at he
    have hc' : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hb hb').mp (by simpa using he.symm)
    have hc1 : c = 1 := ENNReal.coe_eq_one.mp hc'
    simpa only [hc1, one_smul] using hc

end TransposeFollowup.RealMobius
