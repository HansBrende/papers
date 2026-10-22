import TransposeFollowup.MeasureAutocorrelation
import TransposeFollowup.MobiusUnimodular
import TransposeFollowup.MobiusSmoothedDensity

/-! Exact inversion and concatenation identities for the actual generator
walk and Haar kernel. No commutation of the kernel with the walk is assumed. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem symmetricGeneratorMeasure_inv {m : ℕ} (G : Fin m → Group) :
    (symmetricGeneratorMeasure G).inv = symmetricGeneratorMeasure G := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_inv_measure]
  unfold symmetricGeneratorMeasure
  simp only [lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_add_measure]
  simp only [lintegral_dirac, inv_inv]
  simp only [add_comm]

theorem generatorWalkMeasure_one {m : ℕ} (G : Fin m → Group) (hm : 0 < m) :
    generatorWalkMeasure G 1 = symmetricGeneratorMeasure G := by
  have : IsProbabilityMeasure (symmetricGeneratorMeasure G) := symmetricGeneratorMeasure_probability G hm
  unfold generatorWalkMeasure
  exact Measure.mconv_dirac_one _

theorem generatorWalkMeasure_add {m : ℕ} (G : Fin m → Group) (hm : 0 < m) (n k : ℕ) :
    generatorWalkMeasure G (n + k) = generatorWalkMeasure G n ∗ₘ generatorWalkMeasure G k := by
  have : IsProbabilityMeasure (generatorWalkMeasure G k) := generatorWalkMeasure_probability G hm k
  induction n with
  | zero => simp only [Nat.zero_add, generatorWalkMeasure, Measure.dirac_one_mconv]
  | succ n ih =>
    have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hm n
    rw [Nat.succ_add, generatorWalkMeasure, ih, ← Measure.mconv_assoc]
    rfl

theorem generatorWalkMeasure_mconv_comm {m : ℕ} (G : Fin m → Group) (hm : 0 < m) (n k : ℕ) :
    generatorWalkMeasure G n ∗ₘ generatorWalkMeasure G k =
      generatorWalkMeasure G k ∗ₘ generatorWalkMeasure G n := by
  rw [← generatorWalkMeasure_add G hm, ← generatorWalkMeasure_add G hm, Nat.add_comm]

theorem generatorWalkMeasure_inv {m : ℕ} (G : Fin m → Group) (hm : 0 < m) (n : ℕ) :
    (generatorWalkMeasure G n).inv = generatorWalkMeasure G n := by
  have : IsProbabilityMeasure (symmetricGeneratorMeasure G) := symmetricGeneratorMeasure_probability G hm
  induction n with
  | zero => simp [generatorWalkMeasure, Measure.inv_def, Measure.map_dirac' measurable_inv]
  | succ n ih =>
    have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hm n
    rw [generatorWalkMeasure, inv_mconv, ih, symmetricGeneratorMeasure_inv,
      ← generatorWalkMeasure_one G hm, generatorWalkMeasure_mconv_comm G hm n 1,
      generatorWalkMeasure_one G hm]

theorem mobiusHaarKernelDensity_inv (η : ℝ) (g : Group) :
    mobiusHaarKernelDensity η g⁻¹ = mobiusHaarKernelDensity η g := by
  have he : g⁻¹ ∈ mobiusIdentityBall η ↔ g ∈ mobiusIdentityBall η := by
    change mobiusIdentityDistanceSq g⁻¹ < η ^ 2 ↔ mobiusIdentityDistanceSq g < η ^ 2
    rw [RationalFreePair.real_identityDistanceSq_inv]
  simp only [mobiusHaarKernelDensity, Set.indicator_apply, he]

theorem mobiusHaarKernel_inv (η : ℝ) : (mobiusHaarKernel η).inv = mobiusHaarKernel η := by
  rw [mobiusHaarKernel_eq_withDensity]
  change ((Measure.haar : Measure Group).withDensity (mobiusHaarKernelDensity η)).inv = _
  rw [inv_withDensity _ (mobiusHaarKernelDensity_measurable η)]
  simp only [mobiusHaarKernelDensity_inv]
  rfl

theorem smoothedWalk_autocorrelation_eq_sandwich {m : ℕ} (G : Fin m → Group) (hm : 0 < m)
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    (generatorWalkMeasure G n ∗ₘ mobiusHaarKernel η).inv ∗ₘ
      (generatorWalkMeasure G n ∗ₘ mobiusHaarKernel η) =
      mobiusHaarKernel η ∗ₘ (generatorWalkMeasure G (2 * n) ∗ₘ mobiusHaarKernel η) := by
  have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hm n
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  rw [inv_mconv, mobiusHaarKernel_inv, generatorWalkMeasure_inv G hm,
    Measure.mconv_assoc, ← Measure.mconv_assoc (generatorWalkMeasure G n),
    ← generatorWalkMeasure_add G hm, ← two_mul]

end TransposeFollowup.RealMobius
