import TransposeFollowup.MobiusMatrixGeometryCore
import TransposeFollowup.MobiusSmoothedDensity
import TransposeFollowup.MobiusHaarEntryBox

/-! Actual support bounds for symmetric generator walks and Haar smoothing.
These are derived from matrix multiplication, inversion and convolution;
no support or density-flatness estimate is assumed for the walk. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem mconv_ae_matrixEntryBox (μ ν : Measure Group) [SFinite ν] {B C : ℝ}
    (hμ : ∀ᵐ g ∂μ, g ∈ matrixEntryBox B) (hν : ∀ᵐ g ∂ν, g ∈ matrixEntryBox C) :
    ∀ᵐ g ∂μ ∗ₘ ν, g ∈ matrixEntryBox (2 * B * C) := by
  have hs := (matrixEntryBox_isCompact (2 * B * C)).isClosed.measurableSet
  rw [Measure.mconv]
  apply (ae_map_iff (p := fun g => g ∈ matrixEntryBox (2 * B * C))
    measurable_mul.aemeasurable hs).mpr
  apply (Measure.ae_prod_iff_ae_ae (hs.preimage measurable_mul)).mpr
  filter_upwards [hμ] with g hg
  exact hν.mono (fun h hh => matrixEntryBox_mul hg hh)

theorem symmetricGeneratorMeasure_ae_entryBox {c : ℕ} (G : Fin c → Group) {A : ℝ}
    (hG : ∀ i, G i ∈ matrixEntryBox A) :
    ∀ᵐ g ∂symmetricGeneratorMeasure G, g ∈ matrixEntryBox A := by
  unfold symmetricGeneratorMeasure
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i _
  rw [ae_add_measure_iff]
  exact ⟨(ae_dirac_iff (p := fun g => g ∈ matrixEntryBox A)
      (matrixEntryBox_isCompact A).isClosed.measurableSet).mpr (hG i),
    (ae_dirac_iff (p := fun g => g ∈ matrixEntryBox A)
      (matrixEntryBox_isCompact A).isClosed.measurableSet).mpr (matrixEntryBox_inv (hG i))⟩

theorem generatorWalkMeasure_ae_entryBox {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    {A : ℝ} (hG : ∀ i, G i ∈ matrixEntryBox A) (n : ℕ) :
    ∀ᵐ g ∂generatorWalkMeasure G n, g ∈ matrixEntryBox ((2 * A) ^ n) := by
  induction n with
  | zero =>
    simp only [generatorWalkMeasure, pow_zero]
    exact (ae_dirac_iff (matrixEntryBox_isCompact 1).isClosed.measurableSet).mpr one_mem_matrixEntryBox
  | succ n ih =>
    have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hc n
    have hb := mconv_ae_matrixEntryBox (symmetricGeneratorMeasure G) (generatorWalkMeasure G n)
      (symmetricGeneratorMeasure_ae_entryBox G hG) ih
    simpa only [generatorWalkMeasure, pow_succ'] using hb

theorem generatorWalk_smoothed_ae_entryBox {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    {A η : ℝ} (hG : ∀ i, G i ∈ matrixEntryBox A) (hη : 0 < η) (hηone : η ≤ 1) (n : ℕ) :
    ∀ᵐ g ∂generatorWalkMeasure G n ∗ₘ mobiusHaarKernel η,
      g ∈ matrixEntryBox (4 * (2 * A) ^ n) := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have hk := (mobiusHaarKernel_ae_mem η).mono
    (fun _ hg => mobiusIdentityBall_subset_entryBox_two hη hηone hg)
  have hb := mconv_ae_matrixEntryBox (generatorWalkMeasure G n) (mobiusHaarKernel η)
    (generatorWalkMeasure_ae_entryBox G hc hG n) hk
  rw [show 2 * (2 * A) ^ n * 2 = 4 * (2 * A) ^ n by ring] at hb
  exact hb

theorem mobiusSmoothedWalkDensity_ae_zero_outside {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    {A η : ℝ} (hG : ∀ i, G i ∈ matrixEntryBox A) (hη : 0 < η) (hηone : η ≤ 1) (n : ℕ) :
    ∀ᵐ g ∂(Measure.haar : Measure Group),
      g ∉ matrixEntryBox (4 * (2 * A) ^ n) → mobiusSmoothedDensity (generatorWalkMeasure G n) η g = 0 := by
  have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hc n
  have hs := generatorWalk_smoothed_ae_entryBox G hc hG hη hηone n
  rw [mconv_mobiusHaarKernel_eq_withDensity,
    ae_withDensity_iff (mobiusSmoothedDensity_measurable _ η)] at hs
  exact hs.mono (fun _ hg hnot => by
    by_contra hn
    exact hnot (hg hn))

end TransposeFollowup.RealMobius
