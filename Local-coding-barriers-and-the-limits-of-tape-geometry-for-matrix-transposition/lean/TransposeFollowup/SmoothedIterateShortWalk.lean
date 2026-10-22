import TransposeFollowup.SmoothedIterateEndpoint
import TransposeFollowup.AutocorrelationIterateCoefficient
import TransposeFollowup.GeneratorWalkSymmetry

/-! Every actual iterate retains any shorter terminal walk followed by
the original smoothing kernel. The remaining probability measure has
an explicit bounded support; factors are only reassociated. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem smoothedAutocorrelationIterate_right_shortWalk {m : ℕ} (G : Fin m → Group)
    (hm : 0 < m) (hG : ∀ a, G a ∈ matrixEntryBox 2) {η : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (ell k : ℕ) {t : ℕ} (ht : t ≤ ell) :
    let B := 4 * (4 : ℝ) ^ ell
    let R := (4 * B ^ 2) ^ (2 ^ k)
    ∃ ν : Measure Group, IsProbabilityMeasure ν ∧
      (∀ᵐ a ∂ν, a ∈ matrixEntryBox R) ∧
      (Measure.haar : Measure Group).withDensity
          (smoothedAutocorrelationIterate (generatorWalkMeasure G ell) η k) =
        ν ∗ₘ (generatorWalkMeasure G t ∗ₘ mobiusHaarKernel η) := by
  dsimp only
  let μ := generatorWalkMeasure G ell
  let σ := μ ∗ₘ mobiusHaarKernel η
  let a := σ.inv ∗ₘ σ
  let β := measureConvolutionPower a (2 ^ k - 1)
  let tail := generatorWalkMeasure G (ell - t)
  let ν := (β ∗ₘ σ.inv) ∗ₘ tail
  let B := 4 * (4 : ℝ) ^ ell
  let P := (4 * B ^ 2) ^ (2 ^ k - 1)
  have : IsProbabilityMeasure μ := generatorWalkMeasure_probability G hm ell
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure σ.inv := inv_measure_probability σ
  have : IsProbabilityMeasure a := inferInstance
  have : IsProbabilityMeasure β := measureConvolutionPower_probability _ _
  have : IsProbabilityMeasure tail := generatorWalkMeasure_probability G hm _
  have : IsProbabilityMeasure (generatorWalkMeasure G t) := generatorWalkMeasure_probability G hm t
  have hs : ∀ᵐ g ∂σ, g ∈ matrixEntryBox B := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      generatorWalk_smoothed_ae_entryBox G hm hG hη hηone ell
  have hβ : ∀ᵐ g ∂β, g ∈ matrixEntryBox P := by
    simpa only [show 2 * (2 * B ^ 2) = 4 * B ^ 2 by ring] using
      measureConvolutionPower_ae_entryBox a (autocorrelation_ae_matrixEntryBox σ hs) (2 ^ k - 1)
  have htail : ∀ᵐ g ∂tail, g ∈ matrixEntryBox ((4 : ℝ) ^ (ell - t)) := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      generatorWalkMeasure_ae_entryBox G hm hG (ell - t)
  have hν := mconv_ae_matrixEntryBox (β ∗ₘ σ.inv) tail
    (mconv_ae_matrixEntryBox β σ.inv hβ (inv_ae_matrixEntryBox σ hs)) htail
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hbound : 2 * (2 * P * B) * (4 : ℝ) ^ (ell - t) ≤ (4 * B ^ 2) ^ (2 ^ k) := by
    calc
      _ ≤ 2 * (2 * P * B) * (4 : ℝ) ^ ell := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) (by positivity)
      _ = P * B ^ 2 := by dsimp only [B]; ring
      _ ≤ P * (4 * B ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg B]) hP
      _ = _ := by
        dsimp only [P]
        rw [← pow_succ]
        congr 1
        have := Nat.two_pow_pos k
        omega
  refine ⟨ν, inferInstance, hν.mono (fun g hg i j => (hg i j).trans hbound), ?_⟩
  have hwalk : μ = tail ∗ₘ generatorWalkMeasure G t := by
    rw [← generatorWalkMeasure_add G hm, Nat.sub_add_cancel ht]
  calc
    _ = (β ∗ₘ σ.inv) ∗ₘ (μ ∗ₘ mobiusHaarKernel η) :=
      smoothedAutocorrelationIterate_split_last μ hη k
    _ = (β ∗ₘ σ.inv) ∗ₘ ((tail ∗ₘ generatorWalkMeasure G t) ∗ₘ mobiusHaarKernel η) := by rw [hwalk]
    _ = ν ∗ₘ (generatorWalkMeasure G t ∗ₘ mobiusHaarKernel η) := by
      dsimp only [ν]
      simp only [Measure.mconv_assoc]

end TransposeFollowup.RealMobius
