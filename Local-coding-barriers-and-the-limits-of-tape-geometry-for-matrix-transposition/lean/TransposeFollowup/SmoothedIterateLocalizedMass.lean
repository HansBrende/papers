import TransposeFollowup.MobiusLocalizedProbability
import TransposeFollowup.SmoothedIterateShortWalk
import TransposeFollowup.ConvolutionTranslateMass

/-! The actual iterate's concentration on a translate of U transfers to
the same localized set A for every shorter smoothed walk, with explicit
probability loss and a bounded translating element. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_shortWalk_localized_mass {m : ℕ} (G : Fin m → Group) (hm : 0 < m)
    (hG : ∀ a, G a ∈ matrixEntryBox 2) {η : ℝ} (hη : 0 < η) (hηone : η ≤ 1)
    (ell k : ℕ) {t : ℕ} (ht : t ≤ ell) {U : Set Group} {Q α X : ℝ}
    (hU1 : 1 ∈ U) (hUo : IsOpen U) (hUi : U⁻¹ = U) (hUb : U ⊆ matrixEntryBox Q)
    (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1) (x : Group) (hx : x ∈ matrixEntryBox X)
    {c C : ℝ≥0∞} (hc : 0 < c)
    (hmass : c ≤ C * (Measure.haar : Measure Group).withDensity
      (smoothedAutocorrelationIterate (generatorWalkMeasure G ell) η k) (x • U)) :
    let B := 4 * (4 : ℝ) ^ ell
    let R := (4 * B ^ 2) ^ (2 ^ k)
    let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
    let A := U ^ 2 ∩ mobiusIdentityBall α
    ∃ w ∈ matrixEntryBox (4 * R * X * Q),
      c ≤ 2 * C * M * (generatorWalkMeasure G t ∗ₘ mobiusHaarKernel η) (w • A) := by
  dsimp only
  let σ := (Measure.haar : Measure Group).withDensity
    (smoothedAutocorrelationIterate (generatorWalkMeasure G ell) η k)
  let A := U ^ 2 ∩ mobiusIdentityBall α
  let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
  let R := (4 * (4 * (4 : ℝ) ^ ell) ^ 2) ^ (2 ^ k)
  have : IsProbabilityMeasure (generatorWalkMeasure G ell) := generatorWalkMeasure_probability G hm ell
  have : IsProbabilityMeasure (generatorWalkMeasure G t) := generatorWalkMeasure_probability G hm t
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure σ := smoothedAutocorrelationIterate_probability _ hη k
  obtain ⟨z, hz, hloc⟩ := exists_near_identity_translate_mass σ ⟨1, hU1⟩ hQ hα hαone hUb hUi x
  have hm' : c ≤ C * M * σ ((x * z) • A) := hmass.trans (by
    simpa only [mul_assoc] using mul_le_mul' (le_refl C) hloc)
  have hp : 0 < σ ((x * z) • A) := by
    by_contra hn
    have hz : σ ((x * z) • A) = 0 := le_antisymm (not_lt.mp hn) bot_le
    rw [hz, mul_zero] at hm'
    exact (not_le_of_gt hc) hm'
  have hU2o : IsOpen (U ^ 2) := by simpa only [pow_two] using hUo.mul_right
  have hAo : IsOpen A := hU2o.inter (mobiusIdentityBall_isOpen α)
  obtain ⟨ν, hν, hνsupport, he⟩ := smoothedAutocorrelationIterate_right_shortWalk G hm hG hη hηone ell k ht
  have : IsProbabilityMeasure ν := hν
  obtain ⟨a, ha, hamass⟩ := exists_translate_mass_of_mconv ν
    (generatorWalkMeasure G t ∗ₘ mobiusHaarKernel η)
    (hAo.measurableSet.const_smul (x * z)) hνsupport hp (measure_ne_top σ _)
    (by rw [← he])
  have hpre : (a * ·) ⁻¹' ((x * z) • A) = (a⁻¹ * (x * z)) • A := by
    change (fun b => a • b) ⁻¹' ((x * z) • A) = _
    rw [Set.preimage_smul, smul_smul]
  rw [hpre] at hamass
  refine ⟨a⁻¹ * (x * z), ?_, ?_⟩
  · have hb := matrixEntryBox_mul (matrixEntryBox_inv ha) (matrixEntryBox_mul hx (hUb hz))
    change a⁻¹ * (x * z) ∈ matrixEntryBox (2 * R * (2 * X * Q)) at hb
    simpa only [show 2 * R * (2 * X * Q) = 4 * R * X * Q by ring] using hb
  · calc
      c ≤ C * M * σ ((x * z) • A) := hm'
      _ ≤ C * M * (2 * (generatorWalkMeasure G t ∗ₘ mobiusHaarKernel η) ((a⁻¹ * (x * z)) • A)) :=
        mul_le_mul' le_rfl hamass
      _ = _ := by ring

end TransposeFollowup.RealMobius
