import TransposeFollowup.DyadicWalkSeparatedSubset
import TransposeFollowup.SmoothedIterateLocalizedMass
import TransposeFollowup.DyadicWalkLengthThreshold

/-! The actual nonflattening witness yields separated subsets at every
admissible dyadic scale. The shorter length is proved to fit inside the
selected walk. Neither smoothing nor translation introduces a scale cutoff. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_iterate_dyadic_separated_subset {r j v ell : ℕ}
    (hr : 5 ≤ r) (hv : 7680 * r ≤ v) (hvj : v ≤ j)
    (hlog : Real.log (1 / (1 / 4 : ℝ) ^ j) /
      Real.log (1 / dyadicRadius r) < (ell : ℝ))
    (g : Fin (2 ^ (3 * r)) → Group)
    (hg : ∀ a, HasDenominator (dyadicDenominator r) (g a))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    (hG : ∀ a, realEmbedding (g a) ∈ matrixEntryBox 2) (i : ℕ)
    {U : Set RealMobius.Group} {Q α X : ℝ}
    (hU1 : 1 ∈ U) (hUo : IsOpen U) (hUi : U⁻¹ = U) (hUb : U ⊆ matrixEntryBox Q)
    (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1)
    (x : RealMobius.Group) (hx : x ∈ matrixEntryBox X)
    {c C : ℝ≥0∞} (hc : 0 < c)
    (hmass : c ≤ C * (Measure.haar : Measure RealMobius.Group).withDensity
      (smoothedAutocorrelationIterate (generatorWalkMeasure (realEmbedding ∘ g) ell)
        ((1 / 4 : ℝ) ^ j) i) (x • U)) :
    let A := U ^ 2 ∩ mobiusIdentityBall α
    let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
    ∃ F : Finset RealMobius.Group, (F : Set RealMobius.Group) ⊆ A ∧
      Metric.IsSeparated (ENNReal.ofReal ((1 / 4 : ℝ) ^ v))
        ((fun a : RealMobius.Group => (a : Matrix (Fin 2) (Fin 2) ℝ)) '' (F : Set RealMobius.Group)) ∧
      c ≤ 4 * C * M * (F.card : ℝ≥0∞) *
        ENNReal.ofReal (((1 / 4 : ℝ) ^ v) ^ (1 / 30720 : ℝ)) := by
  dsimp only
  let η := (1 / 4 : ℝ) ^ j
  let t := initialWalkLength r v
  let A := U ^ 2 ∩ mobiusIdentityBall α
  let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
  have hm : 0 < (2 : ℕ) ^ (3 * r) := by positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht : t ≤ ell := (Nat.div_le_div_right hvj).trans
    (initialWalkLength_le_of_log_threshold (by omega) hlog)
  obtain ⟨w, _, hw⟩ := exists_shortWalk_localized_mass (realEmbedding ∘ g) hm hG
    hη hηone ell i ht hU1 hUo hUi hUb hQ hα hαone x hx hc hmass
  let μ := generatorWalkMeasure (realEmbedding ∘ g) t ∗ₘ mobiusHaarKernel η
  have : IsProbabilityMeasure (generatorWalkMeasure (realEmbedding ∘ g) t) :=
    generatorWalkMeasure_probability _ hm t
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have hp : 0 < μ (w • A) := by
    by_contra hn
    have hz : μ (w • A) = 0 := le_antisymm (not_lt.mp hn) bot_le
    change c ≤ 2 * C * M * μ (w • A) at hw
    rw [hz, mul_zero] at hw
    exact (not_le_of_gt hc) hw
  have hU2o : IsOpen (U ^ 2) := by simpa only [pow_two] using hUo.mul_right
  obtain ⟨F, hFA, hsep, hcount⟩ := exists_dyadic_walk_separated_subset hr hv g hg hfree hη hηone
    (hU2o.inter (mobiusIdentityBall_isOpen α)).measurableSet
    (fun a ha => mobiusIdentityBall_subset_entryBox_two hα hαone ha.2) w hp (measure_ne_top μ _) le_rfl
  refine ⟨F, hFA, hsep, ?_⟩
  calc
    c ≤ 2 * C * M * μ (w • A) := hw
    _ ≤ 2 * C * M * (2 * (F.card : ℝ≥0∞) *
        ENNReal.ofReal (((1 / 4 : ℝ) ^ v) ^ (1 / 30720 : ℝ))) := mul_le_mul' le_rfl hcount
    _ = _ := by ring

end TransposeFollowup.RationalFreePair
