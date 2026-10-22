import TransposeFollowup.SmoothedIterateSeparatedSubset
import TransposeFollowup.SeparatedCardinalityPower
import TransposeFollowup.DyadicSeparationInterpolation
import TransposeFollowup.SeparatedPowerAbsorption

/-! The actual localized iterate witness satisfies a pure power-law
separation bound at every intermediate real radius once its proved
coefficient budgets and a fixed exponent margin are supplied. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_iterate_separated_subset {r j ell : ℕ} {s ε Q α X : ℝ} {N_level : ℕ}
    (hr : 5 ≤ r)
    (hlog : Real.log (1 / (1 / 4 : ℝ) ^ j) /
      Real.log (1 / dyadicRadius r) < (ell : ℝ))
    (g : Fin (2 ^ (3 * r)) → Group)
    (hg : ∀ a, HasDenominator (dyadicDenominator r) (g a))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    (hG : ∀ a, realEmbedding (g a) ∈ matrixEntryBox 2) (i : ℕ)
    {U : Set RealMobius.Group} (hU1 : 1 ∈ U) (hUo : IsOpen U) (hUi : U⁻¹ = U)
    (hUb : U ⊆ matrixEntryBox Q) (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1)
    (x : RealMobius.Group) (hx : x ∈ matrixEntryBox X)
    (hmargin : 1140 * s ≤ ε / 61440)
    (hwindow : ((1 / 4 : ℝ) ^ j) ^ ε ≤ min (1 / 256) ((1 / 4 : ℝ) ^ (7680 * r)))
    (hlarge : 2 ^ 100 ≤ ((1 / 4 : ℝ) ^ j) ^ (-s))
    (hlevel : (N_level : ℝ) ≤ ((1 / 4 : ℝ) ^ j) ^ (-s))
    (hQscale : Q ≤ ((1 / 4 : ℝ) ^ j) ^ (-s))
    (hαscale : α⁻¹ ^ 4 ≤ ((1 / 4 : ℝ) ^ j) ^ (-s)) :
    let η := (1 / 4 : ℝ) ^ j
    let q := ENNReal.ofReal (η ^ s)
    let K₀ := 64 * (N_level : ℝ≥0∞) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
    q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (Measure.haar : Measure RealMobius.Group).withDensity
      (smoothedAutocorrelationIterate (generatorWalkMeasure (realEmbedding ∘ g) ell) η i) (x • U) →
    ∀ ρ : ℝ, η < ρ → ρ < η ^ ε →
      ∃ F : Finset RealMobius.Group, (F : Set RealMobius.Group) ⊆ U ^ 2 ∩ mobiusIdentityBall α ∧
        Metric.IsSeparated (ENNReal.ofReal ρ)
          ((fun a : RealMobius.Group => (a : Matrix (Fin 2) (Fin 2) ℝ)) '' (F : Set RealMobius.Group)) ∧
        ρ ^ (-(1 / 122880 : ℝ)) ≤ (F.card : ℝ) := by
  dsimp only
  intro hmass ρ hηρ hρupper
  let η := (1 / 4 : ℝ) ^ j
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hρ : 0 < ρ := hη.trans hηρ
  have hρsmall : ρ ≤ 1 / 256 := hρupper.le.trans (hwindow.trans (min_le_left _ _))
  have hρJ : ρ ≤ (1 / 4 : ℝ) ^ (7680 * r) := hρupper.le.trans (hwindow.trans (min_le_right _ _))
  obtain ⟨v, hv, hvj, hρv, hvρ⟩ := exists_quarter_scale_between hηρ hρJ
  have hθ : 0 < η ^ s := Real.rpow_pos_of_pos hη s
  obtain ⟨F, hFA, hsep, hcount⟩ := exists_iterate_dyadic_separated_subset hr hv hvj hlog g hg hfree hG i
    hU1 hUo hUi hUb hQ hα hαone x hx
    (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr hθ) 2) hmass
  have hm := separated_cardinality_power_bound hlarge hlevel (zero_le_one.trans hQ) hQscale
    hα hαscale hθ (le_of_eq (Real.rpow_neg hη.le s).symm)
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ v) (1 / 30720 : ℝ))
    (by simpa only [← mul_assoc, show (4 : ℝ≥0∞) * 8192 = 32768 by norm_num] using hcount)
  have he : (η ^ (-s)) ^ (1140 : ℕ) = η ^ (-(1140 * s)) := by
    rw [← Real.rpow_mul_natCast hη.le]
    congr 1
    norm_num
    ring
  rw [he] at hm
  have hcard := separated_power_absorption hη hηone hρ hρsmall hρupper.le
    (by norm_num : (0 : ℝ) < 1 / 30720)
    (by convert hmargin using 1; ring)
    (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ v) hvρ.le (Nat.cast_nonneg F.card) hm
  refine ⟨F, hFA, hsep.anti (ENNReal.ofReal_le_ofReal hρv), ?_⟩
  simpa only [show -(1 / 30720 : ℝ) / 4 = -(1 / 122880 : ℝ) by norm_num] using hcard

end TransposeFollowup.RationalFreePair
