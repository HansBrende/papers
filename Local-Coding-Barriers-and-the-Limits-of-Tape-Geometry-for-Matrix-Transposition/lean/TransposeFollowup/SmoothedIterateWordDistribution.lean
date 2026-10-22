import TransposeFollowup.SmoothedIterateShortWords
import TransposeFollowup.DyadicWalkLengthThreshold
import TransposeFollowup.InitialWalkRadiusGain
import TransposeFollowup.SeparatedCardinalityPower
import TransposeFollowup.SeparatedPowerAbsorption

/-! The actual profile's coefficient budgets force a power-law number of
normalized short words. This retains the free-group witnesses needed for
algebraic escape, rather than only separated real-matrix images. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_iterate_scaled_short_words {r j v ell : ℕ} {s Q α X θ : ℝ} {N_level : ℕ}
    (hr : 5 ≤ r) (hv : 7680 * r ≤ v) (hvj : v ≤ j)
    (hscale : (1 / 4 : ℝ) ^ v ≤ ((1 / 4 : ℝ) ^ j) ^ θ)
    (hlog : Real.log (1 / (1 / 4 : ℝ) ^ j) /
      Real.log (1 / dyadicRadius r) < (ell : ℝ))
    (g : Fin (2 ^ (3 * r)) → Group)
    (hg : ∀ a, HasDenominator (dyadicDenominator r) (g a))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    (hG : ∀ a, realEmbedding (g a) ∈ matrixEntryBox 2) (i : ℕ)
    {U : Set RealMobius.Group} (hU1 : 1 ∈ U) (hUo : IsOpen U) (hUi : U⁻¹ = U)
    (hUb : U ⊆ matrixEntryBox Q) (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1)
    (x : RealMobius.Group) (hx : x ∈ matrixEntryBox X)
    (hmargin : 1140 * s ≤ θ / 61440)
    (hlarge : 2 ^ 100 ≤ ((1 / 4 : ℝ) ^ j) ^ (-s))
    (hlevel : (N_level : ℝ) ≤ ((1 / 4 : ℝ) ^ j) ^ (-s))
    (hQscale : Q ≤ ((1 / 4 : ℝ) ^ j) ^ (-s))
    (hαscale : α⁻¹ ^ 4 ≤ ((1 / 4 : ℝ) ^ j) ^ (-s)) :
    let η := (1 / 4 : ℝ) ^ j
    let ρ := (1 / 4 : ℝ) ^ v
    let q := ENNReal.ofReal (η ^ s)
    let K₀ := 64 * (N_level : ℝ≥0∞) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
    let A := U ^ 2 ∩ mobiusIdentityBall α
    let t := initialWalkLength r v
    q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (Measure.haar : Measure RealMobius.Group).withDensity
      (smoothedAutocorrelationIterate (generatorWalkMeasure (realEmbedding ∘ g) ell) η i) (x • U) →
    ∃ u ∈ mobiusIdentityBall η, ∃ F : Finset (FreeGroup (Fin (2 ^ (3 * r)))), 1 ∈ F ∧
      (∀ v ∈ F, FreeGroup.norm v ≤ 2 * t ∧
        FreeGroup.lift (realEmbedding ∘ g) v ∈ denominatorCarrier ((dyadicDenominator r) ^ (2 * t)) ∧
        u⁻¹ * FreeGroup.lift (realEmbedding ∘ g) v * u ∈ A ^ 2) ∧
      ρ ^ (-(1 / 122880 : ℝ)) ≤ (F.card : ℝ) := by
  dsimp only
  intro hmass
  let η := (1 / 4 : ℝ) ^ j
  let ρ := (1 / 4 : ℝ) ^ v
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hρsmall : ρ ≤ 1 / 256 := by
    calc
      _ ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = _ := by norm_num
  have hm : 0 < (2 : ℕ) ^ (3 * r) := by positivity
  have hε := dyadicRadius_pos r
  have hκ : 1 ≤ 1 / dyadicRadius r := (le_div_iff₀ hε).mpr (by simpa using dyadicRadius_le_one r)
  have hcard : (1 / dyadicRadius r) ^ 2 ≤ 2 * ((2 ^ (3 * r) : ℕ) : ℝ) := by
    have hh := pow_le_pow_right₀ hκ (by norm_num : (2 : ℕ) ≤ 3)
    rw [dyadicFamily_mass] at hh
    have hm0 : (0 : ℝ) ≤ ((2 ^ (3 * r) : ℕ) : ℝ) := by positivity
    linarith
  have hθ : 0 < η ^ s := Real.rpow_pos_of_pos hη s
  obtain ⟨u, hu, F, hF1, hF, hcount⟩ := exists_iterate_normalized_short_words g hm hg hfree hG hκ hcard
    hη hηone ell i ((Nat.div_le_div_right hvj).trans
      (initialWalkLength_le_of_log_threshold (by omega) hlog))
    hU1 hUo hUi hUb hQ hα hαone x hx
    (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr hθ) 2) hmass
  have hatom : (2 / (1 / dyadicRadius r)) ^ initialWalkLength r v ≤ ρ ^ (1 / 30720 : ℝ) := by
    simpa only [div_div_eq_mul_div, div_one] using initial_walk_factor_radius_le hr hv
  have hcount' := hcount.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hatom))
  have hpow := separated_cardinality_power_bound hlarge hlevel (zero_le_one.trans hQ) hQscale
    hα hαscale hθ (le_of_eq (Real.rpow_neg hη.le s).symm)
    (Real.rpow_nonneg hρ.le (1 / 30720 : ℝ))
    (by simpa only [← mul_assoc, show (4 : ℝ≥0∞) * 8192 = 32768 by norm_num] using hcount')
  have he : (η ^ (-s)) ^ (1140 : ℕ) = η ^ (-(1140 * s)) := by
    rw [← Real.rpow_mul_natCast hη.le]
    congr 1
    norm_num
    ring
  rw [he] at hpow
  have hsize := separated_power_absorption hη hηone hρ hρsmall hscale (by norm_num : (0 : ℝ) < 1 / 30720)
    (by convert hmargin using 1; ring) hρ.le (show ρ ≤ 4 * ρ by linarith)
    (Nat.cast_nonneg F.card) hpow
  refine ⟨u, hu, F, hF1, hF, ?_⟩
  simpa only [show -(1 / 30720 : ℝ) / 4 = -(1 / 122880 : ℝ) by norm_num] using hsize


end TransposeFollowup.RationalFreePair
