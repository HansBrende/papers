import TransposeFollowup.SmoothedIterateWordDistribution
import TransposeFollowup.ShortWordGrowthThreshold
import TransposeFollowup.HomFamilyComplexEscape
import TransposeFollowup.FractionalDyadicIndex
import TransposeFollowup.EscapeExponentScales
import TransposeFollowup.RationalSpanCertificate

/-! Quantitative spanning and every requested positive escape exponent are attained by a shorter
terminal walk at the original smoothing radius. The fractional scale is
fixed before all families and iterates; all rounding and budgets are proved. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise commutatorElement
set_option autoImplicit false
variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]
local notation "CMat" => Matrix (Fin 2) (Fin 2) ℂ

theorem exists_iterate_spanning_escape {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ ∀ r : ℕ, 5 ≤ r → ∃ J : ℕ,
    ∀ {j ell : ℕ} {s Q α X : ℝ} {N_level : ℕ} (_hJj : J ≤ j)
    (_hlog : Real.log (1 / (1 / 4 : ℝ) ^ j) /
      Real.log (1 / dyadicRadius r) < (ell : ℝ))
    (g : Fin (2 ^ (3 * r)) → Group)
    (_hg : ∀ a, HasDenominator (dyadicDenominator r) (g a))
    (_hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    (_hG : ∀ a, realEmbedding (g a) ∈ matrixEntryBox 2) (i : ℕ)
    {U : Set RealMobius.Group} (_hU1 : 1 ∈ U) (_hUo : IsOpen U) (_hUi : U⁻¹ = U)
    (_hUb : U ⊆ matrixEntryBox Q) (_hQ : 1 ≤ Q) (_hα : 0 < α) (_hαone : α ≤ 1)
    (x : RealMobius.Group) (_hx : x ∈ matrixEntryBox X)
    (_hmargin : 1140 * s ≤ θ / 61440)
    (_hlarge : 2 ^ 100 ≤ ((1 / 4 : ℝ) ^ j) ^ (-s))
    (_hlevel : (N_level : ℝ) ≤ ((1 / 4 : ℝ) ^ j) ^ (-s))
    (_hQscale : Q ≤ ((1 / 4 : ℝ) ^ j) ^ (-s))
    (_hαscale : α⁻¹ ^ 4 ≤ ((1 / 4 : ℝ) ^ j) ^ (-s)),
    let η := (1 / 4 : ℝ) ^ j
    let q := ENNReal.ofReal (η ^ s)
    let K₀ := 64 * (N_level : ℝ≥0∞) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
    let A := U ^ 2 ∩ mobiusIdentityBall α
    q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (Measure.haar : Measure RealMobius.Group).withDensity
      (smoothedAutocorrelationIterate (generatorWalkMeasure (realEmbedding ∘ g) ell) η i) (x • U) →
    (∀ P : CMatˣ, ∃ h ∈ A ^ 4, η ^ ε ≤
      ‖SL2Escape.complexConjugation P (Matrix.SpecialLinearGroup.map Complex.ofRealHom h) 0 1 *
        SL2Escape.complexConjugation P (Matrix.SpecialLinearGroup.map Complex.ofRealHom h) 1 0‖) ∧
    ∃ p q : RealMobius.Group, p ∈ A ^ 34 ∧ q ∈ A ^ 34 ∧ p * q ∈ A ^ 34 ∧
      η ^ ε ≤ |(SL2Escape.pairSpanMatrix
        (p : Matrix (Fin 2) (Fin 2) ℝ) (q : Matrix (Fin 2) (Fin 2) ℝ)).det| ∧
      LinearIndependent ℝ (SL2Escape.pairSpanMatrix
        (p : Matrix (Fin 2) (Fin 2) ℝ) (q : Matrix (Fin 2) (Fin 2) ℝ)).col := by
  let θ := min (1 / 4 : ℝ) (ε / 68)
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθhalf : θ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hθε : 68 * θ ≤ ε := by have hh : θ ≤ ε / 68 := min_le_right _ _; linarith
  obtain ⟨Jw, hJw⟩ := FreeWordFamily.exists_short_word_bicommutator_threshold
    (by norm_num : (0 : ℝ) < 1 / 122880)
  obtain ⟨Jc, hJc⟩ := exists_escape_prefactor_threshold hε
  refine ⟨θ, hθ, hθhalf, ?_⟩
  intro r hr
  obtain ⟨Jv, hJv⟩ := exists_fractional_dyadic_index_threshold hθ hθhalf (max Jw (7680 * r))
  refine ⟨max Jc Jv, ?_⟩
  intro j ell s Q α X N_level hJj hlog g hg hfree hG i U
    hU1 hUo hUi hUb hQ hα hαone x hx hmargin hlarge hlevel hQscale hαscale
  dsimp only
  intro hmass
  obtain ⟨v, hvmax, hvj, _hvlo, hvhi, hscale⟩ := hJv j ((le_max_right _ _).trans hJj)
  have hv : 7680 * r ≤ v := (le_max_right _ _).trans hvmax
  obtain ⟨u, _hu, F, hF1, hF, hsize⟩ := exists_iterate_scaled_short_words hr hv hvj hscale
    hlog g hg hfree hG i hU1 hUo hUi hUb hQ hα hαone x hx hmargin hlarge hlevel hQscale hαscale hmass
  have ht : 2 * initialWalkLength r v ≤ 2 * v := Nat.mul_le_mul_left 2 (Nat.div_le_self _ _)
  obtain ⟨a, ha, z, hz, w, hw, hne, _hlen⟩ := hJw v ((le_max_left _ _).trans hvmax)
    F (2 * initialWalkLength r v) ht (fun v hv => (hF v hv).1) hsize
  let f := FreeGroup.lift (realEmbedding ∘ g)
  have hneR : f ⁅⁅a, z⁆, ⁅a, w⁆⁆ ≠ 1 := by
    intro he
    exact hne (hfree (by simpa only [map_one] using he))
  have hA1 : (1 : RealMobius.Group) ∈ U ^ 2 ∩ mobiusIdentityBall α :=
    ⟨Set.one_mem_pow hU1, one_mem_mobiusIdentityBall hα⟩
  have hAb : U ^ 2 ∩ mobiusIdentityBall α ⊆ matrixEntryBox 2 :=
    fun q hq => mobiusIdentityBall_subset_entryBox_two hα hαone hq.2
  have hescape := hom_family_complex_escape f
    (pow_pos (dyadicDenominator_pos r) (2 * initialWalkLength r v)) hA1 hAb F hF1
    (fun z hz => (hF z hz).2.1) u (fun z hz => (hF z hz).2.2) ha hz hw hneR
  have hvε : 34 * (v : ℝ) ≤ (j : ℝ) * ε := by
    nlinarith [mul_le_mul_of_nonneg_right hθε (Nat.cast_nonneg j)]
  have hgap := hJc j ((le_max_left _ _).trans hJj) (initial_escape_gap_of_short_index r j v hvε)
  constructor
  · intro P
    obtain ⟨h, hh, hprod⟩ := hescape P
    refine ⟨h, hh, hgap.trans ?_⟩
    simpa only [Nat.cast_pow, ← pow_mul,
      show (2 * initialWalkLength r v) * 17 = 34 * initialWalkLength r v by omega] using hprod
  · have hAi : (U ^ 2 ∩ mobiusIdentityBall α)⁻¹ = U ^ 2 ∩ mobiusIdentityBall α := by
      rw [Set.inter_inv, ← inv_pow, hUi, mobiusIdentityBall_inv]
    obtain ⟨p, q, hp, hq, hpq, hdet, hind⟩ := rational_conjugated_spanning
      (pow_pos (dyadicDenominator_pos r) (2 * initialWalkLength r v)) hA1 hAi u
      (hF a ha).2.1 (hF z hz).2.1 (hF w hw).2.1
      (hF a ha).2.2 (hF z hz).2.2 (hF w hw).2.2
      (by simpa only [map_commutatorElement] using hneR)
    refine ⟨p, q, hp, hq, hpq, ?_, hind⟩
    apply le_trans _ hdet
    have hη : (0 : ℝ) < (1 / 4 : ℝ) ^ j := by positivity
    calc
      ((1 / 4 : ℝ) ^ j) ^ ε = (((1 / 4 : ℝ) ^ j) ^ (ε / 2)) ^ 2 := by
        rw [pow_two, ← Real.rpow_add hη]
        congr 1
        ring
      _ ≤ (1 / (dyadicDenominator r : ℝ) ^ (34 * initialWalkLength r v)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hη.le _) (initial_escape_gap_of_short_index r j v hvε) 2
      _ = 1 / ((dyadicDenominator r ^ (2 * initialWalkLength r v) : ℕ) : ℝ) ^ 34 := by
        simp only [Nat.cast_pow, one_div_pow, ← pow_mul]
        congr 2
        omega


end TransposeFollowup.RationalFreePair
