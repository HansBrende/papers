import TransposeFollowup.InitialWalkDistribution
import TransposeFollowup.SpanningProfileExclusion

/-! Strict flattening for the actual fixed rational walk family. The
nonflattening profile supplies the same localized set, frame and separated
subsets; its coefficient envelope is derived from the original level and
support estimates. The contraction exponent is fixed before the iterate
cutoff, and the generating family before the native scale and walk length. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_initial_walk_strict_flattening {γ : ℝ} (hγ : 0 < γ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧
    ∀ k : ℕ, ∃ N₀ J₀ : ℕ, 0 < N₀ ∧
    ∀ r : ℕ, 5 ≤ r → ∃ g : Fin (2^(3*r)) → Group,
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (Finset.univ.image g).card = 2^(3*r) ∧
      (Finset.univ.image (realEmbedding ∘ g)).card = 2^(3*r) ∧
      (∀ t, HasDenominator (dyadicDenominator r) (g t) ∧
        realEmbedding (g t) ∈ mobiusIdentityBall (dyadicRadius r) ∧
        (realEmbedding (g t))⁻¹ ∈ mobiusIdentityBall (dyadicRadius r)) ∧
    ∃ Jr : ℕ, max J₀ (7680*r) ≤ Jr ∧
    ∀ N j ell i : ℕ, N₀ ≤ N → Jr ≤ j → 2*N*ell ≤ j →
      Real.log (1/(1/4 : ℝ)^j)/Real.log (1/dyadicRadius r) < (ell : ℝ) → i ≤ k →
      let η := (1/4 : ℝ)^j
      let μ := generatorWalkMeasure (realEmbedding ∘ g) ell
      let V := ∫⁻ x, smoothedAutocorrelationIterate μ η i x^2 ∂(Measure.haar : Measure RealMobius.Group)
      ENNReal.ofReal (η^(-γ)) ≤ V →
      (∫⁻ x, smoothedAutocorrelationIterate μ η (i+1) x^2 ∂(Measure.haar : Measure RealMobius.Group)) <
        ENNReal.ofReal (η^s)*V := by
  let κ := min (γ/2) (1/122880 : ℝ)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκone : κ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hκγ : κ ≤ γ/2 := min_le_left _ _
  have hκdist : κ ≤ 1/122880 := min_le_right _ _
  obtain ⟨θ, α, L, Je, hθ, _hθquarter, hα, hαone, hL, hexclude⟩ :=
    SL2Projection.exists_spanning_profile_exclusion hκ hκone
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  let β := θ/(L : ℝ)
  have hβ : 0 < β := div_pos hθ hLR
  obtain ⟨s, hs, hsone, _hsk, _hsg, hsb, _hspacing, hall⟩ :=
    exists_initial_walk_spanning (ε := θ/2) (ζ := θ) hα hαone hγ hβ (by positivity) hθ
  have hLs : (L : ℝ)*s ≤ θ := by
    have hsβ : s ≤ β := by linarith only [hs, hsb]
    have hh := (le_div_iff₀ hLR).mp hsβ
    simpa only [mul_comm] using hh
  obtain ⟨η₀, hη₀, hη₀half, hbudget⟩ := exists_uniform_covering_loss_threshold hs
    (max ((2 : ℝ)^100) (α⁻¹^4))
  obtain ⟨Jη, hscale⟩ := exists_quarter_scale_threshold hη₀
  refine ⟨s, hs, hsone, ?_⟩
  intro k
  obtain ⟨No, Jo, hNo, hfamily⟩ := hall k
  obtain ⟨Ns, Js, _hNs, hsupport⟩ := exists_dyadic_walk_support_threshold hs k
  let N₀ := max No Ns
  let J₀ := max Jo (max Js (max Jη Je))
  refine ⟨N₀, J₀, hNo.trans_le (le_max_left _ _), ?_⟩
  intro r hr
  obtain ⟨g, hg, hgr, hcard, hcardr, hnear, Jr, hJr, hprofile⟩ := hfamily r hr
  refine ⟨g, hg, hgr, hcard, hcardr, hnear, max Jr J₀, ?_, ?_⟩
  · exact max_le (le_max_right _ _) ((le_max_right _ _).trans (hJr.trans (le_max_left _ _)))
  intro N j ell i hN hj hell hlog hi η μ V henergy
  apply lt_of_not_ge
  intro hnonflat
  have hNoN : No ≤ N := (le_max_left _ _).trans hN
  have hNsN : Ns ≤ N := (le_max_right _ _).trans hN
  have hjr : Jr ≤ j := (le_max_left _ _).trans hj
  have hj₀ : J₀ ≤ j := (le_max_right _ _).trans hj
  have hjs : Js ≤ j := by dsimp only [J₀] at hj₀; omega
  have hjη : Jη ≤ j := by dsimp only [J₀] at hj₀; omega
  have hje : Je ≤ j := by dsimp only [J₀] at hj₀; omega
  obtain ⟨_hV0, hVt, Nlevel, _hNl, hlevel, U, Y, x, _hU1, _hUo, hUi, _hUc, hUb, _hU0, _hUt,
    hYs, _hYi, hYcard, hYcov, _happrox, _hx, _hVlo, _hVhi, _hmass,
    hA1, _hAo, hAi, _hAc, _hAb, _hA0, _hAt, _hA3, _hHlo, _hHhi, _hVAlo, _hVAhi,
    _hnA0, _hnA3, _hn3t, _htrip, _hlo, _hhi, _hsizeLo, hsizeHi, _hsmalltrip, _hshort,
    hdistribution, _hescape, p, q, hp, hq, hpq, hdet, _hind⟩ :=
    hprofile N j ell i hNoN hjr hell hlog hi henergy hnonflat
  let A := U^2 ∩ mobiusIdentityBall α
  let R := (4*(4*(4 : ℝ)^ell)^2)^(2^i)
  let Q := 32*(R+1)^6
  let q₀ := η^s
  let qE := ENNReal.ofReal q₀
  let K₀ := 64*(Nlevel : ℝ≥0∞)^4
  let Lc := 8*(K₀^2/qE^2)
  let K := (2 : ℝ≥0∞)^55*Lc^21
  let ηn : ℝ≥0 := ⟨η, by positivity⟩
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηsmall : η ≤ η₀ := hscale j hjη
  have hηhalf : η ≤ 1/2 := hηsmall.trans hη₀half
  have hηone : η ≤ 1 := hηhalf.trans (by norm_num)
  obtain ⟨hconst, hlogscale⟩ := hbudget η hη hηsmall
  have hlarge : (2 : ℝ)^100 ≤ η^(-s) := (le_max_left _ _).trans hconst
  have hαscale : α⁻¹^4 ≤ η^(-s) := (le_max_right _ _).trans hconst
  have hVpower := ENNReal.toReal_mono hVt.ne henergy
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg hη.le (-γ))] at hVpower
  have hlevelscale := (covering_level_log_bound_of_powers hη hηhalf hsone
    (by norm_num : (0 : ℝ) ≤ 1/61440) hγ.le le_rfl hVpower hlevel).trans hlogscale
  have hQscale : Q ≤ η^(-s) := hsupport N j ell i hNsN hjs hell hi
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 1 ≤ Q := by
    have hh := one_le_pow₀ (n := 6) (show (1 : ℝ) ≤ R+1 by linarith only [hR])
    dsimp only [Q]
    linarith only [hh]
  have hq₀ : 0 < q₀ := Real.rpow_pos_of_pos hη _
  have hq₀inv : q₀⁻¹ ≤ η^(-s) := (Real.rpow_neg hη.le s).symm.le
  have hqE : qE ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq₀
  have hK₀t : K₀ ≠ ⊤ := by dsimp only [K₀]; finiteness
  have hLct : Lc ≠ ⊤ := by dsimp only [Lc]; finiteness
  have hKt : K ≠ ⊤ := by dsimp only [K]; finiteness
  have hYcardR := ENNReal.toReal_mono (show 512*K^16 ≠ ⊤ by finiteness) hYcard
  dsimp only [K, Lc, K₀, qE] at hYcardR
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hq₀.le] at hYcardR
  have hdist (ρ : ℝ) (hηρ : η < ρ) (hρ : ρ < η^(θ/2)) :
      ∃ T : Finset RealMobius.Group, (T : Set RealMobius.Group) ⊆ A ∧
        Metric.IsSeparated (ENNReal.ofReal ρ)
          ((fun x : RealMobius.Group => (x : Matrix (Fin 2) (Fin 2) ℝ)) '' (T : Set RealMobius.Group)) ∧
        ρ^(-κ) ≤ (T.card : ℝ) := by
    obtain ⟨T, hTA, hsep, hcardT⟩ := hdistribution ρ hηρ hρ
    have hρone : ρ ≤ 1 := hρ.le.trans (Real.rpow_le_one hη.le hηone (by positivity))
    exact ⟨T, hTA, hsep, (Real.rpow_le_rpow_of_exponent_ge
      (hη.trans hηρ) hρone (neg_le_neg hκdist)).trans hcardT⟩
  have hsize : (Metric.externalCoveringNumber ηn
      ((fun x : RealMobius.Group => (x : Matrix (Fin 2) (Fin 2) ℝ)) '' A) : ℝ≥0∞).toReal ≤ η^(-(3-κ)) :=
    hsizeHi.trans (Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith only [hκγ]))
  exact hexclude j hje (A := A) Y hlarge hlevelscale hQ hQscale hα le_rfl hαscale
    hq₀ hq₀inv hs.le hLs le_rfl hYcardR (fun u hu => hUb (subset_closure hu))
    hUi hYs hYcov rfl hA1 hAi hp hq hpq hdet hdist hsize

end TransposeFollowup.RationalFreePair
