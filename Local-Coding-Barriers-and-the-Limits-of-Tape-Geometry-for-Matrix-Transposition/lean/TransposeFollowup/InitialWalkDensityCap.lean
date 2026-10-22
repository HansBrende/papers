import TransposeFollowup.InitialWalkFlattening
import TransposeFollowup.AutocorrelationEnergyDescent

/-! A fixed dyadic autocorrelation power of the actual rational walk has
an arbitrarily small negative-power density cap. The exponent is chosen
first, then the iterate count and thresholds, then the generating family.
No flattening or density hypothesis remains. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_initial_walk_density_cap {γ : ℝ} (hγ : 0 < γ) :
    ∃ k N₀ J₀ : ℕ, 0 < k ∧ 0 < N₀ ∧
    ∀ r : ℕ, 5 ≤ r → ∃ g : Fin (2^(3*r)) → Group,
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (Finset.univ.image g).card = 2^(3*r) ∧
      (Finset.univ.image (realEmbedding ∘ g)).card = 2^(3*r) ∧
      (∀ t, HasDenominator (dyadicDenominator r) (g t) ∧
        realEmbedding (g t) ∈ mobiusIdentityBall (dyadicRadius r) ∧
        (realEmbedding (g t))⁻¹ ∈ mobiusIdentityBall (dyadicRadius r)) ∧
    ∃ Jr : ℕ, max J₀ (7680*r) ≤ Jr ∧
    ∀ N j ell : ℕ, N₀ ≤ N → Jr ≤ j → 2*N*ell ≤ j →
      Real.log (1/(1/4 : ℝ)^j)/Real.log (1/dyadicRadius r) < (ell : ℝ) →
      ∀ x : RealMobius.Group,
        smoothedAutocorrelationIterate (generatorWalkMeasure (realEmbedding ∘ g) ell)
          ((1/4 : ℝ)^j) k x ≤ ENNReal.ofReal (((1/4 : ℝ)^j)^(-γ)) := by
  obtain ⟨s, hs, _hsone, hflatten⟩ := exists_initial_walk_strict_flattening hγ
  obtain ⟨n, hn⟩ := exists_nat_gt (3/s)
  have hns : 3 ≤ (n : ℝ)*s := ((div_lt_iff₀ hs).mp hn).le
  obtain ⟨N₀, Jo, hN₀, hfamily⟩ := hflatten n
  obtain ⟨Ji, hinitial⟩ := exists_initial_radius_prefactor_threshold
    (512/(Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ))
  let J₀ := max Jo Ji
  refine ⟨n+1, N₀, J₀, by omega, hN₀, ?_⟩
  intro r hr
  obtain ⟨g, hg, hgr, hcard, hcardr, hnear, Jr, hJr, hflat⟩ := hfamily r hr
  refine ⟨g, hg, hgr, hcard, hcardr, hnear, max Jr J₀, ?_, ?_⟩
  · exact max_le (le_max_right _ _) ((le_max_right _ _).trans (hJr.trans (le_max_left _ _)))
  intro N j ell hN hj hell hlog x
  have hjr : Jr ≤ j := (le_max_left _ _).trans hj
  have hji : Ji ≤ j := (le_max_right _ _).trans ((le_max_right _ _).trans hj)
  have hjradius : 7680*r ≤ j := ((le_max_right _ _).trans hJr).trans hjr
  have hlen : initialWalkLength r j ≤ ell := initialWalkLength_le_of_log_threshold (by omega) hlog
  let η := (1/4 : ℝ)^j
  let μ := generatorWalkMeasure (realEmbedding ∘ g) ell
  let V := fun i : ℕ => ∫⁻ y, smoothedAutocorrelationIterate μ η i y^2 ∂(Measure.haar : Measure RealMobius.Group)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have : IsProbabilityMeasure μ := generatorWalkMeasure_probability _ (by positivity) ell
  have hbase (y : RealMobius.Group) : mobiusSmoothedDensity μ η y ≤ ENNReal.ofReal (η^(-(3 : ℝ))) := by
    have hd := later_walk_density_radius_gain hr hjradius hlen g (fun i => (hnear i).1) hgr y
    exact hd.trans (ENNReal.ofReal_le_ofReal ((hinitial j hji).trans
      (Real.rpow_le_rpow_of_exponent_ge hη hηone (by norm_num))))
  have hzero : V 0 ≤ ENNReal.ofReal (η^(-(3 : ℝ))) :=
    smoothedAutocorrelationIterate_lintegral_sq_le μ hη hbase 0
  have hterminal : (ENNReal.ofReal (η^s))^n*ENNReal.ofReal (η^(-(3 : ℝ))) ≤
      ENNReal.ofReal (η^(-γ)) := by
    rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hη.le s),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg hη.le s) n),
      ← Real.rpow_mul_natCast hη.le, ← Real.rpow_add hη]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hη hηone
      (by nlinarith only [hns, hγ]))
  have henergy : V n ≤ ENNReal.ofReal (η^(-γ)) :=
    antitone_energy_threshold_descent (smoothedAutocorrelationIterate_energy_antitone μ hη)
      hzero hterminal (fun i hi hhigh => (hflat N j ell i hN hjr hell hlog hi.le hhigh).le)
  exact (smoothedAutocorrelationIterate_succ_le_energy μ η n x).trans henergy

end TransposeFollowup.RationalFreePair
