import TransposeFollowup.InitialWalkLocalizedMass
import TransposeFollowup.SmoothedIterateDistribution
import TransposeFollowup.SmoothedIterateSmallEscape

/-! One fixed rational free family supplies the full covering profile,
short-walk concentration, and pure power-law separated subsets at every
intermediate real radius, together with escape at any requested positive
exponent after every invertible complex basis change, and a quantitative
four-matrix spanning certificate inside A^34. Only energy threshold and nonflattening remain
analytic premises; all coefficient, support and scale budgets are derived. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_initial_walk_spanning {α γ β ε ζ : ℝ}
    (hα : 0 < α) (hαone : α ≤ 1) (hγ : 0 < γ) (hβ : 0 < β) (hε : 0 < ε) (hζ : 0 < ζ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ 30000 * s ≤ (1 / 61440 : ℝ) / 2 ∧
      30000 * s ≤ γ / 2 ∧ 30000 * s ≤ β ∧ 1140 * s ≤ ε / 61440 ∧
    ∀ k : ℕ, ∃ N₀ J₀ : ℕ, 0 < N₀ ∧
    ∀ r : ℕ, 5 ≤ r → ∃ g : Fin (2 ^ (3 * r)) → Group,
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (Finset.univ.image g).card = 2 ^ (3 * r) ∧
      (Finset.univ.image (realEmbedding ∘ g)).card = 2 ^ (3 * r) ∧
      (∀ t, HasDenominator (dyadicDenominator r) (g t) ∧
        realEmbedding (g t) ∈ mobiusIdentityBall (dyadicRadius r) ∧
        (realEmbedding (g t))⁻¹ ∈ mobiusIdentityBall (dyadicRadius r)) ∧
    ∃ Jr : ℕ, max J₀ (7680 * r) ≤ Jr ∧
    ∀ N j ell i : ℕ, N₀ ≤ N → Jr ≤ j → 2 * N * ell ≤ j →
      Real.log (1 / (1 / 4 : ℝ) ^ j) / Real.log (1 / dyadicRadius r) < (ell : ℝ) → i ≤ k →
    let η := (1 / 4 : ℝ) ^ j
    let μ := generatorWalkMeasure (realEmbedding ∘ g) ell
    let B := 4 * (4 : ℝ) ^ ell
    let C := η ^ (-3 + 1 / 61440 : ℝ)
    ENNReal.ofReal (η ^ (-γ)) ≤
      (∫⁻ x, smoothedAutocorrelationIterate μ η i x ^ 2 ∂(Measure.haar : Measure RealMobius.Group)) →
    ENNReal.ofReal (η ^ s) *
      (∫⁻ x, smoothedAutocorrelationIterate μ η i x ^ 2 ∂(Measure.haar : Measure RealMobius.Group)) ≤
      (∫⁻ x, smoothedAutocorrelationIterate μ η (i + 1) x ^ 2 ∂(Measure.haar : Measure RealMobius.Group)) →
    let θ := η ^ s
    let H : Measure RealMobius.Group := Measure.haar
    let f := smoothedAutocorrelationIterate μ η i
    let V := ∫⁻ x, f x ^ 2 ∂H
    let q := ENNReal.ofReal θ
    let R := (4 * B ^ 2) ^ (2 ^ i)
    let Q := 32 * (R + 1) ^ 6
    let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
    let ι := fun g : RealMobius.Group => (g : Matrix (Fin 2) (Fin 2) ℝ)
    0 < V ∧ V < ⊤ ∧
    ∃ N_level : ℕ, 0 < N_level ∧ (N_level : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / (θ * V.toReal))) ∧
      let K₀ := 64 * (N_level : ℝ≥0∞) ^ 4
      let L := 8 * (K₀ ^ 2 / q ^ 2)
      let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
      let A₆ := ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52)
      let D := 393216 ^ 4 * A₆ * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100) * M
      ∃ (U : Set RealMobius.Group) (Y : Finset RealMobius.Group) (x : RealMobius.Group),
        1 ∈ U ∧ IsOpen U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
        closure U ⊆ matrixEntryBox Q ∧ 0 < H U ∧ H U < ⊤ ∧
        (Y : Set RealMobius.Group) ⊆ U ^ 2 ∧ (Y : Set RealMobius.Group)⁻¹ = (Y : Set RealMobius.Group) ∧
        (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 ∧ U ^ 2 ⊆ (Y : Set RealMobius.Group) * U ∧
        IsApproximateSubgroup (512 * K ^ 16).toReal U ∧ x ∈ matrixEntryBox (R + 1) ∧
        q ≤ 128 * K₀ * K * L ^ 2 * V * H U ∧ q * V * H U ≤ 16 * K ^ 7 * K₀ ∧
        q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (H.withDensity f) (x • U) ∧
        let A := U ^ 2 ∩ mobiusIdentityBall α
        let nA : ℝ≥0∞ := Metric.externalCoveringNumber ⟨η, (by positivity : 0 ≤ η)⟩ (ι '' A)
        let n₃ : ℝ≥0∞ := Metric.externalCoveringNumber ⟨η, (by positivity : 0 ≤ η)⟩ (ι '' (A ^ 3))
        1 ∈ A ∧ IsOpen A ∧ A⁻¹ = A ∧ IsCompact (closure A) ∧
        closure A ⊆ matrixEntryBox 2 ∧ 0 < H A ∧ H A < ⊤ ∧ A ^ 3 ⊆ U ^ 6 ∧
        H U ≤ M * H A ∧ H A ≤ 512 * K ^ 16 * H U ∧
        q ≤ 128 * K₀ * K * L ^ 2 * M * V * H A ∧ q * V * H A ≤ 8192 * K₀ * K ^ 23 ∧
        0 < nA ∧ nA ≤ n₃ ∧ n₃ < ⊤ ∧
        n₃ * q ^ 2 ≤ 6561 * D * nA ∧
        q ≤ 128 * 6561 * 393216 ^ 4 * K₀ * K * L ^ 2 * M * V * nA * H (mobiusIdentityBall η) ∧
        nA * q ^ 3 * V * H (mobiusIdentityBall η) ≤ A₆ * 2 ^ 72 * K₀ ^ 2 * L ^ 2 * K ^ 107 ∧
        η ^ (-(1 / 61440 : ℝ) / 2) ≤ nA.toReal ∧ nA.toReal ≤ η ^ (-3 + γ / 2) ∧
        n₃.toReal ≤ η ^ (-β) * nA.toReal ∧
        (∀ t : ℕ, t ≤ ell → ∃ w ∈ matrixEntryBox (4 * R * (R + 1) * Q),
          q ^ 2 ≤ 16384 * K₀ * L ^ 2 * K ^ 4 * M *
            (generatorWalkMeasure (realEmbedding ∘ g) t ∗ₘ mobiusHaarKernel η) (w • A)) ∧
        (∀ ρ : ℝ, η < ρ → ρ < η ^ ε →
          ∃ F : Finset RealMobius.Group, (F : Set RealMobius.Group) ⊆ A ∧
            Metric.IsSeparated (ENNReal.ofReal ρ) (ι '' (F : Set RealMobius.Group)) ∧
            ρ ^ (-(1 / 122880 : ℝ)) ≤ (F.card : ℝ)) ∧
        (∀ P : (Matrix (Fin 2) (Fin 2) ℂ)ˣ, ∃ h ∈ A ^ 4, η ^ ζ ≤
          ‖SL2Escape.complexConjugation P (Matrix.SpecialLinearGroup.map Complex.ofRealHom h) 0 1 *
            SL2Escape.complexConjugation P (Matrix.SpecialLinearGroup.map Complex.ofRealHom h) 1 0‖) ∧
        ∃ p q : RealMobius.Group, p ∈ A ^ 34 ∧ q ∈ A ^ 34 ∧ p * q ∈ A ^ 34 ∧
          η ^ ζ ≤ |(SL2Escape.pairSpanMatrix
            (p : Matrix (Fin 2) (Fin 2) ℝ) (q : Matrix (Fin 2) (Fin 2) ℝ)).det| ∧
          LinearIndependent ℝ (SL2Escape.pairSpanMatrix
            (p : Matrix (Fin 2) (Fin 2) ℝ) (q : Matrix (Fin 2) (Fin 2) ℝ)).col := by
  obtain ⟨θ, hθ, _hθhalf, hEscape⟩ := exists_iterate_spanning_escape hζ
  let β' := min β (min (ε / 10000) (θ / 10000))
  have hβ' : 0 < β' := lt_min hβ (lt_min (by positivity) (by positivity))
  obtain ⟨s, hs, hsone, hsk, hsg, hsb, hall⟩ := exists_initial_walk_localized_mass hα hαone hγ hβ'
  have hsb' : 30000 * s ≤ β := hsb.trans (min_le_left _ _)
  have hmargin : 1140 * s ≤ ε / 61440 := by
    have hh : 30000 * s ≤ ε / 10000 :=
      (hsb.trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith
  have hEscapeMargin : 1140 * s ≤ θ / 61440 := by
    have hh : 30000 * s ≤ θ / 10000 :=
      (hsb.trans (min_le_right _ _)).trans (min_le_right _ _)
    linarith
  refine ⟨s, hs, hsone, hsk, hsg, hsb', hmargin, ?_⟩
  intro k
  obtain ⟨No, Jo, hNo, hfamily⟩ := hall k
  obtain ⟨Ns, Js, _, hsupport⟩ := exists_dyadic_walk_support_threshold hs k
  obtain ⟨η₀, hη₀, hη₀half, hbudget⟩ := exists_uniform_covering_loss_threshold hs
    (max ((2 : ℝ) ^ 100) (α⁻¹ ^ 4))
  obtain ⟨Jη, hscale⟩ := exists_quarter_scale_threshold hη₀
  let N₀ := max No Ns
  let J₀ := max Jo (max Js Jη)
  refine ⟨N₀, J₀, hNo.trans_le (le_max_left _ _), ?_⟩
  intro r hr
  obtain ⟨g, hg, hgr, hcard, hcardr, hnear, hcover⟩ := hfamily r hr
  obtain ⟨Jw, hwindow⟩ := exists_separation_window_threshold hε (7680 * r)
  obtain ⟨Je, hEsc⟩ := hEscape r hr
  let Jr := max J₀ (max (7680 * r) (max Jw Je))
  have hJr : max J₀ (7680 * r) ≤ Jr := max_le (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨g, hg, hgr, hcard, hcardr, hnear, Jr, hJr, ?_⟩
  intro N j ell i hN hj hell hlog hi
  dsimp only
  intro henergy hnonflat
  have hNoN : No ≤ N := (le_max_left _ _).trans hN
  have hNsN : Ns ≤ N := (le_max_right _ _).trans hN
  have hj₀ : J₀ ≤ j := (le_max_left _ _).trans hj
  have hjo : max Jo (7680 * r) ≤ j := max_le
    ((le_max_left _ _).trans hj₀) ((le_max_right _ _).trans (hJr.trans hj))
  have hjs : Js ≤ j := (le_max_left _ _).trans ((le_max_right _ _).trans hj₀)
  have hjη : Jη ≤ j := (le_max_right _ _).trans ((le_max_right _ _).trans hj₀)
  have hjw : Jw ≤ j := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hj))
  have hje : Je ≤ j := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hj))
  obtain ⟨hV0, hVt, N_level, hNl, hlevel, U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
      hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass,
      hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3, hHlo, hHhi, hVAlo, hVAhi,
      hnA0, hnA3, hn3t, htrip, hlo, hhi, hsizeLo, hsizeHi, hsmalltrip, hshort⟩ :=
    hcover N j ell i hNoN hjo hell hlog hi henergy hnonflat
  have hη : (0 : ℝ) < (1 / 4 : ℝ) ^ j := by positivity
  have hηsmall := hscale j hjη
  have hηhalf : (1 / 4 : ℝ) ^ j ≤ 1 / 2 := hηsmall.trans hη₀half
  have hηone : (1 / 4 : ℝ) ^ j ≤ 1 := by linarith
  have htripβ :
      ((1 / 4 : ℝ) ^ j) ^ (-β') ≤ ((1 / 4 : ℝ) ^ j) ^ (-β) :=
    Real.rpow_le_rpow_of_exponent_ge hη hηone (neg_le_neg (min_le_left _ _))
  refine ⟨hV0, hVt, N_level, hNl, hlevel, U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
    hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass,
    hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3, hHlo, hHhi, hVAlo, hVAhi,
    hnA0, hnA3, hn3t, htrip, hlo, hhi, hsizeLo, hsizeHi,
    hsmalltrip.trans (mul_le_mul_of_nonneg_right htripβ ENNReal.toReal_nonneg), hshort, ?_⟩
  obtain ⟨hconst, hlogscale⟩ := hbudget _ hη hηsmall
  have hlarge := (le_max_left _ _).trans hconst
  have hαscale := (le_max_right _ _).trans hconst
  have hVpowerlo := ENNReal.toReal_mono hVt.ne henergy
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg hη.le (-γ))] at hVpowerlo
  have hlevelscale := (covering_level_log_bound_of_powers hη hηhalf hsone
    (by norm_num : (0 : ℝ) ≤ 1 / 61440) hγ.le le_rfl hVpowerlo hlevel).trans hlogscale
  have hQscale := hsupport N j ell i hNsN hjs hell hi
  have hG : ∀ a, realEmbedding (g a) ∈ matrixEntryBox 2 :=
    fun a => mobiusIdentityBall_subset_entryBox_two (dyadicRadius_pos r)
      (dyadicRadius_le_one r) (hnear a).2.1
  have hR : 0 ≤ (4 * (4 * (4 : ℝ) ^ ell) ^ 2) ^ (2 ^ i) := by positivity
  have hQ : 1 ≤ 32 * ((4 * (4 * (4 : ℝ) ^ ell) ^ 2) ^ (2 ^ i) + 1) ^ 6 := by
    have hh := one_le_pow₀ (n := 6) (show (1 : ℝ) ≤ (4 * (4 * (4 : ℝ) ^ ell) ^ 2) ^ (2 ^ i) + 1 by linarith)
    linarith only [hh]
  constructor
  · exact exists_iterate_separated_subset hr hlog g (fun a => (hnear a).1) hgr hG i
      hU1 hUo hUi (fun a ha => hUb (subset_closure ha)) hQ hα hαone x hx hmargin
      (hwindow j hjw) hlarge hlevelscale hQscale hαscale hmass
  · exact hEsc hje hlog g (fun a => (hnear a).1) hgr hG i
      hU1 hUo hUi (fun a ha => hUb (subset_closure ha)) hQ hα hαone x hx hEscapeMargin
      hlarge hlevelscale hQscale hαscale hmass


end TransposeFollowup.RationalFreePair
