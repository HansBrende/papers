import TransposeFollowup.MobiusUnipotentEnergy
import TransposeFollowup.MobiusLocalFactorization
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A quantitative near-identity estimate from three unipotent factors.
The fixed conjugation avoids a separate dilation-flow argument. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory SchwartzMap
set_option autoImplicit false

theorem complexPullbackL2_conjugate_difference (g h : Group) (f : ComplexL2) :
    ‖complexPullbackL2 (g * h * g⁻¹) f - f‖ =
      ‖complexPullbackL2 h (complexPullbackL2 g f) - complexPullbackL2 g f‖ := by
  have hi : complexPullbackL2 g⁻¹ (complexPullbackL2 g f) = f := by
    rw [← complexPullbackL2_mul, mul_inv_cancel, complexPullbackL2_one]
  rw [complexPullbackL2_mul, complexPullbackL2_mul]
  conv_lhs => arg 1; arg 2; rw [← hi]
  exact complexPullbackL2_norm_sub _ _ _

theorem schwartz_unit_entry_deriv_energy_le (g : Group) (ha : g 0 0 = 1) (hc : g 1 0 = 1)
    (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R : ℝ} (hR : schwartzDyadicRegularityCost j u ≤ R) :
    (∫ x, ‖deriv (scaledPullback g u) x‖ ^ 2) ≤ 24 * ((2 : ℝ) ^ j) ^ 2 * R := by
  have hr : 0 ≤ R := (schwartzDyadicRegularityCost_nonneg j u).trans hR
  have hp : 1 ≤ ((2 : ℝ) ^ j) ^ 2 :=
    one_le_pow₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hd := (schwartzDyadicRegularityCost_deriv_energy_le j u).trans
    (mul_le_mul_of_nonneg_left hR (sq_nonneg _))
  have hm := (schwartzDyadicRegularityCost_components_le j u).2.1.trans hR
  have hn := (schwartzDyadicRegularityCost_components_le j u).1.trans hR
  rw [schwartz_toLp_norm_sq] at hn
  have hb := schwartz_scaledPullback_deriv_energy_le g u
  simp only [ha, hc, one_pow, mul_one] at hb
  have hrp := mul_le_mul_of_nonneg_right hp hr
  nlinarith

theorem complexPullbackL2_tilted_difference (f : ComplexL2) (t : ℝ) :
    ‖complexPullbackL2 (tiltedUnipotent t) f - f‖ =
      ‖complexPullbackL2 (upperUnipotent (-t))
        (complexPullbackL2 (upperUnipotent 1 * inversionMatrix) f) -
        complexPullbackL2 (upperUnipotent 1 * inversionMatrix) f‖ := by
  rw [tiltedUnipotent, complexPullbackL2_conjugate_difference,
    complexPullbackL2_lower_difference]
  simp only [complexPullbackL2_mul]

theorem schwartz_tiltedUnipotent_regularity_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (t : ℝ) :
    ‖complexPullbackL2 (tiltedUnipotent t) (u.toLp 2 volume) - u.toLp 2 volume‖ ^ 2 ≤
      24 * t ^ 2 * ((2 : ℝ) ^ j) ^ 2 * R := by
  have he := schwartz_unit_entry_deriv_energy_le (upperUnipotent 1 * inversionMatrix)
    upperUnipotent_one_mul_inversion_entries.1 upperUnipotent_one_mul_inversion_entries.2 j u hR
  rw [complexPullbackL2_tilted_difference, complexPullbackL2_schwartz]
  have h := schwartz_transformed_upperUnipotent_energy_le (upperUnipotent 1 * inversionMatrix) u (-t)
  rw [neg_sq] at h
  exact h.trans (by convert mul_le_mul_of_nonneg_left he (sq_nonneg t) using 1; ring)

theorem schwartz_upperUnipotent_norm_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (t : ℝ) :
    ‖complexPullbackL2 (upperUnipotent t) (u.toLp 2 volume) - u.toLp 2 volume‖ ≤
      |t| * (2 : ℝ) ^ j * Real.sqrt R := by
  have hr : 0 ≤ R := (schwartzDyadicRegularityCost_nonneg j u).trans hR
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow, sq_abs, Real.sq_sqrt hr] using schwartz_upperUnipotent_regularity_le j u hR t

theorem schwartz_lowerUnipotent_norm_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (t : ℝ) :
    ‖complexPullbackL2 (lowerUnipotent t) (u.toLp 2 volume) - u.toLp 2 volume‖ ≤
      5 * |t| * (2 : ℝ) ^ j * Real.sqrt R := by
  have hr : 0 ≤ R := (schwartzDyadicRegularityCost_nonneg j u).trans hR
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp only [mul_pow, sq_abs, Real.sq_sqrt hr]
  have h := schwartz_lowerUnipotent_regularity_le j u hR t
  have hpos : 0 ≤ t ^ 2 * ((2 : ℝ) ^ j) ^ 2 * R := by positivity
  nlinarith

theorem schwartz_tiltedUnipotent_norm_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (t : ℝ) :
    ‖complexPullbackL2 (tiltedUnipotent t) (u.toLp 2 volume) - u.toLp 2 volume‖ ≤
      5 * |t| * (2 : ℝ) ^ j * Real.sqrt R := by
  have hr : 0 ≤ R := (schwartzDyadicRegularityCost_nonneg j u).trans hR
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp only [mul_pow, sq_abs, Real.sq_sqrt hr]
  have h := schwartz_tiltedUnipotent_regularity_le j u hR t
  have hpos : 0 ≤ t ^ 2 * ((2 : ℝ) ^ j) ^ 2 * R := by positivity
  nlinarith

theorem schwartz_nearIdentity_norm_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R η : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (g : Group) (hη : η ≤ 1 / 2)
    (ha : |g 0 0 - 1| ≤ η) (hb : |g 0 1| ≤ η) (hc : |g 1 0| ≤ η) :
    ‖complexPullbackL2 g (u.toLp 2 volume) - u.toLp 2 volume‖ ≤
      29 * (2 : ℝ) ^ j * Real.sqrt R * η := by
  obtain ⟨hp, hs, ht⟩ := mobius_local_factor_parameters g hη ha hb hc
  let s := (g 1 0 - (g 0 0 - 1)) / g 0 0
  let q := g 0 0 - 1
  let t := (g 0 1 + (g 0 0 - 1)) / g 0 0
  have hf : g = lowerUnipotent s * tiltedUnipotent q * upperUnipotent t :=
    mobius_three_unipotent_factorization g (ne_of_gt hp)
  have hsum := complexPullbackL2_product_difference_le
    (lowerUnipotent s * tiltedUnipotent q) (upperUnipotent t) (u.toLp 2 volume)
  have hpair := complexPullbackL2_product_difference_le
    (lowerUnipotent s) (tiltedUnipotent q) (u.toLp 2 volume)
  calc
    _ ≤ (5 * |s| * (2 : ℝ) ^ j * Real.sqrt R + 5 * |q| * (2 : ℝ) ^ j * Real.sqrt R) +
        |t| * (2 : ℝ) ^ j * Real.sqrt R := by
      rw [hf]
      linarith [schwartz_lowerUnipotent_norm_le j u hR s,
        schwartz_tiltedUnipotent_norm_le j u hR q, schwartz_upperUnipotent_norm_le j u hR t]
    _ ≤ (5 * (4 * η) * (2 : ℝ) ^ j * Real.sqrt R + 5 * η * (2 : ℝ) ^ j * Real.sqrt R) +
        (4 * η) * (2 : ℝ) ^ j * Real.sqrt R := by
      gcongr
    _ = _ := by ring

end TransposeFollowup.RealMobius


/-! Pairwise action comparison with a variable matrix-entry bound.
The variable bound also covers long words in the generators. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory SchwartzMap
set_option autoImplicit false

theorem mobius_relative_entry_identities (g h : Group) :
    (g * h⁻¹) 0 0 - 1 = (g 0 0 - h 0 0) * h 1 1 - (g 0 1 - h 0 1) * h 1 0 ∧
    (g * h⁻¹) 0 1 = -(g 0 0 - h 0 0) * h 0 1 + (g 0 1 - h 0 1) * h 0 0 ∧
    (g * h⁻¹) 1 0 = (g 1 0 - h 1 0) * h 1 1 - (g 1 1 - h 1 1) * h 1 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  change ((g : Matrix (Fin 2) (Fin 2) ℝ) * !![h 1 1, -h 0 1; -h 1 0, h 0 0]) 0 0 - 1 = _ ∧
    ((g : Matrix (Fin 2) (Fin 2) ℝ) * !![h 1 1, -h 0 1; -h 1 0, h 0 0]) 0 1 = _ ∧
    ((g : Matrix (Fin 2) (Fin 2) ℝ) * !![h 1 1, -h 0 1; -h 1 0, h 0 0]) 1 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · nlinarith [determinant h]
  constructor <;> ring

theorem abs_two_products_sub_le {x y a b η B : ℝ} (hx : |x| ≤ η) (hy : |y| ≤ η)
    (ha : |a| ≤ B) (hb : |b| ≤ B) : |x * a - y * b| ≤ 2 * B * η := by
  calc
    _ ≤ |x * a| + |y * b| := abs_sub _ _
    _ = |x| * |a| + |y| * |b| := by rw [abs_mul, abs_mul]
    _ ≤ η * B + η * B := add_le_add
      (mul_le_mul hx ha (abs_nonneg _) ((abs_nonneg _).trans hx))
      (mul_le_mul hy hb (abs_nonneg _) ((abs_nonneg _).trans hy))
    _ = _ := by ring

theorem mobius_relative_entries_le (g h : Group) {B η : ℝ}
    (hh : ∀ i k : Fin 2, |h i k| ≤ B) (he : ∀ i k : Fin 2, |g i k - h i k| ≤ η) :
    |(g * h⁻¹) 0 0 - 1| ≤ 2 * B * η ∧ |(g * h⁻¹) 0 1| ≤ 2 * B * η ∧
      |(g * h⁻¹) 1 0| ≤ 2 * B * η := by
  obtain ⟨ha, hb, hc⟩ := mobius_relative_entry_identities g h
  rw [ha, hb, hc]
  refine ⟨abs_two_products_sub_le (he 0 0) (he 0 1) (hh 1 1) (hh 1 0), ?_,
    abs_two_products_sub_le (he 1 0) (he 1 1) (hh 1 1) (hh 1 0)⟩
  convert abs_two_products_sub_le (he 0 1) (he 0 0) (hh 0 0) (hh 0 1) using 1
  congr 1
  ring

theorem complexPullbackL2_pairwise_difference (g h : Group) (f : ComplexL2) :
    ‖complexPullbackL2 g f - complexPullbackL2 h f‖ =
      ‖complexPullbackL2 (g * h⁻¹) f - f‖ := by
  calc
    _ = ‖complexPullbackL2 h⁻¹ (complexPullbackL2 g f) -
        complexPullbackL2 h⁻¹ (complexPullbackL2 h f)‖ :=
      (complexPullbackL2_norm_sub h⁻¹ _ _).symm
    _ = _ := by rw [← complexPullbackL2_mul, ← complexPullbackL2_mul,
      mul_inv_cancel, complexPullbackL2_one]

theorem schwartz_pairwise_norm_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R B η : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (g h : Group)
    (hh : ∀ i k : Fin 2, |h i k| ≤ B) (he : ∀ i k : Fin 2, |g i k - h i k| ≤ η)
    (hsmall : 2 * B * η ≤ 1 / 2) :
    ‖complexPullbackL2 g (u.toLp 2 volume) - complexPullbackL2 h (u.toLp 2 volume)‖ ≤
      58 * B * (2 : ℝ) ^ j * Real.sqrt R * η := by
  obtain ⟨ha, hb, hc⟩ := mobius_relative_entries_le g h hh he
  rw [complexPullbackL2_pairwise_difference]
  convert schwartz_nearIdentity_norm_le j u hR (g * h⁻¹) hsmall ha hb hc using 1
  ring

theorem schwartz_bounded_pairwise_norm_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R η : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (g h : Group)
    (hh : ∀ i k : Fin 2, |h i k| ≤ 2) (he : ∀ i k : Fin 2, |g i k - h i k| ≤ η)
    (hsmall : η ≤ 1 / 8) :
    ‖complexPullbackL2 g (u.toLp 2 volume) - complexPullbackL2 h (u.toLp 2 volume)‖ ≤
      116 * (2 : ℝ) ^ j * Real.sqrt R * η := by
  simpa only [show (58 : ℝ) * 2 = 116 by norm_num] using
    schwartz_pairwise_norm_le j u hR g h hh he (by linarith : 2 * 2 * η ≤ 1 / 2)

end TransposeFollowup.RealMobius


/-! Strong and joint continuity of the actual complex L2 action.
The quantitative Schwartz estimate extends by density and isometry. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Filter SchwartzMap
open scoped Topology
set_option autoImplicit false

theorem complexPullbackL2_isometry (g : Group) : Isometry (complexPullbackL2 g) := by
  apply isometry_iff_dist_eq.mpr
  intro f h
  simp only [dist_eq_norm, complexPullbackL2_norm_sub]

theorem schwartz_complexPullbackL2_continuous (u : 𝓢(ℝ, ℂ)) :
    Continuous (fun g : Group => complexPullbackL2 g (u.toLp 2 volume)) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  let B : ℝ := ‖fun i k : Fin 2 => h i k‖
  let E : Group → ℝ := fun g => ‖fun i k : Fin 2 => g i k - h i k‖
  have hh (i k : Fin 2) : |h i k| ≤ B := by
    exact (norm_le_pi_norm (h i) k).trans (norm_le_pi_norm (fun i k : Fin 2 => h i k) i)
  have he (g : Group) (i k : Fin 2) : |g i k - h i k| ≤ E g := by
    exact (norm_le_pi_norm (fun k : Fin 2 => g i k - h i k) k).trans
      (norm_le_pi_norm (fun i k : Fin 2 => g i k - h i k) i)
  have hc : Continuous E := by dsimp [E]; fun_prop
  have hlim : Tendsto E (𝓝 h) (𝓝 0) := by simpa [E] using hc.tendsto h
  have hscale : Tendsto (fun g => 2 * B * E g) (𝓝 h) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hlim :
      Tendsto (fun g => 2 * B * E g) (𝓝 h) (𝓝 (2 * B * 0)))
  have hsmall : ∀ᶠ g in 𝓝 h, 2 * B * E g ≤ 1 / 2 :=
    (hscale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ hx => hx.le)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun g => norm_nonneg _))
    (g := fun g => 58 * B * (2 : ℝ) ^ 0 * Real.sqrt (schwartzDyadicRegularityCost 0 u) * E g)
  · filter_upwards [hsmall] with g hg
    exact schwartz_pairwise_norm_le 0 u le_rfl g h hh (he g) hg
  · simpa using (tendsto_const_nhds.mul hlim :
      Tendsto (fun g => 58 * B * (2 : ℝ) ^ 0 * Real.sqrt (schwartzDyadicRegularityCost 0 u) * E g)
        (𝓝 h) (𝓝 (58 * B * (2 : ℝ) ^ 0 * Real.sqrt (schwartzDyadicRegularityCost 0 u) * 0)))

theorem complexPullbackL2_joint_continuous :
    Continuous (fun p : ComplexL2 × Group => complexPullbackL2 p.2 p.1) := by
  refine continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume) (by norm_num)) ?_ ?_
  · intro f hf
    obtain ⟨u, rfl⟩ := hf
    exact schwartz_complexPullbackL2_continuous u
  · intro g
    exact (complexPullbackL2_isometry g).lipschitzWith

theorem complexPullbackL2_continuous (f : ComplexL2) :
    Continuous (fun g : Group => complexPullbackL2 g f) := by
  have hp : Continuous (fun g : Group => (f, g)) := continuous_const.prodMk continuous_id
  exact Continuous.comp (g := fun p : ComplexL2 × Group => complexPullbackL2 p.2 p.1)
    (f := fun g : Group => (f, g)) complexPullbackL2_joint_continuous hp

end TransposeFollowup.RealMobius


/-! Actual Bochner averages in the representation convention T_g=W_(g^-1).
Finite measures give integrable orbits, and probability averages contract. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory SchwartzMap Set
set_option autoImplicit false

instance instGroupSecondCountableTopology : SecondCountableTopology Group := by
  have : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)).isEmbedding.secondCountableTopology

theorem complexPullbackL2_inverse_continuous (f : ComplexL2) :
    Continuous (fun g : Group => complexPullbackL2 g⁻¹ f) :=
  Continuous.comp (g := fun g : Group => complexPullbackL2 g f)
    (f := fun g : Group => g⁻¹) (complexPullbackL2_continuous f) continuous_inv

theorem complexPullbackL2_inverse_difference (g : Group) (f : ComplexL2) :
    ‖complexPullbackL2 g⁻¹ f - f‖ = ‖complexPullbackL2 g f - f‖ := by
  calc
    _ = ‖complexPullbackL2 g (complexPullbackL2 g⁻¹ f) - complexPullbackL2 g f‖ :=
      (complexPullbackL2_norm_sub g _ _).symm
    _ = _ := by
      rw [← complexPullbackL2_mul, inv_mul_cancel, complexPullbackL2_one, norm_sub_rev]

variable [MeasurableSpace Group] [BorelSpace Group]

noncomputable def groupActionAverage (μ : Measure Group) (f : ComplexL2) : ComplexL2 :=
  ∫ g, complexPullbackL2 g⁻¹ f ∂μ

theorem integrable_complexPullbackL2_inverse (μ : Measure Group) [IsFiniteMeasure μ] (f : ComplexL2) :
    Integrable (fun g : Group => complexPullbackL2 g⁻¹ f) μ := by
  apply (integrable_const ‖f‖ : Integrable (fun _ : Group => ‖f‖) μ).mono'
    (complexPullbackL2_inverse_continuous f).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun g => (complexPullbackL2_norm g⁻¹ f).le)

omit [BorelSpace Group] in
theorem groupActionAverage_norm_le_measure (μ : Measure Group) [IsFiniteMeasure μ] (f : ComplexL2) :
    ‖groupActionAverage μ f‖ ≤ μ.real univ * ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun g : Group => (complexPullbackL2_norm g⁻¹ f).le))
  simpa only [groupActionAverage, mul_comm] using h

omit [BorelSpace Group] in
theorem groupActionAverage_norm_le (μ : Measure Group) [IsProbabilityMeasure μ] (f : ComplexL2) :
    ‖groupActionAverage μ f‖ ≤ ‖f‖ := by
  simpa using groupActionAverage_norm_le_measure μ f

theorem groupActionAverage_sub (μ : Measure Group) [IsFiniteMeasure μ] (f h : ComplexL2) :
    groupActionAverage μ (f - h) = groupActionAverage μ f - groupActionAverage μ h := by
  simp only [groupActionAverage, map_sub]
  exact integral_sub (integrable_complexPullbackL2_inverse μ f) (integrable_complexPullbackL2_inverse μ h)

theorem groupActionAverage_norm_sub_le (μ : Measure Group) [IsProbabilityMeasure μ] (f h : ComplexL2) :
    ‖groupActionAverage μ f - groupActionAverage μ h‖ ≤ ‖f - h‖ := by
  rw [← groupActionAverage_sub]
  exact groupActionAverage_norm_le μ (f - h)

theorem groupActionAverage_difference_le (μ : Measure Group) [IsProbabilityMeasure μ]
    (f : ComplexL2) {C : ℝ} (hC : ∀ᵐ g ∂μ, ‖complexPullbackL2 g⁻¹ f - f‖ ≤ C) :
    ‖groupActionAverage μ f - f‖ ≤ C := by
  have hi : (∫ g, complexPullbackL2 g⁻¹ f - f ∂μ) = groupActionAverage μ f - f := by
    rw [integral_sub (integrable_complexPullbackL2_inverse μ f) (integrable_const f)]
    simp only [groupActionAverage, integral_const, probReal_univ, one_smul]
  have h := norm_integral_le_of_norm_le_const hC
  simpa only [hi, probReal_univ, mul_one] using h

theorem groupActionAverage_nearIdentity_le (μ : Measure Group) [IsProbabilityMeasure μ]
    (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R η : ℝ} (hR : schwartzDyadicRegularityCost j u ≤ R)
    (hη : η ≤ 1 / 2)
    (hs : ∀ᵐ g ∂μ, |g 0 0 - 1| ≤ η ∧ |g 0 1| ≤ η ∧ |g 1 0| ≤ η) :
    ‖groupActionAverage μ (u.toLp 2 volume) - u.toLp 2 volume‖ ≤
      29 * (2 : ℝ) ^ j * Real.sqrt R * η := by
  apply groupActionAverage_difference_le
  filter_upwards [hs] with g hg
  rw [complexPullbackL2_inverse_difference]
  exact schwartz_nearIdentity_norm_le j u hR g hη hg.1 hg.2.1 hg.2.2

end TransposeFollowup.RealMobius


/-! Right-convolution smoothing for the actual representation average.
The error depends only on the smoothing kernel and the original input,
not on the size of the support of the measure being smoothed. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory SchwartzMap
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem groupActionAverage_mconv (μ ν : Measure Group) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : ComplexL2) :
    groupActionAverage (μ ∗ₘ ν) f = groupActionAverage μ (groupActionAverage ν f) := by
  unfold groupActionAverage
  rw [integral_mconv (integrable_complexPullbackL2_inverse (μ ∗ₘ ν) f)]
  simp only [mul_inv_rev, complexPullbackL2_mul]
  apply integral_congr_ae
  filter_upwards [] with g
  exact (complexPullbackL2 g⁻¹).integral_comp_comm (integrable_complexPullbackL2_inverse ν f)

theorem groupActionAverage_smoothing_difference_le (μ ν : Measure Group)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : ComplexL2) :
    ‖groupActionAverage (μ ∗ₘ ν) f - groupActionAverage μ f‖ ≤
      ‖groupActionAverage ν f - f‖ := by
  rw [groupActionAverage_mconv]
  exact groupActionAverage_norm_sub_le μ _ _

theorem groupActionAverage_smoothing_nearIdentity_le (μ ν : Measure Group)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R η : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (hη : η ≤ 1 / 2)
    (hs : ∀ᵐ g ∂ν, |g 0 0 - 1| ≤ η ∧ |g 0 1| ≤ η ∧ |g 1 0| ≤ η) :
    ‖groupActionAverage (μ ∗ₘ ν) (u.toLp 2 volume) - groupActionAverage μ (u.toLp 2 volume)‖ ≤
      29 * (2 : ℝ) ^ j * Real.sqrt R * η :=
  (groupActionAverage_smoothing_difference_le μ ν _).trans
    (groupActionAverage_nearIdentity_le ν j u hR hη hs)

theorem groupActionAverage_smoothing_norm_lower (μ ν : Measure Group)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R η m : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (hη : η ≤ 1 / 2)
    (hs : ∀ᵐ g ∂ν, |g 0 0 - 1| ≤ η ∧ |g 0 1| ≤ η ∧ |g 1 0| ≤ η)
    (hm : m ≤ ‖groupActionAverage μ (u.toLp 2 volume)‖)
    (he : 29 * (2 : ℝ) ^ j * Real.sqrt R * η ≤ m / 2) :
    m / 2 ≤ ‖groupActionAverage (μ ∗ₘ ν) (u.toLp 2 volume)‖ := by
  have hb := groupActionAverage_smoothing_nearIdentity_le μ ν j u hR hη hs
  have ht := norm_add_le
    (groupActionAverage μ (u.toLp 2 volume) - groupActionAverage (μ ∗ₘ ν) (u.toLp 2 volume))
    (groupActionAverage (μ ∗ₘ ν) (u.toLp 2 volume))
  rw [sub_add_cancel, norm_sub_rev] at ht
  linarith

end TransposeFollowup.RealMobius
