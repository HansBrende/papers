import MergeDepth.StraddleLocal

/-!
# Partial results on Conjecture S: the density of `W` (Proposition 7.12(b))

Route: the law of `W` is identified through characteristic functions, and the identity through
Poisson summation. `ζ i` for `i : Fin (κ - 1)` stands for `ζ_{i+1}`; `n_i = binN k i` is `4` for
levels below `k` and `2` from `k` on.

* `bspline w` `= (4/w⁴)(Δ_w ⋆ Δ_w)`, the density of `Z = w(ω₁ + ⋯ + ω₄)`; `fourier_bspline`:
  `𝓕 f_Z(ξ) = sinc⁴(πξw/2)` (from `fourier_tent` and Mathlib's `Real.fourier_mul_convolution_eq`).
* `densityW` `= f_W`, the finite mixture `∑_j ∏_i C(n_i, j_i) 2^{-n_i} f_Z(y - ∑_i (j_i - n_i/2)Π̂_i)`;
  `continuous_densityW`, `densityW_nonneg`, `hasCompactSupport_densityW`.
* `fourier_densityW`: `𝓕 f_W(ξ) = Ψ(ξ) = ∏_i cos^{n_i}(πξΠ̂_i) sinc⁴(πξΠ̂_κ/2)`;
  `psiW_eq_phiGen`: `Ψ(r/N) = φ(r)`.
* `charFun_binomial_half`, `charFun_uniform_quarter`, `charFun_lawW`: by independence
  (`iIndepFun.charFun_map_fun_sum_eq_prod`), `E e^{itW} = Ψ(t/(2π))`;
  `charFun_withDensity_densityW`: the same for `f_W(y) dy`; `charFun_lawW_eq_straddlePhi`:
  `E e^{2πirW/N} = φ_k(r)`.
* `tsum_densityW_eq`: `N ∑_{l ∈ ℤ} f_W(lN) = 1 + V_k` (Mathlib's
  `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable` and Proposition 7.12(a)).
* `density_W`: **Proposition 7.12(b)**: the law of `W` is `f_W(y) dy` (`Measure.ext_of_charFun`),
  `f_W` is continuous and nonnegative, and `1 + V_k = N ∑_l f_W(lN)`.
* `exact_form_V`: Proposition 7.12(a) and (c), restated.
* `density_W_model_exists`: the hypotheses of `density_W` are satisfiable (product space).
* `densityW_poisson_scale`, `tsum_densityW_int`, `sideband_eq_densityW`: the remark after
  Proposition 7.12, `∑_l f_W(l) = ∑_w φ_k(Nw)` and `SB_k = N ∑_l f_W(lN) - ∑_l f_W(l)`.
-/

namespace MergeDepth

open Finset Real MeasureTheory
open scoped Convolution FourierTransform

/-! ### The tent and the cubic B-spline on the line -/

theorem tent_eq_zero_of_not_mem {w y : ℝ} (hy : y ∉ Set.Icc (-(|w| / 2)) (|w| / 2)) :
    tent w y = 0 := by
  apply tent_eq_zero
  simp only [Set.mem_Icc, not_and_or, not_le] at hy
  have hw : w ≤ |w| := le_abs_self w
  rcases hy with h | h
  · rw [abs_of_neg (by linarith [abs_nonneg w])]; linarith
  · rw [abs_of_pos (by linarith [abs_nonneg w])]; linarith

theorem hasCompactSupport_tent (w : ℝ) : HasCompactSupport (tent w) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(|w| / 2)) (b := |w| / 2))
    fun _ hy => tent_eq_zero_of_not_mem hy

theorem integrable_tent (w : ℝ) : Integrable (tent w) :=
  (continuous_tent w).integrable_of_hasCompactSupport (hasCompactSupport_tent w)

open Complex in
/-- The Fourier transform of the tent on the line:
`𝓕Δ_w(ξ) = ∫ e^{-2πiξy} Δ_w(y) dy = (w²/2) sinc²(πξw/2)`. -/
theorem fourier_tent {w : ℝ} (hw : 0 ≤ w) (ξ : ℝ) :
    𝓕 (fun y : ℝ => (tent w y : ℂ)) ξ =
      ((w ^ 2 / 2 * Real.sinc (π * ξ * w / 2) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hsupp : ∀ v ∉ Set.Ioc (-(w / 2)) (w / 2),
      Complex.exp (↑(-2 * π * v * ξ) * I) • (tent w v : ℂ) = 0 := by
    intro v hv
    have : tent w v = 0 := by
      apply tent_eq_zero
      simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
      rcases hv with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [this]; simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h := integral_exp_tent (N := w) hw le_rfl (2 * π * ξ)
  rw [show 2 * π * ξ * w / 4 = π * ξ * w / 2 by ring] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun v _ => ?_
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- The density of `Z = w(ω₁ + ⋯ + ω₄)` with `ω_j` uniform on `[-1/4, 1/4]`: the cubic B-spline
`(4/w⁴) (Δ_w ⋆ Δ_w)` (`Δ_w ⋆ Δ_w/2` is the density of `w(ω₁ + ω₂)` times `w²/4`, …). -/
noncomputable def bspline (w : ℝ) (z : ℝ) : ℝ :=
  4 / w ^ 4 * (tent w ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] tent w) z

theorem continuous_bspline (w : ℝ) : Continuous (bspline w) :=
  continuous_const.mul ((hasCompactSupport_tent w).continuous_convolution_left _
    (continuous_tent w) (integrable_tent w).locallyIntegrable)

theorem hasCompactSupport_bspline (w : ℝ) : HasCompactSupport (bspline w) := by
  have h := (hasCompactSupport_tent w).convolution (ContinuousLinearMap.mul ℝ ℝ)
    (hasCompactSupport_tent w) (μ := volume)
  exact h.mul_left (f := fun _ => 4 / w ^ 4)

theorem bspline_nonneg {w : ℝ} (z : ℝ) : 0 ≤ bspline w z := by
  unfold bspline
  apply mul_nonneg (by positivity)
  rw [convolution_def]
  exact integral_nonneg fun t => by
    simp only [ContinuousLinearMap.mul_apply']
    exact mul_nonneg (tent_nonneg _ _) (tent_nonneg _ _)

theorem integrable_bspline (w : ℝ) : Integrable (bspline w) :=
  (continuous_bspline w).integrable_of_hasCompactSupport (hasCompactSupport_bspline w)

open Complex in
/-- `𝓕 f_Z(ξ) = sinc⁴(πξw/2)`, via the convolution theorem. -/
theorem fourier_bspline {w : ℝ} (hw : 0 < w) (ξ : ℝ) :
    𝓕 (fun z : ℝ => (bspline w z : ℂ)) ξ = ((Real.sinc (π * ξ * w / 2) ^ 4 : ℝ) : ℂ) := by
  set T : ℝ → ℂ := fun y => (tent w y : ℂ) with hT
  have hTi : Integrable T := (integrable_tent w).ofReal
  have hconv : (fun z : ℝ => (bspline w z : ℂ)) =
      fun z => (4 / w ^ 4 : ℂ) * (T ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] T) z := by
    ext z
    unfold bspline
    rw [convolution_def, convolution_def]
    simp only [ContinuousLinearMap.mul_apply', hT]
    push_cast
    congr 1
    rw [← integral_complex_ofReal]
    congr 1; ext t; push_cast; ring
  rw [hconv]
  have hlin : 𝓕 (fun z => (4 / w ^ 4 : ℂ) * (T ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] T) z) ξ =
      (4 / w ^ 4 : ℂ) * 𝓕 (T ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] T) ξ := by
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
      ← integral_const_mul]
    congr 1; ext v
    simp only [smul_eq_mul]; ring
  rw [hlin, Real.fourier_mul_convolution_eq hTi hTi, fourier_tent hw.le]
  have hw' : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  push_cast
  field_simp
  ring

/-! ### The density `f_W` and its Fourier transform -/

open Complex in
/-- `∑_{j=0}^{n} C(n,j) 2^{-n} e^{-iθ(j - n/2)} = cos^n(θ/2)` (the binomial law, centred). -/
theorem sum_choose_exp (n : ℕ) (θ : ℝ) :
    ∑ j ∈ range (n + 1), ((n.choose j : ℝ) / 2 ^ n : ℂ) *
        Complex.exp (-(((θ * ((j : ℝ) - n / 2)) : ℝ) : ℂ) * I) =
      ((Real.cos (θ / 2) ^ n : ℝ) : ℂ) := by
  have hcos : ((Real.cos (θ / 2) : ℝ) : ℂ) * 2 =
      Complex.exp (-(((θ / 2 : ℝ)) : ℂ) * I) + Complex.exp ((((θ / 2 : ℝ)) : ℂ) * I) := by
    rw [Complex.ofReal_cos, mul_comm, Complex.two_cos]; ring_nf
  have h2 : (((Real.cos (θ / 2) ^ n : ℝ)) : ℂ) =
      (Complex.exp (-((θ / 2 : ℝ) : ℂ) * I) + Complex.exp (((θ / 2 : ℝ) : ℂ) * I)) ^ n / 2 ^ n := by
    rw [← hcos]; push_cast; field_simp; ring
  rw [h2, add_pow, Finset.sum_div]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have hexp : (j : ℂ) * (-((θ / 2 : ℝ) : ℂ) * I) + ((n - j : ℕ) : ℂ) * (((θ / 2 : ℝ) : ℂ) * I) =
      -(((θ * ((j : ℝ) - n / 2)) : ℝ) : ℂ) * I := by
    rw [Nat.cast_sub hj']; push_cast; ring
  rw [hexp]
  push_cast
  ring

/-- `n_i ∈ {4, 2}`: `ζ + n_i/2 ~ Bin(n_i, 1/2)` at level `i + 1` (`4` below `k`, `2` from `k` on). -/
def binN (k i : ℕ) : ℕ := if i + 1 < k then 4 else 2

/-- The outcomes `j : Fin (κ - 1) → ℕ`, `j i ≤ n_i`, of the binomial variables. -/
def outcomes (k κ : ℕ) : Finset (Fin (κ - 1) → ℕ) :=
  Fintype.piFinset fun i => range (binN k i + 1)

/-- The probability `∏_i C(n_i, j_i) 2^{-n_i}` of an outcome. -/
noncomputable def outWeight (k κ : ℕ) (j : Fin (κ - 1) → ℕ) : ℝ :=
  ∏ i : Fin (κ - 1), ((binN k i).choose (j i) : ℝ) / 2 ^ binN k i

/-- The value `∑_i (j_i - n_i/2) Π̂_{i+1}` of `∑_{i<κ} ζ_i Π̂_i` at an outcome. -/
noncomputable def outPoint (m k κ : ℕ) (j : Fin (κ - 1) → ℕ) : ℝ :=
  ∑ i : Fin (κ - 1), ((j i : ℝ) - binN k i / 2) * piHat m (i + 1)

/-- **The density `f_W`** of `W = ∑_{i<κ} ζ_i Π̂_i + Z`: a finite mixture of translates of `f_Z`. -/
noncomputable def densityW (m k κ : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ outcomes k κ, outWeight k κ j * bspline (piHat m κ) (y - outPoint m k κ j)

/-- `Ψ(ξ) = ∏_{i<κ} cos^{n_i}(πξΠ̂_i) sinc⁴(πξΠ̂_κ/2)`, so that `Ψ(r/N) = φ_k(r)`. -/
noncomputable def psiW (m k κ : ℕ) (ξ : ℝ) : ℝ :=
  (∏ i : Fin (κ - 1), Real.cos (π * ξ * piHat m (i + 1)) ^ binN k i) *
    Real.sinc (π * ξ * piHat m κ / 2) ^ 4

theorem continuous_densityW (m k κ : ℕ) : Continuous (densityW m k κ) := by
  unfold densityW
  exact continuous_finsetSum _ fun j _ => continuous_const.mul
    ((continuous_bspline _).comp (continuous_id.sub continuous_const))

theorem densityW_nonneg (m k κ : ℕ) (y : ℝ) : 0 ≤ densityW m k κ y := by
  unfold densityW outWeight
  exact sum_nonneg fun j _ => mul_nonneg (prod_nonneg fun i _ => by positivity) (bspline_nonneg _)

theorem hasCompactSupport_densityW (m k κ : ℕ) : HasCompactSupport (densityW m k κ) := by
  unfold densityW
  have : ∀ j ∈ outcomes k κ, HasCompactSupport
      (fun y => outWeight k κ j * bspline (piHat m κ) (y - outPoint m k κ j)) := by
    intro j _
    exact ((hasCompactSupport_bspline (piHat m κ)).comp_homeomorph
      (Homeomorph.subRight (outPoint m k κ j))).mul_left (f := fun _ => outWeight k κ j)
  have h := HasCompactSupport.finset_sum this
  convert h using 1
  ext y
  simp only [Finset.sum_apply]

theorem integrable_densityW (m k κ : ℕ) : Integrable (densityW m k κ) :=
  (continuous_densityW m k κ).integrable_of_hasCompactSupport (hasCompactSupport_densityW m k κ)

open Complex in
/-- Translation: `𝓕(g(· - x))(ξ) = e^{-2πixξ} 𝓕g(ξ)`. -/
theorem fourier_comp_sub_const (g : ℝ → ℂ) (x ξ : ℝ) :
    𝓕 (fun y => g (y - x)) ξ = Complex.exp (↑(-2 * π * x * ξ) * I) * 𝓕 g ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  set F : ℝ → ℂ := fun u => Complex.exp (↑(-2 * π * x * ξ) * I) *
    (Complex.exp (↑(-2 * π * u * ξ) * I) • g u) with hF
  have e : (fun v => Complex.exp (↑(-2 * π * v * ξ) * I) • g (v - x)) = fun v => F (v - x) := by
    ext v
    simp only [hF, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [e, integral_sub_right_eq_self F x]

open Complex in
/-- **The Fourier transform of `f_W`**: `𝓕 f_W(ξ) = Ψ(ξ)`. -/
theorem fourier_densityW (m k κ : ℕ) (ξ : ℝ) :
    𝓕 (fun y => (densityW m k κ y : ℂ)) ξ = (psiW m k κ ξ : ℂ) := by
  set w := piHat m κ with hwdef
  have hw : 0 < w := piHat_pos
  have hint : ∀ j ∈ outcomes k κ, Integrable (fun v : ℝ =>
      Complex.exp (↑(-2 * π * v * ξ) * I) • ((outWeight k κ j : ℂ) *
        (bspline w (v - outPoint m k κ j) : ℂ))) := by
    intro j _
    have h1 : Integrable (fun v : ℝ => (outWeight k κ j : ℂ) * (bspline w (v - outPoint m k κ j) : ℂ)) :=
      (((integrable_bspline w).comp_sub_right (outPoint m k κ j)).ofReal).const_mul _
    have h2 := (Real.fourierIntegral_convergent_iff ξ).2 h1
    simpa [Circle.smul_def, Real.fourierChar_apply, mul_comm, mul_left_comm, mul_assoc] using h2
  have hlin : 𝓕 (fun y => (densityW m k κ y : ℂ)) ξ =
      ∑ j ∈ outcomes k κ, (outWeight k κ j : ℂ) *
        𝓕 (fun y => (bspline w (y - outPoint m k κ j) : ℂ)) ξ := by
    simp_rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    rw [← integral_finsetSum _ (fun j hj => ?_)]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [densityW, ← hwdef]
      push_cast
      rw [Finset.smul_sum]
      refine sum_congr rfl fun j _ => ?_
      simp only [smul_eq_mul]
      ring
    · have := hint j hj
      refine this.congr (Filter.Eventually.of_forall fun v => ?_)
      simp only [smul_eq_mul]
      ring
  rw [hlin]
  simp_rw [fourier_comp_sub_const (fun y => (bspline w y : ℂ)), fourier_bspline hw]
  have hprod : ∑ j ∈ outcomes k κ, (outWeight k κ j : ℂ) *
        Complex.exp (↑(-2 * π * outPoint m k κ j * ξ) * I) =
      ∏ i : Fin (κ - 1), ∑ ji ∈ range (binN k i + 1),
        (((binN k i).choose ji : ℝ) / 2 ^ binN k i : ℂ) *
          Complex.exp (-(((2 * π * piHat m (i + 1) * ξ) * ((ji : ℝ) - binN k i / 2) : ℝ) : ℂ) * I) := by
    rw [Finset.prod_univ_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    unfold outWeight outPoint
    push_cast
    congr 2
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun i _ => ?_
    ring
  have hsum : ∑ j ∈ outcomes k κ, (outWeight k κ j : ℂ) *
        (Complex.exp (↑(-2 * π * outPoint m k κ j * ξ) * I) *
          ((Real.sinc (π * ξ * w / 2) ^ 4 : ℝ) : ℂ)) =
      (∑ j ∈ outcomes k κ, (outWeight k κ j : ℂ) *
        Complex.exp (↑(-2 * π * outPoint m k κ j * ξ) * I)) *
          ((Real.sinc (π * ξ * w / 2) ^ 4 : ℝ) : ℂ) := by
    rw [Finset.sum_mul]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hsum, hprod]
  simp_rw [sum_choose_exp]
  unfold psiW
  push_cast
  congr 1
  refine prod_congr rfl fun i _ => ?_
  congr 2
  ring

/-- `∏_{i : Fin n} g(i + 1) = ∏_{i=1}^{n} g(i)`. -/
theorem prod_fin_succ_eq_prod_Icc {M : Type*} [CommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∏ i : Fin n, g (i + 1) = ∏ i ∈ Icc 1 n, g i := by
  rw [Fin.prod_univ_eq_prod_range (fun i => g (i + 1)) n]
  refine Finset.prod_nbij' (fun i => i + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_range] at hi; simp only [mem_Icc]; omega
  · intro i hi; simp only [mem_Icc] at hi; simp only [mem_range]; omega
  · intro i _; simp
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro i _; rfl

/-- `Ψ(r/N) = φ(r)` (the general form `phiGen` of `φ_k`) for `k ≤ κ`. -/
theorem psiW_eq_phiGen {m k κ : ℕ} (hkκ : k ≤ κ) (r : ℤ) :
    psiW m k κ (r / ((m : ℝ) + 1)) = phiGen m k κ r := by
  unfold psiW phiGen
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hsinc : π * (r / ((m : ℝ) + 1)) * piHat m κ / 2 = π * r * piHat m κ / (2 * ((m : ℝ) + 1)) := by
    field_simp
  rw [hsinc]
  have hcos : ∀ i : ℕ, Real.cos (π * (r / ((m : ℝ) + 1)) * piHat m i) =
      Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) := fun i => by congr 1; field_simp
  have hsplit : ∀ i ∈ Icc 1 (κ - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ binN k (i - 1) =
      Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2 *
        (if i < k then Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2 else 1) := by
    intro i hi
    have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
    unfold binN
    split_ifs with h1 h2 h2
    · ring
    · exfalso; omega
    · exfalso; omega
    · ring
  have hprod : ∏ i : Fin (κ - 1), Real.cos (π * (r / ((m : ℝ) + 1)) * piHat m (i + 1)) ^ binN k i =
      ∏ i ∈ Icc 1 (κ - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ binN k (i - 1) := by
    rw [← prod_fin_succ_eq_prod_Icc (κ - 1)
      (fun i => Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ binN k (i - 1))]
    refine prod_congr rfl fun i _ => ?_
    rw [hcos]
    simp
  rw [hprod, prod_congr rfl hsplit, prod_mul_distrib, ← prod_filter]
  have hfilter : (Icc 1 (κ - 1)).filter (fun i => i < k) = Icc 1 (k - 1) := by
    ext i; simp only [mem_filter, mem_Icc]; omega
  rw [hfilter]
  ring

/-! ### Characteristic functions of the ingredients -/

open scoped ENNReal ProbabilityTheory

/-- `1/2` as a point of the unit interval. -/
noncomputable def halfI : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

open Complex ProbabilityTheory in
/-- `E e^{itB} = e^{int/2} cos^n(t/2)` for `B ~ Bin(n, 1/2)`. -/
theorem charFun_binomial_half (n : ℕ) (t : ℝ) :
    charFun (Bin(ℝ, n, halfI)) t =
      Complex.exp (((n * t / 2 : ℝ) : ℂ) * I) * ((Real.cos (t / 2) ^ n : ℝ) : ℂ) := by
  rw [map_cast_binomial_eq_sum_dirac, charFun_apply_real, integral_finsetSum_measure]
  · simp_rw [integral_smul_measure, integral_dirac]
    have h := sum_choose_exp n (-t)
    rw [show -t / 2 = -(t / 2) by ring, Real.cos_neg] at h
    rw [← h, Finset.mul_sum]
    have hI : Finset.Iic n = range (n + 1) := by ext j; simp
    rw [hI]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hw : ((n.choose j : ℝ) * ((halfI : ℝ)) ^ j * (1 - (halfI : ℝ)) ^ (n - j)) =
        (n.choose j : ℝ) / 2 ^ n := by
      simp only [halfI]
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, mul_assoc, ← pow_add,
        Nat.add_sub_cancel' hj', one_div_pow, mul_one_div]
    have hexp : Complex.exp ((t : ℂ) * (((j : ℕ) : ℝ) : ℂ) * I) =
        Complex.exp (((n * t / 2 : ℝ) : ℂ) * I) *
          Complex.exp (-(((-t * ((j : ℝ) - n / 2)) : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hw, ENNReal.toReal_ofReal (by positivity), Complex.real_smul, hexp]
    push_cast
    ring
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

open Complex in
/-- `E e^{itω} = sinc(t/4)` for `ω` uniform on `[-1/4, 1/4]`. -/
theorem charFun_uniform_quarter (t : ℝ) :
    charFun (ProbabilityTheory.cond volume (Set.Icc (-1 / 4 : ℝ) (1 / 4))) t =
      ((Real.sinc (t / 4) : ℝ) : ℂ) := by
  unfold ProbabilityTheory.cond
  rw [Real.volume_Icc, charFun_apply_real, integral_smul_measure,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have h2 : (ENNReal.ofReal (1 / 4 - -1 / 4))⁻¹.toReal = 2 := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by norm_num)]; norm_num
  rw [h2, Complex.real_smul]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
    norm_num
  · have htI : ((t : ℂ) * I) ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) I_ne_zero
    have e : (fun x : ℝ => Complex.exp (t * x * I)) = fun x : ℝ => Complex.exp ((t * I) * x) := by
      ext x; ring_nf
    rw [e, integral_exp_mul_complex htI]
    have hsin : Complex.exp ((t : ℂ) * I * ((1 / 4 : ℝ) : ℂ)) - Complex.exp ((t : ℂ) * I * ((-1 / 4 : ℝ) : ℂ)) =
        2 * (Real.sin (t / 4) : ℂ) * I := by
      have e1 : (t : ℂ) * I * ((1 / 4 : ℝ) : ℂ) = ((t / 4 : ℝ) : ℂ) * I := by push_cast; ring
      have e2 : (t : ℂ) * I * ((-1 / 4 : ℝ) : ℂ) = (-((t / 4 : ℝ) : ℂ)) * I := by push_cast; ring
      rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_sin]
      ring
    rw [hsin, Real.sinc_of_ne_zero (by positivity)]
    push_cast
    field_simp
    ring

theorem psiW_neg (m k κ : ℕ) (ξ : ℝ) : psiW m k κ (-ξ) = psiW m k κ ξ := by
  unfold psiW
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    rw [show π * -ξ * piHat m (i + 1) = -(π * ξ * piHat m (i + 1)) by ring, Real.cos_neg]
  · rw [show π * -ξ * piHat m κ / 2 = -(π * ξ * piHat m κ / 2) by ring, Real.sinc_neg]

open Complex in
/-- The characteristic function of `f_W(y) dy` is `t ↦ Ψ(t/(2π))`. -/
theorem charFun_withDensity_densityW (m k κ : ℕ) (t : ℝ) :
    charFun (volume.withDensity fun y => ENNReal.ofReal (densityW m k κ y)) t =
      (psiW m k κ (t / (2 * π)) : ℂ) := by
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul
    (continuous_densityW m k κ).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (densityW_nonneg m k κ _)]
  rw [← psiW_neg, ← fourier_densityW, Real.fourier_real_eq_integral_exp_smul]
  congr 1; ext x
  rw [Complex.real_smul, smul_eq_mul, mul_comm]
  congr 2
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  push_cast
  field_simp

open Complex ProbabilityTheory in
/-- The characteristic function of the law of `W` is `t ↦ Ψ(t/(2π))`. -/
theorem charFun_lawW {m k κ : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (ζ : Fin (κ - 1) → Ω → ℝ) (ω : Fin 4 → Ω → ℝ)
    (hind : iIndepFun (Sum.elim ζ ω) P)
    (hζ : ∀ i, HasLaw (fun x => ζ i x + (binN k i : ℝ) / 2) Bin(ℝ, binN k i, halfI) P)
    (hω : ∀ j, pdf.IsUniform (ω j) (Set.Icc (-1 / 4 : ℝ) (1 / 4)) P) (t : ℝ) :
    charFun (P.map (fun x => ∑ i, ζ i x * piHat m (i + 1) + piHat m κ * ∑ j, ω j x)) t =
      (psiW m k κ (t / (2 * π)) : ℂ) := by
  set c : Fin (κ - 1) ⊕ Fin 4 → ℝ := Sum.elim (fun i => piHat m (i + 1)) (fun _ => piHat m κ)
    with hc
  set X : Fin (κ - 1) ⊕ Fin 4 → Ω → ℝ := fun s x => c s * Sum.elim ζ ω s x with hX
  have hmeasζ : ∀ i, AEMeasurable (ζ i) P := fun i => by
    have h1 := (hζ i).aemeasurable.sub_const ((binN k i : ℝ) / 2)
    have h2 : (fun x => ζ i x + (binN k i : ℝ) / 2 - (binN k i : ℝ) / 2) = ζ i := by ext; ring
    rwa [h2] at h1
  have hmeasω : ∀ j, AEMeasurable (ω j) P := fun j => (hω j).aemeasurable
  have hmeas : ∀ s, AEMeasurable (Sum.elim ζ ω s) P := by
    intro s
    cases s with
    | inl i => exact hmeasζ i
    | inr j => exact hmeasω j
  have hXmeas : ∀ s, AEMeasurable (X s) P := fun s => (hmeas s).const_mul (c s)
  have hXind : iIndepFun X P :=
    hind.comp (fun s y => c s * y) (fun s => measurable_const.mul measurable_id)
  have hW : (fun x => ∑ i, ζ i x * piHat m (i + 1) + piHat m κ * ∑ j, ω j x) =
      fun x => ∑ s, X s x := by
    ext x
    rw [Fintype.sum_sum_type]
    simp only [hX, hc, Sum.elim_inl, Sum.elim_inr, Finset.mul_sum]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hW, hXind.charFun_map_fun_sum_eq_prod hXmeas, Finset.prod_apply]
  simp_rw [hX, charFun_map_mul_comp (hmeas _)]
  rw [Fintype.prod_sum_type]
  simp only [hc, Sum.elim_inl, Sum.elim_inr]
  -- the binomial factors
  have hbin : ∀ i : Fin (κ - 1), charFun (P.map (ζ i)) (piHat m (i + 1) * t) =
      ((Real.cos (π * (t / (2 * π)) * piHat m (i + 1)) ^ binN k i : ℝ) : ℂ) := by
    intro i
    have hmap : P.map (ζ i) =
        (Bin(ℝ, binN k i, halfI)).map (fun y => y + (-((binN k i : ℝ) / 2))) := by
      rw [← (hζ i).map_eq, AEMeasurable.map_map_of_aemeasurable
        (measurable_add_const _).aemeasurable (hζ i).aemeasurable]
      congr 1; ext x; simp
    rw [hmap, charFun_map_add_const, charFun_binomial_half, mul_comm, ← mul_assoc,
      ← Complex.exp_add]
    simp only [RCLike.inner_apply, conj_trivial]
    have e : ((piHat m (i + 1) * t * -((binN k i : ℝ) / 2) : ℝ) : ℂ) * I +
        ((((binN k i : ℝ) * (piHat m (i + 1) * t) / 2) : ℝ) : ℂ) * I = 0 := by
      push_cast; ring
    rw [e, Complex.exp_zero, one_mul]
    congr 2
    field_simp
  have hunif : ∀ j : Fin 4, charFun (P.map (ω j)) (piHat m κ * t) =
      ((Real.sinc (π * (t / (2 * π)) * piHat m κ / 2) : ℝ) : ℂ) := by
    intro j
    rw [(hω j).map_eq, charFun_uniform_quarter]
    congr 2
    field_simp
    ring
  simp_rw [hbin, hunif]
  rw [prod_const, card_univ, Fintype.card_fin]
  unfold psiW
  push_cast
  rfl

/-! ### Poisson summation and Proposition 7.12(b) -/

open Complex in
/-- **`N ∑_{l ∈ ℤ} f_W(lN) = 1 + V_k`**, by Poisson summation for `x ↦ f_W(xN)`, whose Fourier
transform at `n` is `N⁻¹ Ψ(n/N) = N⁻¹ φ(n)`, and Proposition 7.12(a). -/
theorem tsum_densityW_eq {m k κ : ℕ} (hkκ : k ≤ κ) (hκ : 1 ≤ κ) :
    ((m : ℝ) + 1) * ∑' l : ℤ, densityW m k κ (l * ((m : ℝ) + 1)) = 1 + relVariance m k κ := by
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hN : 0 < N := by positivity
  set g : ℝ → ℂ := fun x => (densityW m k κ (x * N) : ℂ) with hg
  have hgc : Continuous g := Complex.continuous_ofReal.comp
    ((continuous_densityW m k κ).comp (continuous_id.mul continuous_const))
  have hgsupp : HasCompactSupport g := by
    have h1 := (hasCompactSupport_densityW m k κ).comp_homeomorph (Homeomorph.mulRight₀ N hN.ne')
    exact h1.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hgO : g =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    have hev : g =ᶠ[Filter.cocompact ℝ] fun _ => 0 := by
      filter_upwards [hgsupp.isCompact.compl_mem_cocompact] with x hx
      exact image_eq_zero_of_notMem_tsupport hx
    exact (Asymptotics.isBigO_zero _ _).congr' hev.symm (Filter.EventuallyEq.refl _ _)
  have hFg : ∀ ξ : ℝ, 𝓕 g ξ = ((N⁻¹ * psiW m k κ (ξ / N) : ℝ) : ℂ) := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    have h := Measure.integral_comp_mul_right
      (fun y => Complex.exp (↑(-2 * π * y * (ξ / N)) * I) • (densityW m k κ y : ℂ)) N
    have e : (fun x : ℝ => Complex.exp (↑(-2 * π * x * ξ) * I) • g x) =
        fun x => (fun y => Complex.exp (↑(-2 * π * y * (ξ / N)) * I) • (densityW m k κ y : ℂ))
          (x * N) := by
      ext x
      simp only [hg]
      congr 3
      field_simp
    rw [e, h, ← Real.fourier_real_eq_integral_exp_smul, fourier_densityW,
      abs_of_pos (inv_pos.mpr hN), Complex.real_smul]
    push_cast
    ring
  have hφ : ∀ n : ℤ, psiW m k κ ((n : ℝ) / N) = phiGen m k κ n := fun n => psiW_eq_phiGen hkκ n
  have hsumR : HasSum (fun n : ℤ => N⁻¹ * phiGen m k κ n) (N⁻¹ * (1 + relVariance m k κ)) :=
    (hasSum_phiGen (m := m) (k := k) hκ).mul_left N⁻¹
  have hsumC : HasSum (fun n : ℤ => 𝓕 g n) ((N⁻¹ * (1 + relVariance m k κ) : ℝ) : ℂ) := by
    have := (Complex.ofRealCLM.hasSum hsumR)
    simp only [Complex.ofRealCLM_apply] at this
    convert this using 1
    ext n
    rw [hFg, hφ]
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hgc (by norm_num : (1 : ℝ) < 2)
    hgO hsumC.summable 0
  have hfour : ∀ n : ℤ, fourier n ((0 : ℝ) : UnitAddCircle) = 1 := fun n => by
    rw [fourier_coe_apply]; simp
  simp only [zero_add, hfour, mul_one] at hP
  rw [hsumC.tsum_eq] at hP
  have hreal : ((∑' l : ℤ, densityW m k κ (l * N) : ℝ) : ℂ) =
      ((N⁻¹ * (1 + relVariance m k κ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact hP
  have := Complex.ofReal_injective hreal
  rw [this]
  field_simp

open ProbabilityTheory in
/-- **Proposition 7.12(b).** Let `ζ_1, …, ζ_{κ-1}, ω_1, …, ω_4` be independent random variables
(`ζ i` for `i : Fin (κ - 1)` stands for `ζ_{i+1}`) with `ζ_i + 2 ~ Bin(4, 1/2)` for `i < k`,
`ζ_i + 1 ~ Bin(2, 1/2)` for `k ≤ i < κ`, and `ω_j` uniform on `[-1/4, 1/4]`, and let
`W = ∑_{i<κ} ζ_i Π̂_i + Π̂_κ(ω_1 + ⋯ + ω_4)`. Then `W` has the continuous density `f_W = densityW`
(i.e. its law is `f_W(y) dy`), and `1 + V_k = N ∑_{l ∈ ℤ} f_W(lN)`. -/
theorem density_W {m k κ : ℕ} (hkκ : k ≤ κ) (hκ : 1 ≤ κ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (ζ : Fin (κ - 1) → Ω → ℝ) (ω : Fin 4 → Ω → ℝ)
    (hind : iIndepFun (Sum.elim ζ ω) P)
    (hζ : ∀ i, HasLaw (fun x => ζ i x + (binN k i : ℝ) / 2) Bin(ℝ, binN k i, halfI) P)
    (hω : ∀ j, pdf.IsUniform (ω j) (Set.Icc (-1 / 4 : ℝ) (1 / 4)) P) :
    HasLaw (fun x => ∑ i, ζ i x * piHat m (i + 1) + piHat m κ * ∑ j, ω j x)
        (volume.withDensity fun y => ENNReal.ofReal (densityW m k κ y)) P ∧
      Continuous (densityW m k κ) ∧ (∀ y, 0 ≤ densityW m k κ y) ∧
      1 + relVariance m k κ =
        ((m : ℝ) + 1) * ∑' l : ℤ, densityW m k κ (l * ((m : ℝ) + 1)) := by
  set W : Ω → ℝ := fun x => ∑ i, ζ i x * piHat m (i + 1) + piHat m κ * ∑ j, ω j x with hWdef
  have hmeasζ : ∀ i, AEMeasurable (ζ i) P := fun i => by
    have h1 := (hζ i).aemeasurable.sub_const ((binN k i : ℝ) / 2)
    have h2 : (fun x => ζ i x + (binN k i : ℝ) / 2 - (binN k i : ℝ) / 2) = ζ i := by ext; ring
    rwa [h2] at h1
  have hmeasW : AEMeasurable W P := by
    refine (Finset.aemeasurable_fun_sum _ fun i _ => (hmeasζ i).mul_const _).add
      ((Finset.aemeasurable_fun_sum _ fun j _ => (hω j).aemeasurable).const_mul _)
  refine ⟨⟨hmeasW, ?_⟩, continuous_densityW m k κ, densityW_nonneg m k κ,
    (tsum_densityW_eq hkκ hκ).symm⟩
  have : IsFiniteMeasure (volume.withDensity fun y => ENNReal.ofReal (densityW m k κ y)) :=
    isFiniteMeasure_withDensity_ofReal (integrable_densityW m k κ).hasFiniteIntegral
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hmeasW).mpr inferInstance
  apply Measure.ext_of_charFun
  ext t
  rw [hWdef, charFun_lawW ζ ω hind hζ hω t, charFun_withDensity_densityW]

open ProbabilityTheory in
/-- The identity `E exp(2πirW/N) = φ_k(r)` of the proof of Proposition 7.12(b). -/
theorem charFun_lawW_eq_straddlePhi {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (ζ : Fin (κ - 1) → Ω → ℝ) (ω : Fin 4 → Ω → ℝ)
    (hind : iIndepFun (Sum.elim ζ ω) P)
    (hζ : ∀ i, HasLaw (fun x => ζ i x + (binN k i : ℝ) / 2) Bin(ℝ, binN k i, halfI) P)
    (hω : ∀ j, pdf.IsUniform (ω j) (Set.Icc (-1 / 4 : ℝ) (1 / 4)) P) (r : ℤ) :
    charFun (P.map (fun x => ∑ i, ζ i x * piHat m (i + 1) + piHat m κ * ∑ j, ω j x))
        (2 * π * r / ((m : ℝ) + 1)) = (straddlePhi m k κ r : ℂ) := by
  rw [charFun_lawW ζ ω hind hζ hω, ← phiGen_eq_straddlePhi hk hkκ, ← psiW_eq_phiGen hkκ]
  congr 2
  field_simp

/-- **Proposition 7.12(a) and (c)**, restated in this file (see `StraddleFourier`):
`V_k = ∑_{r ≠ 0} φ_k(r)`, `V_k ≥ F_k` and `F_k = F(n_κ, κ - k)`. -/
theorem exact_form_V {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k < κ) (hκm : κ ≤ m) :
    HasSum (fun r : ℤ => if r = 0 then 0 else straddlePhi m k κ r) (relVariance m k κ) ∧
      fineFloorK m k κ ≤ relVariance m k κ ∧ fineFloorK m k κ = fineFloor (m - κ + 1) (κ - k) :=
  ⟨hasSum_straddlePhi_ne_zero hk hkκ.le, fineFloorK_le_relVariance hk hkκ.le,
    fineFloorK_eq hk hkκ hκm⟩

open ProbabilityTheory in
/-- The hypotheses of `density_W` are satisfiable: the coordinates of the product probability
space `∏_s μ_s` with the prescribed laws `μ_s`. -/
theorem density_W_model_exists (k κ : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ζ : Fin (κ - 1) → Ω → ℝ) (ω : Fin 4 → Ω → ℝ),
      iIndepFun (Sum.elim ζ ω) P ∧
      (∀ i, HasLaw (fun x => ζ i x + (binN k i : ℝ) / 2) Bin(ℝ, binN k i, halfI) P) ∧
      ∀ j, pdf.IsUniform (ω j) (Set.Icc (-1 / 4 : ℝ) (1 / 4)) P := by
  let μ : Fin (κ - 1) ⊕ Fin 4 → Measure ℝ := Sum.elim
    (fun i => (Bin(ℝ, binN k i, halfI)).map (fun y => y - (binN k i : ℝ) / 2))
    (fun _ => ProbabilityTheory.cond volume (Set.Icc (-1 / 4 : ℝ) (1 / 4)))
  have hbin : ∀ n : ℕ, IsProbabilityMeasure (Bin(ℝ, n, halfI)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (Measurable.of_discrete).aemeasurable).mpr inferInstance
  have hprob : ∀ s, IsProbabilityMeasure (μ s) := by
    intro s
    cases s with
    | inl i =>
      have := hbin (binN k i)
      exact (Measure.isProbabilityMeasure_map_iff (measurable_sub_const _).aemeasurable).mpr this
    | inr j =>
      apply cond_isProbabilityMeasure_of_finite
      · rw [Real.volume_Icc]; norm_num
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  refine ⟨Fin (κ - 1) ⊕ Fin 4 → ℝ, inferInstance, Measure.pi μ, inferInstance,
    fun i x => x (Sum.inl i), fun j x => x (Sum.inr j), ?_, ?_, ?_⟩
  · have h := iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)
    convert h using 1
    ext s x
    cases s <;> rfl
  · intro i
    refine ⟨((measurable_pi_apply _).add_const _).aemeasurable, ?_⟩
    have e : (fun x : Fin (κ - 1) ⊕ Fin 4 → ℝ => x (Sum.inl i) + (binN k i : ℝ) / 2) =
        (fun y => y + (binN k i : ℝ) / 2) ∘ (fun x : Fin (κ - 1) ⊕ Fin 4 → ℝ => x (Sum.inl i)) :=
      rfl
    have hev : (Measure.pi μ).map (fun x : Fin (κ - 1) ⊕ Fin 4 → ℝ => x (Sum.inl i)) =
        μ (Sum.inl i) := (measurePreserving_eval μ (Sum.inl i)).map_eq
    have hmm := Measure.map_map (μ := Measure.pi μ) (measurable_add_const ((binN k i : ℝ) / 2))
      (measurable_pi_apply (Sum.inl i))
    rw [e, ← hmm, hev]
    simp only [μ, Sum.elim_inl]
    rw [Measure.map_map (measurable_add_const _) (measurable_sub_const _)]
    have hid : ((fun y : ℝ => y + (binN k i : ℝ) / 2) ∘ fun y => y - (binN k i : ℝ) / 2) = id := by
      ext y; simp
    rw [hid, Measure.map_id]
  · intro j
    refine ⟨(measurable_pi_apply _).aemeasurable, ?_⟩
    exact (measurePreserving_eval μ (Sum.inr j)).map_eq

/-! ### The sidebands: `SB_k = N ∑_l f_W(lN) - ∑_l f_W(l)` -/

open Complex in
/-- Poisson summation at any scale `c > 0`: if `∑_n Ψ(n/c) = A`, then `c ∑_{l ∈ ℤ} f_W(lc) = A`. -/
theorem densityW_poisson_scale {m k κ : ℕ} {c A : ℝ} (hc : 0 < c)
    (hA : HasSum (fun n : ℤ => psiW m k κ (n / c)) A) :
    c * ∑' l : ℤ, densityW m k κ (l * c) = A := by
  set g : ℝ → ℂ := fun x => (densityW m k κ (x * c) : ℂ) with hg
  have hgc : Continuous g := Complex.continuous_ofReal.comp
    ((continuous_densityW m k κ).comp (continuous_id.mul continuous_const))
  have hgsupp : HasCompactSupport g := by
    have h1 := (hasCompactSupport_densityW m k κ).comp_homeomorph (Homeomorph.mulRight₀ c hc.ne')
    exact h1.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hgO : g =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    have hev : g =ᶠ[Filter.cocompact ℝ] fun _ => 0 := by
      filter_upwards [hgsupp.isCompact.compl_mem_cocompact] with x hx
      exact image_eq_zero_of_notMem_tsupport hx
    exact (Asymptotics.isBigO_zero _ _).congr' hev.symm (Filter.EventuallyEq.refl _ _)
  have hFg : ∀ ξ : ℝ, 𝓕 g ξ = ((c⁻¹ * psiW m k κ (ξ / c) : ℝ) : ℂ) := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    have h := Measure.integral_comp_mul_right
      (fun y => Complex.exp (↑(-2 * π * y * (ξ / c)) * I) • (densityW m k κ y : ℂ)) c
    have e : (fun x : ℝ => Complex.exp (↑(-2 * π * x * ξ) * I) • g x) =
        fun x => (fun y => Complex.exp (↑(-2 * π * y * (ξ / c)) * I) • (densityW m k κ y : ℂ))
          (x * c) := by
      ext x
      simp only [hg]
      congr 3
      field_simp
    rw [e, h, ← Real.fourier_real_eq_integral_exp_smul, fourier_densityW,
      abs_of_pos (inv_pos.mpr hc), Complex.real_smul]
    push_cast
    ring
  have hsumC : HasSum (fun n : ℤ => 𝓕 g n) ((c⁻¹ * A : ℝ) : ℂ) := by
    have := Complex.ofRealCLM.hasSum (hA.mul_left c⁻¹)
    simp only [Complex.ofRealCLM_apply] at this
    convert this using 1
    ext n
    rw [hFg]
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hgc (by norm_num : (1 : ℝ) < 2)
    hgO hsumC.summable 0
  have hfour : ∀ n : ℤ, fourier n ((0 : ℝ) : UnitAddCircle) = 1 := fun n => by
    rw [fourier_coe_apply]; simp
  simp only [zero_add, hfour, mul_one] at hP
  rw [hsumC.tsum_eq] at hP
  have hreal : ((∑' l : ℤ, densityW m k κ (l * c) : ℝ) : ℂ) = ((c⁻¹ * A : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact hP
  rw [Complex.ofReal_injective hreal]
  field_simp

/-- `∑_{l ∈ ℤ} f_W(l) = ∑_{w ∈ ℤ} φ_k(Nw)` (Poisson summation with period `1`). -/
theorem tsum_densityW_int {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) :
    HasSum (fun w : ℤ => straddlePhi m k κ (((m : ℤ) + 1) * w)) (∑' l : ℤ, densityW m k κ l) := by
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hinj : Function.Injective (fun w : ℤ => ((m : ℤ) + 1) * w) := fun x y h =>
    mul_left_cancel₀ (by positivity : ((m : ℤ) + 1) ≠ 0) h
  have hs : Summable (fun w : ℤ => straddlePhi m k κ (((m : ℤ) + 1) * w)) :=
    (hasSum_straddlePhi (m := m) hk hkκ).summable.comp_injective hinj
  have hpsi : ∀ n : ℤ, psiW m k κ ((n : ℝ) / 1) = straddlePhi m k κ (((m : ℤ) + 1) * n) := by
    intro n
    rw [← phiGen_eq_straddlePhi hk hkκ, ← psiW_eq_phiGen hkκ]
    congr 1
    push_cast
    field_simp
  have h := densityW_poisson_scale (m := m) (k := k) (κ := κ) one_pos
    (A := ∑' w : ℤ, straddlePhi m k κ (((m : ℤ) + 1) * w))
    (by simp_rw [hpsi]; exact hs.hasSum)
  simp only [mul_one, one_mul] at h
  rw [h]
  exact hs.hasSum

/-- **The sidebands through the density**: `SB_k = N ∑_{l ∈ ℤ} f_W(lN) - ∑_{l ∈ ℤ} f_W(l)`. -/
theorem sideband_eq_densityW {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) :
    sideband m k κ = ((m : ℝ) + 1) * ∑' l : ℤ, densityW m k κ (l * ((m : ℝ) + 1)) -
      ∑' l : ℤ, densityW m k κ l := by
  set φ := straddlePhi m k κ with hφ
  set N : ℤ := (m : ℤ) + 1 with hNdef
  have hNpos : 0 < N := by positivity
  have hφs : Summable φ := (hasSum_straddlePhi (m := m) hk hkκ).summable
  have hV : HasSum (fun r : ℤ => if r = 0 then 0 else φ r) (relVariance m k κ) :=
    hasSum_straddlePhi_ne_zero hk hkκ
  have hpt : ∀ r : ℤ, (if r = 0 then 0 else φ r) =
      (if N ∣ r then 0 else φ r) + (if N ∣ r ∧ r ≠ 0 then φ r else 0) := by
    intro r
    by_cases hr : r = 0
    · subst hr; simp
    · by_cases hd : N ∣ r
      · simp [hr, hd]
      · simp [hr, hd]
  have hs1 : Summable (fun r : ℤ => if N ∣ r then 0 else φ r) :=
    hφs.summable_of_eq_zero_or_self fun r => by
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hV' : relVariance m k κ = sideband m k κ +
      ∑' r : ℤ, (if N ∣ r ∧ r ≠ 0 then φ r else 0) := by
    rw [← hV.tsum_eq]
    simp_rw [hpt]
    rw [Summable.tsum_add hs1 (summable_ite hφs _)]
    rfl
  have hinjN : Function.Injective (fun w : ℤ => N * w) := fun x y h =>
    mul_left_cancel₀ hNpos.ne' h
  have hmult : ∑' r : ℤ, (if N ∣ r ∧ r ≠ 0 then φ r else 0) =
      ∑' w : ℤ, (if w = 0 then 0 else φ (N * w)) := by
    rw [← hinjN.tsum_eq]
    · refine tsum_congr fun w => ?_
      by_cases hw : w = 0
      · simp [hw]
      · have : N * w ≠ 0 := mul_ne_zero hNpos.ne' hw
        simp [hw, this]
    · intro r hr
      rw [Function.mem_support] at hr
      by_cases h : N ∣ r ∧ r ≠ 0
      · obtain ⟨⟨w, hw⟩, _⟩ := h
        exact ⟨w, hw.symm⟩
      · simp [h] at hr
  have hsw : Summable (fun w : ℤ => φ (N * w)) := hφs.comp_injective hinjN
  have hite : ∑' w : ℤ, (if w = 0 then 0 else φ (N * w)) = ∑' w : ℤ, φ (N * w) - 1 := by
    rw [hsw.tsum_eq_add_tsum_ite 0]
    simp only [mul_zero]
    rw [show φ 0 = 1 from straddlePhi_zero hk hkκ]
    ring
  have hint := (tsum_densityW_int (m := m) hk hkκ).tsum_eq
  have hκ : 1 ≤ κ := le_trans hk hkκ
  have hmain := tsum_densityW_eq (m := m) hkκ hκ
  rw [hmain]
  rw [hmult, hite] at hV'
  rw [← hint]
  linarith

end MergeDepth
