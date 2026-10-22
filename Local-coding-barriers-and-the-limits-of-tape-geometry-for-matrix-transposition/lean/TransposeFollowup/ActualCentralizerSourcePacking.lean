import TransposeFollowup.ActualCentralizerPacking
import TransposeFollowup.CubicSourceWordLocality
import TransposeFollowup.PowerClusterConcentration

/-! The actual-frame cubic lower bound now reaches an actual fixed power
of the original set. The approximant error, localization, input spacing,
frame scale and right-translation cost are all charged. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

/-- Charge integer rounding once for both global and local cubic packing. -/
theorem nat_cubic_bound_of_quotient (n L : ℕ) {U : ℝ} (hL : 0 < L)
    (hbound : ((n / L : ℕ) : ℝ) ^ 3 ≤ U) :
    (n : ℝ) ^ 3 ≤ 4 * (L : ℝ) ^ 3 * (U + 1) := by
  have hn : (n : ℝ) ≤ (((n / L : ℕ) : ℝ) + 1) * (L : ℝ) := by
    have hh : n ≤ (n / L + 1) * L := by
      simpa only [Nat.add_mul, one_mul] using (Nat.lt_div_mul_add hL).le
    exact_mod_cast hh
  have hm : (((n / L : ℕ) : ℝ) + 1) ^ 3 ≤ 4 * (U + 1) := by
    have hh := add_pow_le (Nat.cast_nonneg (n / L) : (0 : ℝ) ≤ ((n / L : ℕ) : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1) 3
    norm_num at hh
    linarith
  calc
    _ ≤ ((((n / L : ℕ) : ℝ) + 1) * (L : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hn 3
    _ = (L : ℝ) ^ 3 * (((n / L : ℕ) : ℝ) + 1) ^ 3 := by ring
    _ ≤ (L : ℝ) ^ 3 * (4 * (U + 1)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem actual_localized_source_packing_near {ι : Type*} [Fintype ι]
    (f X : ι → G) (c t : ι → ℝ) (base : G) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d R ε s : ℝ} {η : ℝ≥0} {m : ℕ}
    (hA1 : 1 ∈ A) (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α) (hαsmall : 2 * (5 : ℝ) ^ 34 * α ≤ 1)
    (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hd₀ : 0 < d₀)
    (hspan : d₀ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|)
    (hz : z ∈ mobiusIdentityBall (1 / 2)) (hr₀ : 0 < r₀)
    (hfar : r₀ ≤ dist (z : RMat) 1)
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hscale : 128 * ((4 : ℝ) ^ 68) ^ 2 ≤ M)
    (hδ : 0 < δ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m)
    (hf : ∀ x i j, |f x i j| ≤ B)
    (hform : ∀ x, (f x : RMat) = scalarAffine (z : RMat) (c x) (t x))
    (hbranch : 8 * B * δ ≤ 1) (hradius : 8 * B * δ ≤ (r₀ / 8) * r)
    (hcard : binCount B δ ^ 4 * m ≤ Fintype.card ι)
    (hd : 0 < d)
    (hframe : d ≤ (r₀ / 8) ^ 3 / (3456 * (96 * ((4 : ℝ) ^ 34) ^ 4 / d₀) ^ 3))
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hsep : ∀ x y, x ≠ y →
      10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) < dist (f x : RMat) (f y : RMat))
    (hbase : base ∈ A) (hX : ∀ i, X i ∈ A) (hBR : B ≤ R)
    (hHR : (4 : ℝ) ^ 68 ≤ R) (hε : 0 ≤ ε) (hη : 0 < η)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * X i : G) : RMat) ≤ ε)
    (hs : 0 ≤ s) (hdiam : ∀ i j, dist (f i : RMat) (f j : RMat) ≤ 2 * s) :
    ∃ v ∈ A ^ 68,
    let T := (fun g : G => (g : RMat)) ''
      {g : G | g ∈ A ^ 142 ∧ dist (g : RMat) (v : RMat) ≤ 40 * (2 * R) ^ 11 * (s + ε)}
    Metric.externalCoveringNumber η T ≠ ⊤ ∧
      (m : ℝ) ^ 3 ≤
        (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
          (Metric.externalCoveringNumber η T : ℝ≥0∞).toReal := by
  obtain ⟨u, huA, v, hvA, i₀, F, s, _hF, _hclose, _hPfin, hpack⟩ :=
    exists_actual_localized_cubic_packing f c t hA1 hAi hα hαone hA hαsmall
      hp hq hpq hd₀ hspan hz hr₀ hfar hB hM hscale hδ hr hr1 hm hf hform
      hbranch hradius hcard hd hframe hsmall habsorb hsep
  have hAb : A ⊆ matrixEntryBox 2 :=
    hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hub : ∀ i j, |u i j| ≤ R := by
    intro i j
    have hh : |u i j| ≤ (4 : ℝ) ^ 34 := by
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
        set_pow_subset_matrixEntryBox hAb 34 huA i j
    exact hh.trans ((pow_le_pow_right₀ (by norm_num) (by norm_num : 34 ≤ 68)).trans hHR)
  have hvb : ∀ i j, |v i j| ≤ R := by
    intro i j
    have hh : |v i j| ≤ (4 : ℝ) ^ 68 := by
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
        set_pow_subset_matrixEntryBox hAb 68 hvA i j
    exact hh.trans hHR
  have hab : ∀ i j k, |(base⁻¹ * X i : G) j k| ≤ R := by
    intro i j k
    have hh : |(base⁻¹ * X i : G) j k| ≤ 8 := by
      simpa only [show (2 : ℝ) * 2 * 2 = 8 by norm_num] using
        matrixEntryBox_mul (matrixEntryBox_inv (hAb hbase)) (hAb (hX i)) j k
    exact hh.trans ((by norm_num : (8 : ℝ) ≤ 4 ^ 68).trans hHR)
  obtain ⟨_hfin, hTfin, hbound⟩ := cubic_source_word_covering_transfer_near f X base i₀
    (fun x : ↥F => s x) u v hAi hAb hX huA hvA (hB.trans hBR) hε hs hη
    (fun i j k => (hf i j k).trans hBR) hab hub hvb he hdiam
  exact ⟨v, hvA, hTfin, hpack.trans hbound⟩

theorem actual_localized_source_packing {ι : Type*} [Fintype ι]
    (f X : ι → G) (c t : ι → ℝ) (base : G) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d R ε : ℝ} {η : ℝ≥0} {m : ℕ}
    (hA1 : 1 ∈ A) (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α) (hαsmall : 2 * (5 : ℝ) ^ 34 * α ≤ 1)
    (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hd₀ : 0 < d₀)
    (hspan : d₀ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|)
    (hz : z ∈ mobiusIdentityBall (1 / 2)) (hr₀ : 0 < r₀)
    (hfar : r₀ ≤ dist (z : RMat) 1)
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hscale : 128 * ((4 : ℝ) ^ 68) ^ 2 ≤ M)
    (hδ : 0 < δ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m)
    (hf : ∀ x i j, |f x i j| ≤ B)
    (hform : ∀ x, (f x : RMat) = scalarAffine (z : RMat) (c x) (t x))
    (hbranch : 8 * B * δ ≤ 1) (hradius : 8 * B * δ ≤ (r₀ / 8) * r)
    (hcard : binCount B δ ^ 4 * m ≤ Fintype.card ι)
    (hd : 0 < d)
    (hframe : d ≤ (r₀ / 8) ^ 3 / (3456 * (96 * ((4 : ℝ) ^ 34) ^ 4 / d₀) ^ 3))
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hsep : ∀ x y, x ≠ y →
      10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) < dist (f x : RMat) (f y : RMat))
    (hbase : base ∈ A) (hX : ∀ i, X i ∈ A) (hBR : B ≤ R)
    (hHR : (4 : ℝ) ^ 68 ≤ R) (hε : 0 ≤ ε) (hη : 0 < η)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * X i : G) : RMat) ≤ ε) :
    let T := (fun g : G => (g : RMat)) '' (A ^ 142)
    Metric.externalCoveringNumber η T ≠ ⊤ ∧
      (m : ℝ) ^ 3 ≤
        (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
          (Metric.externalCoveringNumber η T : ℝ≥0∞).toReal := by
  have hnorm (i : ι) : ‖(f i : RMat)‖ ≤ 2 * B :=
    frobenius_norm_le_of_entry_bound (by linarith : 0 ≤ B) (hf i)
  have hdiam (i j : ι) : dist (f i : RMat) (f j : RMat) ≤ 2 * (2 * B) := by
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hnorm i, hnorm j])
  obtain ⟨v, _hv, _hlocalfin, hlocal⟩ := actual_localized_source_packing_near f X c t base
    hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfar
    hB hM hscale hδ hr hr1 hm hf hform hbranch hradius hcard hd hframe hsmall habsorb
    hsep hbase hX hBR hHR hε hη he (by positivity : 0 ≤ 2 * B) hdiam
  let T := (fun g : G => (g : RMat)) '' (A ^ 142)
  have hAb : A ⊆ matrixEntryBox 2 :=
    hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hTfin : Metric.externalCoveringNumber η T ≠ ⊤ :=
    finite_coveringNumber_of_entry_bound (by positivity : 0 ≤ (4 : ℝ) ^ 142) hη (by
      rintro z ⟨g, hg, rfl⟩ i j
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
        set_pow_subset_matrixEntryBox hAb 142 hg i j)
  have hsub : (fun g : G => (g : RMat)) ''
      {g : G | g ∈ A ^ 142 ∧ dist (g : RMat) (v : RMat) ≤
        40 * (2 * R) ^ 11 * (2 * B + ε)} ⊆ T :=
    Set.image_mono (fun _ hg => hg.1)
  have hmono := ENNReal.toReal_mono (ENat.toENNReal_ne_top.mpr hTfin)
    (ENat.toENNReal_mono (Metric.externalCoveringNumber_mono_set (ε := η) hsub))
  exact ⟨hTfin, hlocal.trans (mul_le_mul_of_nonneg_left hmono (by positivity))⟩

/-- Cubic packing of a cluster, normalized by the ORIGINAL ambient set.
Its radius decay comes from the proved local profile of the actual power. -/
theorem actual_localized_source_packing_concentration {ι : Type*} [Fintype ι]
    (f X : ι → G) (c t : ι → ℝ) (base : G) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d R ε s K J κ γ : ℝ} {η : ℝ≥0} {m : ℕ}
    (hA1 : 1 ∈ A) (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α) (hαsmall : 2 * (5 : ℝ) ^ 34 * α ≤ 1)
    (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hd₀ : 0 < d₀)
    (hspan : d₀ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|)
    (hz : z ∈ mobiusIdentityBall (1 / 2)) (hr₀ : 0 < r₀)
    (hfar : r₀ ≤ dist (z : RMat) 1)
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hscale : 128 * ((4 : ℝ) ^ 68) ^ 2 ≤ M)
    (hδ : 0 < δ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m)
    (hf : ∀ x i j, |f x i j| ≤ B)
    (hform : ∀ x, (f x : RMat) = scalarAffine (z : RMat) (c x) (t x))
    (hbranch : 8 * B * δ ≤ 1) (hradius : 8 * B * δ ≤ (r₀ / 8) * r)
    (hcard : binCount B δ ^ 4 * m ≤ Fintype.card ι)
    (hd : 0 < d)
    (hframe : d ≤ (r₀ / 8) ^ 3 / (3456 * (96 * ((4 : ℝ) ^ 34) ^ 4 / d₀) ^ 3))
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hsep : ∀ x y, x ≠ y →
      10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) < dist (f x : RMat) (f y : RMat))
    (hbase : base ∈ A) (hX : ∀ i, X i ∈ A) (hBR : B ≤ R)
    (hHR : (4 : ℝ) ^ 68 ≤ R) (hε : 0 ≤ ε) (hη : 0 < η)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * X i : G) : RMat) ≤ ε)
    (hs : 0 ≤ s) (hdiam : ∀ i j, dist (f i : RMat) (f j : RMat) ≤ 2 * s)
    (hK : 1 ≤ K) (hκ : 0 ≤ κ) (hγ : 0 ≤ γ) (hηone : (η : ℝ) ≤ 1)
    (houtRadius : (η : ℝ) ≤ 40 * (2 * R) ^ 11 * (s + ε))
    (hproduct : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ 284)) : ℝ≥0∞).toReal ≤
        K * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (hsize : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ 142)) : ℝ≥0∞).toReal ≤
        J * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (hdistribution : ∀ ρ : ℝ, (η : ℝ) < ρ → ρ < (η : ℝ) ^ γ →
      ∃ T : Finset G, (T : Set G) ⊆ A ∧
        Metric.IsSeparated (ENNReal.ofReal ρ)
          ((fun x : G => (x : RMat)) '' (T : Set G)) ∧
        ρ ^ (-κ) ≤ (T.card : ℝ)) :
    let Bpow := (4 : ℝ) ^ 142
    let ρ := 40 * (2 * R) ^ 11 * (s + ε)
    let E := (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4
    (m : ℝ) ^ 3 ≤ E *
      ((8 * Bpow + 1) ^ 4 * (8 * Bpow ^ 2 + 4 * Bpow + 1) ^ κ * K * J *
        (η : ℝ) ^ (-(γ * κ)) * ρ ^ κ *
          (Metric.externalCoveringNumber η
            ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal) := by
  obtain ⟨v, hv, _hTfin, hpack⟩ := actual_localized_source_packing_near f X c t base
    hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfar
    hB hM hscale hδ hr hr1 hm hf hform hbranch hradius hcard hd hframe hsmall habsorb
    hsep hbase hX hBR hHR hε hη he hs hdiam
  have hv142 : v ∈ A ^ 142 := Set.pow_subset_pow_right hA1 (by norm_num : 68 ≤ 142) hv
  have hAb : A ⊆ matrixEntryBox 2 :=
    hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hlocal := (power_cluster_coveringNumber_le_of_multiscale 142 (by norm_num)
    hA1 hAb hK hκ hγ hη hηone houtRadius hproduct hsize hdistribution v hv142).2
  exact hpack.trans (mul_le_mul_of_nonneg_left hlocal (by positivity))

/-- Full finite-cluster bound, including small or empty clusters.
The integer localization loss and additive one are retained explicitly. -/
theorem finite_source_cluster_cubic_bound {ι : Type*} [Fintype ι]
    (f X : ι → G) (c t : ι → ℝ) (base : G) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d R ε s K J κ γ : ℝ} {η : ℝ≥0}
    (hA1 : 1 ∈ A) (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α) (hαsmall : 2 * (5 : ℝ) ^ 34 * α ≤ 1)
    (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hd₀ : 0 < d₀)
    (hspan : d₀ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|)
    (hz : z ∈ mobiusIdentityBall (1 / 2)) (hr₀ : 0 < r₀)
    (hfar : r₀ ≤ dist (z : RMat) 1)
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hscale : 128 * ((4 : ℝ) ^ 68) ^ 2 ≤ M)
    (hδ : 0 < δ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hf : ∀ x i j, |f x i j| ≤ B)
    (hform : ∀ x, (f x : RMat) = scalarAffine (z : RMat) (c x) (t x))
    (hbranch : 8 * B * δ ≤ 1) (hradius : 8 * B * δ ≤ (r₀ / 8) * r)
    (hd : 0 < d)
    (hframe : d ≤ (r₀ / 8) ^ 3 / (3456 * (96 * ((4 : ℝ) ^ 34) ^ 4 / d₀) ^ 3))
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hsep : ∀ x y, x ≠ y →
      10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) < dist (f x : RMat) (f y : RMat))
    (hbase : base ∈ A) (hX : ∀ i, X i ∈ A) (hBR : B ≤ R)
    (hHR : (4 : ℝ) ^ 68 ≤ R) (hε : 0 ≤ ε) (hη : 0 < η)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * X i : G) : RMat) ≤ ε)
    (hs : 0 ≤ s) (hdiam : ∀ i j, dist (f i : RMat) (f j : RMat) ≤ 2 * s)
    (hK : 1 ≤ K) (hJ : 0 ≤ J) (hκ : 0 ≤ κ) (hγ : 0 ≤ γ) (hηone : (η : ℝ) ≤ 1)
    (houtRadius : (η : ℝ) ≤ 40 * (2 * R) ^ 11 * (s + ε))
    (hproduct : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ 284)) : ℝ≥0∞).toReal ≤
        K * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (hsize : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ 142)) : ℝ≥0∞).toReal ≤
        J * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (hdistribution : ∀ ρ : ℝ, (η : ℝ) < ρ → ρ < (η : ℝ) ^ γ →
      ∃ T : Finset G, (T : Set G) ⊆ A ∧
        Metric.IsSeparated (ENNReal.ofReal ρ)
          ((fun x : G => (x : RMat)) '' (T : Set G)) ∧
        ρ ^ (-κ) ≤ (T.card : ℝ)) :
    let Bpow := (4 : ℝ) ^ 142
    let ρ := 40 * (2 * R) ^ 11 * (s + ε)
    let E := (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4
    let L := binCount B δ ^ 4
    let U := E *
      ((8 * Bpow + 1) ^ 4 * (8 * Bpow ^ 2 + 4 * Bpow + 1) ^ κ * K * J *
        (η : ℝ) ^ (-(γ * κ)) * ρ ^ κ *
          (Metric.externalCoveringNumber η
            ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (Fintype.card ι : ℝ) ^ 3 ≤ 4 * (L : ℝ) ^ 3 * (U + 1) := by
  intro Bpow ρ E L U
  have hL : 0 < L := pow_pos (binCount_pos B δ) 4
  have hK0 : 0 ≤ K := by linarith
  have hρ : 0 ≤ ρ := η.coe_nonneg.trans houtRadius
  have hU : 0 ≤ U := by dsimp only [U, E, Bpow]; positivity
  let m := Fintype.card ι / L
  have hmcard : L * m ≤ Fintype.card ι := Nat.mul_div_le _ _
  have hm : (m : ℝ) ^ 3 ≤ U := by
    by_cases hmzero : m = 0
    · simpa only [hmzero, Nat.cast_zero, zero_pow (by norm_num : 3 ≠ 0)] using hU
    · exact actual_localized_source_packing_concentration f X c t base
        hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfar
        hB hM hscale hδ hr hr1 (Nat.pos_of_ne_zero hmzero) hf hform hbranch hradius
        hmcard hd hframe hsmall habsorb hsep hbase hX hBR hHR hε hη he hs hdiam
        hK hκ hγ hηone houtRadius hproduct hsize hdistribution
  exact nat_cubic_bound_of_quotient (Fintype.card ι) L hL hm

end TransposeFollowup.SL2Projection
