import TransposeFollowup.TraceCommutingExtraction
import TransposeFollowup.CommutingFamilyCubicBound
import TransposeFollowup.ApproximatePowerCover

/-! A second trace-driven extraction uses the original conjugating set.
The resulting commuting family has actual source words in that same set,
so cubic packing applies with its existing spanning frame. Both product
covering numbers are bounded by the actual approximate-group envelope;
the positive ambient covering number is then cancelled. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem trace_reextraction_cubic_bound {U A D : Set G} (Y : Finset G) (k : ℕ)
    {p q : G} {Q α d₀ r₀ M r δ d : ℝ} {η σ : ℝ≥0}
    (hQ : 1 ≤ Q) (hU : U ⊆ matrixEntryBox Q) (hUi : U⁻¹ = U)
    (hY : (Y : Set G) ⊆ U ^ 2) (hdouble : U ^ 2 ⊆ (Y : Set G) * U)
    (hAloc : A = U ^ 2 ∩ mobiusIdentityBall α)
    (hA1 : 1 ∈ A) (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hαsmall : 2 * (5 : ℝ) ^ 34 * α ≤ 1)
    (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hd₀ : 0 < d₀)
    (hspan : d₀ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|)
    (hDn : D.Nonempty) (hDpow : D ⊆ A ^ k)
    (hDnear : D ⊆ mobiusIdentityBall (1 / 2))
    (hr₀ : 0 < r₀) (hDfar : ∀ g ∈ D, r₀ ≤ dist (g : RMat) 1)
    (hη : 0 < η) (hσ : 0 < σ) (herror : 819200 * (η : ℝ) ≤ r₀)
    (hM : 1 ≤ M) (hscale : 128 * ((4 : ℝ) ^ 68) ^ 2 ≤ M)
    (hδ : 0 < δ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hbranch : 8 * 9 * δ ≤ 1) (hradius : 8 * 9 * δ ≤ (r₀ / 8) * r)
    (hd : 0 < d)
    (hframe : d ≤ (r₀ / 8) ^ 3 / (3456 * (96 * ((4 : ℝ) ^ 34) ^ 4 / d₀) ^ 3))
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hspacing : 10 * 9 * M * (384 * M ^ 4 / d * (η : ℝ)) ≤ 2 * (σ : ℝ)) :
    let N := (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal
    let T := (fun g : G => Matrix.trace (g : RMat)) '' D
    let P := fun n : ℕ => (8 * (2 * Q) ^ (4 * n + 3) + 1) ^ 4 *
      (Y.card : ℝ) ^ (2 * n + 1) * (33 ^ 4 * Q ^ 8 / α ^ 4)
    let H := (102400 * (2 : ℝ) ^ 7 / r₀ + 8 * 2 + 1) ^ 4
    let C := 6561 * (4 * (σ : ℝ) / (η : ℝ) + 1) ^ 4
    let L := binCount 9 δ ^ 4
    let R := (4 : ℝ) ^ 68
    let ε := 819200 * (η : ℝ) / r₀
    let E := (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4
    Metric.externalCoveringNumber η T ≠ ⊤ ∧
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η T : ℝ≥0∞).toReal ^ 3 ≤
        (9 * P (k + 1) * H) ^ 3 *
          (4 * (C * (L : ℝ)) ^ 3 * (E * P 141 * N + 1)) := by
  let N := (Metric.externalCoveringNumber η
    ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal
  let T := (fun g : G => Matrix.trace (g : RMat)) '' D
  let P := fun n : ℕ => (8 * (2 * Q) ^ (4 * n + 3) + 1) ^ 4 *
    (Y.card : ℝ) ^ (2 * n + 1) * (33 ^ 4 * Q ^ 8 / α ^ 4)
  let H := (102400 * (2 : ℝ) ^ 7 / r₀ + 8 * 2 + 1) ^ 4
  let C := 6561 * (4 * (σ : ℝ) / (η : ℝ) + 1) ^ 4
  let L := binCount 9 δ ^ 4
  let R := (4 : ℝ) ^ 68
  let ε := 819200 * (η : ℝ) / r₀
  let E := (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4
  have hA : A ⊆ mobiusIdentityBall α := by rw [hAloc]; exact Set.inter_subset_right
  have hAb : A ⊆ matrixEntryBox 2 :=
    hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hDb : D ⊆ matrixEntryBox 2 := hDnear.trans
    (mobiusIdentityBall_subset_entryBox_two (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num))
  have hexsmall : 1536 * (2 : ℝ) ^ 4 * (η : ℝ) ≤ r₀ := by
    have hη0 : (0 : ℝ) ≤ η := η.coe_nonneg
    norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num]
    linarith
  obtain ⟨g, hg, center, base, hbase, f, hform, hclose, _hcomm,
      hAfin, hTfin, _hCfin, _hVfin, hextract⟩ :=
    exists_trace_commuting_extraction (A := A) (D := D) (α := 1 / 2)
      (r := r₀) (B := 2) (η := η) (by norm_num) le_rfl hr₀ (by norm_num) hη
      ⟨1, hA1⟩ hDn hAb hDb hDnear hDfar hexsmall
  let S := {x : G | x ∈ A ∧ dist ((x * g * x⁻¹ : G) : RMat) center ≤ (η : ℝ)}
  let V := Set.range (fun x : S => (f x : RMat))
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hεone : ε ≤ 1 := (div_le_iff₀ hr₀).mpr (by simpa only [one_mul] using herror)
  have he (x : S) : dist (f x : RMat) ((base⁻¹ * x : G) : RMat) ≤ ε := by
    rw [dist_comm]
    convert (hclose x).2 using 1
    norm_num [ε]
  have hf (x : S) (i j : Fin 2) : |f x i j| ≤ 9 := by
    have hsource : base⁻¹ * x ∈ matrixEntryBox 8 := by
      convert matrixEntryBox_mul (matrixEntryBox_inv (hAb hbase.1)) (hAb x.property.1) using 1
      norm_num
    have hentry := (entry_error_le_frobenius_dist (f x : RMat)
      ((base⁻¹ * x : G) : RMat) i j).trans (he x)
    have htri := abs_add_le (f x i j - (base⁻¹ * x : G) i j) ((base⁻¹ * x : G) i j)
    rw [sub_add_cancel] at htri
    linarith [hsource i j]
  choose c t hct using hform
  obtain ⟨_hVfin', _h142fin, hcubic⟩ := commuting_family_cubic_bound f
    (fun x : S => (x : G)) c t base hA1 hAi hα hαone hA hαsmall hp hq hpq
    hd₀ hspan (hDnear hg) hr₀ (hDfar g hg) (by norm_num : (1 : ℝ) ≤ 9)
    hM hscale hδ hr hr1 hf hct hbranch hradius hd hframe hsmall habsorb
    hbase.1 (fun x => x.property.1) (by dsimp only [R]; norm_num : (9 : ℝ) ≤ R)
    (le_refl R) hε hη hσ he ⟨(f ⟨base, hbase⟩ : RMat), ⟨⟨base, hbase⟩, rfl⟩⟩ hspacing
  have henv (n : ℕ) :
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A ^ (n + 1))) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A ^ (n + 1))) : ℝ≥0∞).toReal ≤
        P n * N := by
    obtain ⟨_ha, hb, hc⟩ := localized_set_pow_coveringNumber Y n hQ hα hαone hη hU hUi hY hdouble
    rw [← hAloc] at hb hc
    exact ⟨hb, hc⟩
  have hCsub : A * D * A⁻¹ ⊆ A ^ (k + 2) := by
    calc
      _ ⊆ A * A ^ k * A := Set.mul_subset_mul (Set.mul_subset_mul subset_rfl hDpow) hAi.subset
      _ = _ := by rw [← pow_succ', ← pow_succ]
  have hCcover := Metric.externalCoveringNumber_mono_set (ε := η)
    (Set.image_mono (f := fun x : G => (x : RMat)) hCsub)
  have henvC := henv (k + 1)
  have hCbound : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) : ℝ≥0∞).toReal ≤ P (k + 1) * N := by
    apply (ENNReal.toReal_mono (ENat.toENNReal_ne_top.mpr henvC.1)
      (ENat.toENNReal_mono hCcover)).trans henvC.2
  have hTbound : (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal ^ 3 ≤
      4 * (C * (L : ℝ)) ^ 3 * (E * P 141 * N + 1) := by
    apply hcubic.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ le_rfl
    simpa only [E, mul_assoc, show 141 + 1 = 142 by norm_num] using
      mul_le_mul_of_nonneg_left (henv 141).2
      (show 0 ≤ E by dsimp only [E]; positivity)
  have hNpos : 0 < N := by
    have hh := (Metric.externalCoveringNumber_pos_iff (ε := η)).mpr
      (show ((fun x : G => (x : RMat)) '' A).Nonempty from ⟨1, ⟨1, hA1, rfl⟩⟩)
    have hh' : (0 : ℝ≥0∞) < Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) := by
      simpa only [ENat.toENNReal_zero] using ENat.toENNReal_strictMono hh
    exact ENNReal.toReal_pos hh'.ne' (ENat.toENNReal_ne_top.mpr hAfin)
  have htrace : (Metric.externalCoveringNumber η T : ℝ≥0∞).toReal ≤
      (9 * P (k + 1) * H) * (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal := by
    apply (mul_le_mul_iff_left₀ hNpos).mp
    calc
      _ ≤ 9 * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) : ℝ≥0∞).toReal * H *
            (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal := hextract
      _ ≤ 9 * (P (k + 1) * N) * H *
          (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal := by
        apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
        apply mul_le_mul_of_nonneg_right _ (by dsimp only [H]; positivity)
        exact mul_le_mul_of_nonneg_left hCbound (by norm_num)
      _ = _ := by ring
  refine ⟨hTfin, hAfin, ?_⟩
  calc
    _ ≤ ((9 * P (k + 1) * H) * (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal) ^ 3 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg htrace 3
    _ = (9 * P (k + 1) * H) ^ 3 * (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal ^ 3 :=
      mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hTbound (by dsimp only [P, H]; positivity)

end TransposeFollowup.SL2Projection
