import TransposeFollowup.RetainedTraceGap
import TransposeFollowup.TraceCommutingExtraction
import TransposeFollowup.SpanningCommutingExtraction

/-! Quantitatively nonnilpotent extraction from the original spanning
frame. Trace avoidance is arranged before selecting the conjugacy fiber,
so no inverse discriminant or well-conditioned eigenbasis is assumed. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem sl2_centered_det_factor (g : G) :
    ((g : RMat) - (Matrix.trace (g : RMat) / 2) • (1 : RMat)).det =
      -((Matrix.trace (g : RMat) - 2) * (Matrix.trace (g : RMat) + 2)) / 4 := by
  have hd := g.property
  simp only [Matrix.det_fin_two, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at *
  linear_combination hd

theorem trace_gap_gives_centered_det_gap (g : G) {d : ℝ}
    (hnear : dist (g : RMat) 1 ≤ 1 / 4)
    (hgap : d / 16 < |Matrix.trace (g : RMat) - 2|) :
    d / 32 < dist (g : RMat) 1 ∧
      d / 32 < |((g : RMat) - (Matrix.trace (g : RMat) / 2) • (1 : RMat)).det| := by
  have he : |Matrix.trace (g : RMat) - 2| ≤ 2 * dist (g : RMat) 1 := by
    simpa only [Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat] using
      trace_error_le_frobenius_dist (g : RMat) 1
  have hplus : 2 ≤ |Matrix.trace (g : RMat) + 2| := by
    have hh := (abs_le.mp (he.trans (mul_le_mul_of_nonneg_left hnear (by norm_num)))).1
    exact (show 2 ≤ Matrix.trace (g : RMat) + 2 by linarith only [hh]).trans (le_abs_self _)
  refine ⟨by linarith only [he, hgap], ?_⟩
  rw [sl2_centered_det_factor, abs_div, abs_neg, abs_mul, show |(4 : ℝ)| = 4 by norm_num]
  have hh := mul_le_mul_of_nonneg_left hplus (abs_nonneg (Matrix.trace (g : RMat) - 2))
  linarith only [hh, hgap]

theorem exists_quantitative_spanning_commuting_extraction :
    ∃ n₀ : ℕ, ∃ α₀ C : ℝ, 34 ≤ n₀ ∧ 0 < α₀ ∧ α₀ ≤ 1 / 2 ∧ 0 < C ∧
      ∀ {A : Set G} {α d : ℝ} {η : ℝ≥0} {p q : G},
      1 ∈ A → A⁻¹ = A → 0 < α → α ≤ α₀ → A ⊆ mobiusIdentityBall α →
      0 < d → d ≤ 1 → 0 < η → 1536 * (2 : ℝ) ^ 4 * (η : ℝ) ≤ d / 32 →
      p ∈ A ^ 34 → q ∈ A ^ 34 → p * q ∈ A ^ 34 →
      d ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det| →
      ∃ D : Set G, D ⊆ A ^ (n₀ + 1) ∧ D.Nonempty ∧ D ⊆ mobiusIdentityBall (1 / 2) ∧
        (∀ z ∈ D, d / 32 < dist (z : RMat) 1 ∧
          d / 32 < |((z : RMat) - (Matrix.trace (z : RMat) / 2) • (1 : RMat)).det|) ∧
        A * D * A⁻¹ ⊆ A ^ (n₀ + 3) ∧
        ∃ z ∈ D, ∃ v : RMat,
          let S := {x : G | x ∈ A ∧ dist ((x * z * x⁻¹ : G) : RMat) v ≤ (η : ℝ)}
          ∃ x₀ ∈ S, ∃ f : S → G,
            (∀ x : S, ∃ c t : ℝ, (f x : RMat) = scalarAffine (z : RMat) c t) ∧
            (∀ x : S, x₀⁻¹ * x ∈ A⁻¹ * A ∧
              dist ((x₀⁻¹ * x : G) : RMat) (f x : RMat) ≤ 12800 * (2 : ℝ) ^ 6 * (η : ℝ) / (d / 32)) ∧
            (∀ x y : S, Commute (f x) (f y)) ∧
            Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
            Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) ≠ ⊤ ∧
            Metric.externalCoveringNumber η (Set.range (fun x : S => (f x : RMat))) ≠ ⊤ ∧
            d ^ 11 * (Metric.externalCoveringNumber η
              ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ^ 4 ≤
              C * (9 * (Metric.externalCoveringNumber η
                ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) : ℝ≥0∞).toReal *
                  (102400 * (2 : ℝ) ^ 7 / (d / 32) + 17) ^ 4 *
                    (Metric.externalCoveringNumber η
                      (Set.range (fun x : S => (f x : RMat))) : ℝ≥0∞).toReal) ^ 3 := by
  obtain ⟨n₀, αr, C, hn₀, hαr, hαhalf, hC, hretained⟩ := exists_retained_trace_gap
  let α₀ := min αr (1 / (4 * (5 : ℝ) ^ (n₀ + 1)))
  have hα₀ : 0 < α₀ := by dsimp only [α₀]; positivity
  refine ⟨n₀, α₀, C, hn₀, hα₀, (min_le_left _ _).trans hαhalf, hC, ?_⟩
  intro A α d η p q hA1 hAi hα hαbound hA hd hd1 hη hsmall hp hq hpq hspan
  have hαr' : α ≤ αr := hαbound.trans (min_le_left _ _)
  have hαhalf' : α ≤ 1 / 2 := hαr'.trans hαhalf
  have hαone : α ≤ 1 := hαhalf'.trans (by norm_num)
  obtain ⟨R, hRA, hRn, _hRfin, h, hh, hgap, htrace⟩ :=
    hretained hA1 hAi hα hαr' hA hd hd1 hη hp hq hpq hspan
  let D := (fun x : G => h⁻¹ * x) '' R
  have hDn : D.Nonempty := hRn.image _
  have hhi : h⁻¹ ∈ A ^ n₀ := by simpa only [← inv_pow, hAi] using Set.inv_mem_inv.mpr hh
  have hDpow : D ⊆ A ^ (n₀ + 1) := by
    rintro z ⟨x, hx, rfl⟩
    rw [pow_succ]
    exact Set.mul_mem_mul hhi (hRA hx)
  have hDsmall (z : G) (hz : z ∈ D) : dist (z : RMat) 1 ≤ 1 / 4 := by
    have hs := hαbound.trans (min_le_right _ _)
    have hb := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (5 : ℝ) ^ (n₀ + 1))
    have he : (5 : ℝ) ^ (n₀ + 1) * (1 / (4 * (5 : ℝ) ^ (n₀ + 1))) = 1 / 4 := by field_simp
    rw [he] at hb
    exact (set_pow_dist_from_one_le hα hαone hA (n₀ + 1) z (hDpow hz)).trans hb
  have hDnear : D ⊆ mobiusIdentityBall (1 / 2) := fun z hz =>
    (mobiusIdentityBall_iff_frobenius_dist z (by norm_num)).mpr ((hDsmall z hz).trans_lt (by norm_num))
  have hDgap (z : G) (hz : z ∈ D) : d / 32 < dist (z : RMat) 1 ∧
      d / 32 < |((z : RMat) - (Matrix.trace (z : RMat) / 2) • (1 : RMat)).det| := by
    apply trace_gap_gives_centered_det_gap z (hDsmall z hz)
    obtain ⟨x, hx, rfl⟩ := hz
    exact hgap x hx
  have hAb := hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hDb := hDnear.trans (mobiusIdentityBall_subset_entryBox_two (by norm_num) (by norm_num))
  obtain ⟨z, hz, v, x₀, hx₀, f, hform, hclose, hcomm, hAfin, _hTrfin, hCfin, hVfin, hbound⟩ :=
    exists_trace_commuting_extraction (A := A) (D := D) (α := 1 / 2) (r := d / 32) (B := 2)
      (by norm_num) le_rfl (by positivity) (by norm_num) hη ⟨1, hA1⟩ hDn
      (fun x hx => hAb hx) (fun z hz => hDb hz) hDnear (fun z hz => (hDgap z hz).1.le) hsmall
  refine ⟨D, hDpow, hDn, hDnear, hDgap, normalized_mixed_product_subset_power hAi hRA hh,
    z, hz, v, x₀, hx₀, f, hform, hclose, hcomm, hAfin, hCfin, hVfin, ?_⟩
  let N := (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal
  let T := (Metric.externalCoveringNumber η ((fun x : G => Matrix.trace (x : RMat)) '' D) : ℝ≥0∞).toReal
  have htrace' : d ^ 11 * N ≤ C * T ^ 3 := by
    simpa only [N, T, D, Set.image_image] using htrace
  let L := 9 * (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) : ℝ≥0∞).toReal *
    (102400 * (2 : ℝ) ^ 7 / (d / 32) + 17) ^ 4 *
    (Metric.externalCoveringNumber η (Set.range (fun x => (f x : RMat))) : ℝ≥0∞).toReal
  have hbound' : T * N ≤ L := by
    dsimp only [T, N, L]
    convert hbound using 1; ring
  change d ^ 11 * N ^ 4 ≤ C * L ^ 3
  calc
    _ = (d ^ 11 * N) * N ^ 3 := by ring
    _ ≤ (C * T ^ 3) * N ^ 3 := mul_le_mul_of_nonneg_right htrace' (pow_nonneg ENNReal.toReal_nonneg _)
    _ = C * (T * N) ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hbound' 3) hC.le

end TransposeFollowup.SL2Projection
