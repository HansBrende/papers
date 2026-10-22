import TransposeFollowup.SL2TranslatedCluster

/-! The multiscale separated subsets of the actual approximate group
control local covering numbers. The normalization is the covering number
of the whole set A; no normalization by a smaller extracted set is inferred. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem cluster_coveringNumber_le_of_multiscale {A : Set G} {B K κ ε r : ℝ}
    {η : ℝ≥0} (hB : 1 ≤ B) (hK : 1 ≤ K) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hη : 0 < η) (hηone : (η : ℝ) ≤ 1) (hr : (η : ℝ) ≤ r)
    (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B)
    (hproduct : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ 2)) : ℝ≥0∞).toReal ≤
        K * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (hdistribution : ∀ ρ : ℝ, (η : ℝ) < ρ → ρ < (η : ℝ) ^ ε →
      ∃ T : Finset G, (T : Set G) ⊆ A ∧
        Metric.IsSeparated (ENNReal.ofReal ρ)
          ((fun x : G => (x : RMat)) '' (T : Set G)) ∧
        ρ ^ (-κ) ≤ (T.card : ℝ))
    (h : G) (hh : h ∈ A) :
    let S := {x : G | x ∈ A ∧ dist (x : RMat) (h : RMat) ≤ r}
    let C := 8 * B ^ 2 + 4 * B + 1
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) : ℝ≥0∞).toReal ≤
        (8 * B + 1) ^ 4 * C ^ κ * K * (η : ℝ) ^ (-(ε * κ)) * r ^ κ *
          (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal := by
  let S := {x : G | x ∈ A ∧ dist (x : RMat) (h : RMat) ≤ r}
  let C := 8 * B ^ 2 + 4 * B + 1
  let D := (8 * B + 1) ^ 4
  let nA := (Metric.externalCoveringNumber η
    ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal
  let nS := (Metric.externalCoveringNumber η
    ((fun x : G => (x : RMat)) '' S) : ℝ≥0∞).toReal
  have hB0 : 0 ≤ B := by linarith
  have hηR : 0 < (η : ℝ) := hη
  have hr0 : 0 < r := hηR.trans_le hr
  have hC1 : 1 < C := by dsimp only [C]; nlinarith [sq_nonneg B]
  have hC0 : 0 < C := zero_lt_one.trans hC1
  have hD1 : 1 ≤ D := one_le_pow₀ (by linarith : 1 ≤ 8 * B + 1)
  have hAfin : Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' A) ≠ ⊤ := by
    apply finite_coveringNumber_of_entry_bound hB0 hη
    rintro z ⟨x, hx, rfl⟩
    exact hA x hx
  have hSfin : Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' S) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hAfin
    exact Metric.externalCoveringNumber_mono_set (Set.image_mono (fun _ hx => hx.1))
  have hloss : 1 ≤ (η : ℝ) ^ (-(ε * κ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hηR hηone
      (neg_nonpos.mpr (mul_nonneg hε hκ))
  change _ ≠ ⊤ ∧ nS ≤ D * C ^ κ * K * (η : ℝ) ^ (-(ε * κ)) * r ^ κ * nA
  refine ⟨hSfin, ?_⟩
  by_cases hsmall : C * r < (η : ℝ) ^ ε
  · have hηρ : (η : ℝ) < C * r := hr.trans_lt (by nlinarith)
    obtain ⟨T, hTA, hTsep, hTcard⟩ := hdistribution (C * r) hηρ hsmall
    have hsep : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → C * r < dist (t : RMat) (u : RMat) := by
      intro t ht u hu hne
      have hne' : (t : RMat) ≠ (u : RMat) := fun he => hne (Subtype.ext he)
      have hs := hTsep (Set.mem_image_of_mem _ ht) (Set.mem_image_of_mem _ hu) hne'
      change ENNReal.ofReal (C * r) < edist (t : RMat) (u : RMat) at hs
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at hs
      exact hs
    have hscale : 8 * B * B * r + 4 * B * (η : ℝ) ≤ C * r := by
      dsimp only [C]
      nlinarith [mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 4 * B)]
    obtain ⟨_, _, hcluster⟩ := cluster_coveringNumber_mul_card_le T h hB0 hB0 hη
      hA (hA h hh) hTA hsep hscale
    have hweight : (C * r) ^ (-κ) * nS ≤ D * K * nA := by
      calc
        _ ≤ (T.card : ℝ) * nS := mul_le_mul_of_nonneg_right hTcard ENNReal.toReal_nonneg
        _ ≤ D * (Metric.externalCoveringNumber η
            ((fun x : G => (x : RMat)) '' (A ^ 2)) : ℝ≥0∞).toReal := hcluster
        _ ≤ D * (K * nA) := mul_le_mul_of_nonneg_left hproduct (by dsimp only [D]; positivity)
        _ = _ := (mul_assoc _ _ _).symm
    have hcancel : (C * r) ^ κ * (C * r) ^ (-κ) = 1 := by
      rw [← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero]
    have hlocal : nS ≤ D * C ^ κ * K * r ^ κ * nA := by
      calc
        nS = (C * r) ^ κ * ((C * r) ^ (-κ) * nS) := by rw [← mul_assoc, hcancel, one_mul]
        _ ≤ (C * r) ^ κ * (D * K * nA) :=
          mul_le_mul_of_nonneg_left hweight (by positivity)
        _ = _ := by rw [Real.mul_rpow hC0.le hr0.le]; ring
    apply hlocal.trans
    have hp : 0 ≤ D * C ^ κ * K * r ^ κ * nA := by
      have hn : 0 ≤ nA := ENNReal.toReal_nonneg
      have hK0 : 0 ≤ K := by linarith
      dsimp only [D]
      positivity
    have hl := mul_le_mul_of_nonneg_right hloss hp
    convert hl using 1 <;> ring
  · have hcap : (η : ℝ) ^ ε ≤ C * r := le_of_not_gt hsmall
    have hscale : 1 ≤ C ^ κ * (η : ℝ) ^ (-(ε * κ)) * r ^ κ := by
      calc
        1 = (η : ℝ) ^ (-(ε * κ)) * ((η : ℝ) ^ ε) ^ κ := by
          rw [← Real.rpow_mul η.coe_nonneg, ← Real.rpow_add hηR, neg_add_cancel, Real.rpow_zero]
        _ ≤ (η : ℝ) ^ (-(ε * κ)) * (C * r) ^ κ :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Real.rpow_nonneg η.coe_nonneg ε) hcap hκ) (by positivity)
        _ = _ := by rw [Real.mul_rpow hC0.le hr0.le]; ring
    have hDK : 1 ≤ D * K := by nlinarith
    have hcoef : 1 ≤ D * C ^ κ * K * (η : ℝ) ^ (-(ε * κ)) * r ^ κ := by
      have hs := mul_le_mul hDK hscale zero_le_one (by linarith : 0 ≤ D * K)
      convert hs using 1 <;> ring
    have hmono : nS ≤ nA := ENNReal.toReal_mono (ENat.toENNReal_ne_top.mpr hAfin)
      (ENat.toENNReal_mono (Metric.externalCoveringNumber_mono_set
        (Set.image_mono (fun _ hx => hx.1))))
    exact hmono.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hcoef (show 0 ≤ nA from ENNReal.toReal_nonneg))

end TransposeFollowup.SL2Projection
