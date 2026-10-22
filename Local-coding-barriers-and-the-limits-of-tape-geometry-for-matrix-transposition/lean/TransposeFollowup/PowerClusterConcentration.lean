import TransposeFollowup.SL2LocalConcentration
import TransposeFollowup.ApproximatePowerCover

/-! A fixed power inherits the actual set's separated distribution.
Its global power envelopes then bound each local cluster relative to
the original set, using the existing translated-cluster theorem. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem power_cluster_coveringNumber_le_of_multiscale (n : ℕ) {A : Set G}
    {K J κ γ r : ℝ} {η : ℝ≥0}
    (hn : n ≠ 0) (hA1 : 1 ∈ A) (hA : A ⊆ matrixEntryBox 2)
    (hK : 1 ≤ K) (hκ : 0 ≤ κ) (hγ : 0 ≤ γ)
    (hη : 0 < η) (hηone : (η : ℝ) ≤ 1) (hr : (η : ℝ) ≤ r)
    (hproduct : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ (2 * n))) : ℝ≥0∞).toReal ≤
        K * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (hsize : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ n)) : ℝ≥0∞).toReal ≤
        J * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (hdistribution : ∀ ρ : ℝ, (η : ℝ) < ρ → ρ < (η : ℝ) ^ γ →
      ∃ T : Finset G, (T : Set G) ⊆ A ∧
        Metric.IsSeparated (ENNReal.ofReal ρ)
          ((fun x : G => (x : RMat)) '' (T : Set G)) ∧
        ρ ^ (-κ) ≤ (T.card : ℝ))
    (h : G) (hh : h ∈ A ^ n) :
    let B := (4 : ℝ) ^ n
    let S := {x : G | x ∈ A ^ n ∧ dist (x : RMat) (h : RMat) ≤ r}
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) : ℝ≥0∞).toReal ≤
        (8 * B + 1) ^ 4 * (8 * B ^ 2 + 4 * B + 1) ^ κ * K * J *
          (η : ℝ) ^ (-(γ * κ)) * r ^ κ *
            (Metric.externalCoveringNumber η
              ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal := by
  have hB : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hbound : ∀ x ∈ A ^ n, ∀ i j, |x i j| ≤ (4 : ℝ) ^ n := by
    intro x hx i j
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      set_pow_subset_matrixEntryBox hA n hx i j
  have hfin : Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ n)) ≠ ⊤ :=
    finite_coveringNumber_of_entry_bound (by positivity : 0 ≤ (4 : ℝ) ^ n) hη
      (by rintro x ⟨g, hg, rfl⟩; exact hbound g hg)
  have hsub : A ⊆ A ^ n := Set.subset_pow hA1 hn
  have hmono := ENNReal.toReal_mono (ENat.toENNReal_ne_top.mpr hfin)
    (ENat.toENNReal_mono (Metric.externalCoveringNumber_mono_set (ε := η)
      (Set.image_mono (f := fun x : G => (x : RMat)) hsub)))
  have hp : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' ((A ^ n) ^ 2)) : ℝ≥0∞).toReal ≤
        K * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' (A ^ n)) : ℝ≥0∞).toReal := by
    rw [← pow_mul, Nat.mul_comm n 2]
    exact hproduct.trans (mul_le_mul_of_nonneg_left hmono (by linarith))
  have hd : ∀ ρ : ℝ, (η : ℝ) < ρ → ρ < (η : ℝ) ^ γ →
      ∃ T : Finset G, (T : Set G) ⊆ A ^ n ∧
        Metric.IsSeparated (ENNReal.ofReal ρ)
          ((fun x : G => (x : RMat)) '' (T : Set G)) ∧
        ρ ^ (-κ) ≤ (T.card : ℝ) := by
    intro ρ hρ hρ'
    obtain ⟨T, hT, hsep, hcard⟩ := hdistribution ρ hρ hρ'
    exact ⟨T, hT.trans hsub, hsep, hcard⟩
  obtain ⟨hSfin, hS⟩ := cluster_coveringNumber_le_of_multiscale hB hK hκ hγ hη
    hηone hr hbound hp hd h hh
  refine ⟨hSfin, hS.trans ?_⟩
  have hcoef : 0 ≤ (8 * (4 : ℝ) ^ n + 1) ^ 4 *
      (8 * ((4 : ℝ) ^ n) ^ 2 + 4 * (4 : ℝ) ^ n + 1) ^ κ * K *
        (η : ℝ) ^ (-(γ * κ)) * r ^ κ := by
    have hK0 : 0 ≤ K := by linarith
    have hr0 : 0 ≤ r := η.coe_nonneg.trans hr
    positivity
  convert mul_le_mul_of_nonneg_left hsize hcoef using 1; ring

end TransposeFollowup.SL2Projection
