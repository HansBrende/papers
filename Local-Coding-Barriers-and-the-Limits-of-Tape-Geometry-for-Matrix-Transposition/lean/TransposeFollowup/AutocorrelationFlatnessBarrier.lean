import TransposeFollowup.AutocorrelationIterateCoefficient
import TransposeFollowup.DyadicDensityBarrier

/-! For each fixed number of autocorrelation iterations, sufficient
flatness contradicts the large action of the original smoothed walk.
The flatness premise is explicit and is not proved in this file. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

theorem exists_iterated_density_barrier (Nmin q : ℕ) (hq : 0 < q) {C r : ℝ} (hr : 0 < r) :
    ∃ N₀ J₀ : ℕ, 0 < N₀ ∧ Nmin ≤ N₀ ∧ 0 < J₀ ∧
      ∀ N j n : ℕ, N₀ ≤ N → J₀ ≤ j → 2 * N * n ≤ j → ∀ D : ℝ, D ^ 2 ≤ (2 : ℝ) ^ j →
        C * (64 * (16 : ℝ) ^ n) ^ (2 * q) * D / (2 : ℝ) ^ j < (r ^ n / 2) ^ (4 * q) := by
  obtain ⟨N₁, J₀, hN₁, hmin, hJ₀, hb⟩ := exists_dyadic_density_barrier Nmin
    (C := C * (64 : ℝ) ^ (2 * q) * (2 : ℝ) ^ (4 * q)) hr
  have hq' : 1 ≤ 2 * q := by omega
  refine ⟨2 * q * N₁, J₀, Nat.mul_pos (by omega) hN₁,
    hmin.trans (by simpa using Nat.mul_le_mul_right N₁ hq'), hJ₀, ?_⟩
  intro N j n hN hj hn D hD
  have hn' : 2 * N₁ * (2 * q * n) ≤ j := by
    calc
      _ = 2 * (2 * q * N₁) * n := by ring
      _ ≤ 2 * N * n := by gcongr
      _ ≤ _ := hn
  have h := hb N₁ j (2 * q * n) le_rfl hj hn' D hD
  have he : (C * (64 : ℝ) ^ (2 * q) * (2 : ℝ) ^ (4 * q)) *
      (16 : ℝ) ^ (2 * q * n) * D / (2 : ℝ) ^ j =
      (2 : ℝ) ^ (4 * q) * (C * (64 * (16 : ℝ) ^ n) ^ (2 * q) * D / (2 : ℝ) ^ j) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm n (2 * q)]
    ring
  rw [he] at h
  have ht : (2 : ℝ) ^ (4 * q) * (r ^ n / 2) ^ (4 * q) = (r ^ (2 * q * n)) ^ 2 := by
    calc
      _ = (r ^ n) ^ (4 * q) := by rw [div_pow]; field_simp
      _ = _ := by rw [← pow_mul, ← pow_mul]; congr 1; ring
  apply (mul_lt_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 2 ^ (4 * q))).mp
  apply h.trans_le
  rw [ht]
  nlinarith only [sq_nonneg (r ^ (2 * q * n))]

end TransposeFollowup

namespace TransposeFollowup.RealMobius
open Classical MeasureTheory SchwartzMap
open scoped FourierTransform ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_autocorrelationIterate_action_barrier (Nmin k : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ N₀ J₀ : ℕ, 0 < N₀ ∧ Nmin ≤ N₀ ∧ 0 < J₀ ∧
      ∀ N j n : ℕ, N₀ ≤ N → J₀ ≤ j → 2 * N * n ≤ j →
      ∀ {c : ℕ} (G : Fin c → Group), 0 < c → (∀ i, G i ∈ matrixEntryBox 2) →
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : 𝓢(ℝ, ℂ), ‖u.toLp 2 volume‖ = 1 →
      (∀ ξ : ℝ, |ξ| < (2 : ℝ) ^ j → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) →
      ∀ D : ℝ, 0 ≤ D → D ^ 2 ≤ (2 : ℝ) ^ j →
      (∀ᵐ g ∂(Measure.haar : Measure Group),
        smoothedAutocorrelationIterate (generatorWalkMeasure G n) η k g ≤ ENNReal.ofReal D) →
      ‖groupActionAverage (generatorWalkMeasure G n ∗ₘ mobiusHaarKernel η) (u.toLp 2 volume)‖ < r ^ n / 2 := by
  obtain ⟨N₀, J₀, hN₀, hmin, hJ₀, hb⟩ := exists_iterated_density_barrier Nmin (2 ^ k) (by positivity)
    (C := 2 * Real.pi * (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ)) hr
  refine ⟨N₀, J₀, hN₀, hmin, hJ₀, ?_⟩
  intro N j n hN hj hn c G hc hG η hη hηone u hu hzero D hD hDsq hbound
  have he := smoothedWalk_norm_power_le_of_autocorrelationIterate G hc hG hη hηone n k u hu hD
    (by positivity : (0 : ℝ) < 2 ^ j) hbound hzero
  have hupp : ‖groupActionAverage (generatorWalkMeasure G n ∗ₘ mobiusHaarKernel η)
      (u.toLp 2 volume)‖ ^ (4 * 2 ^ k) < (r ^ n / 2) ^ (4 * 2 ^ k) := by
    apply he.trans_lt
    simpa only [pow_mul, show (2 * (2 : ℝ)) ^ 2 = 16 by norm_num, div_eq_mul_inv] using
      hb N j n hN hj hn D hDsq
  by_contra hnot
  exact (not_lt_of_ge (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r ^ n / 2)
    (le_of_not_gt hnot) (4 * 2 ^ k))) hupp

end TransposeFollowup.RealMobius
