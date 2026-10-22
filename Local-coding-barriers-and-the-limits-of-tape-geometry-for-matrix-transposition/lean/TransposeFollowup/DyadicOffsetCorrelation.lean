import TransposeFollowup.ConcreteDyadicTransport
import TransposeFollowup.FrequencySeparatedCorrelation

/-! Actual separated-band correlations and their sum at any fixed
nonnegative dyadic offset. The bound decays geometrically with the offset. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem dyadicBand_fourier_zero_on {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (j : ℕ) :
    ∀ᵐ ξ ∂volume, ξ ∈ Icc (-(2 : ℝ) ^ j) ((2 : ℝ) ^ j) →
      (𝓕 ((smoothBand hf hs (dyadicAnnularCutoff j)
        (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume) : ComplexL2) ξ = 0 := by
  apply smoothBand_fourier_zero_on hf hs _ _ (Icc (-(2 : ℝ) ^ j) ((2 : ℝ) ^ j))
  intro ξ hξ
  exact dyadicAnnularCutoff_eq_zero_low j (abs_le.mpr hξ)

namespace RealMobius

theorem dyadicBand_offset_correlation {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (g : Group) (j d : ℕ) :
    let u := fun k => smoothBand hf hs (dyadicAnnularCutoff k) (dyadicAnnularCutoff_hasCompactSupport k)
    |inner ℝ (schwartzActionL2 g (u j)) ((u (j + d)).toLp 2 volume)| ≤
      (((2 : ℝ) ^ d)⁻¹ / (2 * Real.pi)) *
        (((2 : ℝ) ^ j)⁻¹ * ‖(schwartzDifferentialTransport g (u j)).toLp 2 volume‖) *
        ‖(u (j + d)).toLp 2 volume‖ := by
  dsimp only
  have h := schwartzActionL2_separated_correlation g
    (smoothBand hf hs (dyadicAnnularCutoff j) (dyadicAnnularCutoff_hasCompactSupport j))
    ((smoothBand hf hs (dyadicAnnularCutoff (j + d))
      (dyadicAnnularCutoff_hasCompactSupport (j + d))).toLp 2 volume)
    ((2 : ℝ) ^ (j + d)) (by positivity) (dyadicBand_fourier_zero_on hf hs (j + d))
  convert h using 1
  simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
  ring

theorem dyadicBand_offset_sum_le (s : Finset ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (g : Group) (d : ℕ) :
    let u := fun k => smoothBand hf hs (dyadicAnnularCutoff k) (dyadicAnnularCutoff_hasCompactSupport k)
    (∑ j ∈ s, |inner ℝ (schwartzActionL2 g (u j)) ((u (j + d)).toLp 2 volume)|) ≤
      (((2 : ℝ) ^ d)⁻¹ / (2 * Real.pi)) *
        (Real.sqrt (dyadicTransportConstant g) * Real.sqrt (dyadicCutoffDerivativeBound 0) *
          ‖hf.toLp f‖ ^ 2) := by
  classical
  let u := fun k => smoothBand hf hs (dyadicAnnularCutoff k) (dyadicAnnularCutoff_hasCompactSupport k)
  let a := fun j => ((2 : ℝ) ^ j)⁻¹ * ‖(schwartzDifferentialTransport g (u j)).toLp 2 volume‖
  let b := fun j => ‖(u (j + d)).toLp 2 volume‖
  have ha : (∑ j ∈ s, (a j) ^ 2) ≤ dyadicTransportConstant g * ‖hf.toLp f‖ ^ 2 := by
    simpa only [a, u, mul_pow, dyadicBandWeight] using dyadic_smoothBand_transport_energy_le s hf hs g
  have hb : (∑ j ∈ s, (b j) ^ 2) ≤ dyadicCutoffDerivativeBound 0 * ‖hf.toLp f‖ ^ 2 := by
    have h := dyadic_smoothBand_energy_le (s.image (fun j => j + d)) hf hs
    rw [Finset.sum_image] at h
    · exact h
    · intro j _ k _ he
      exact Nat.add_right_cancel he
  have hab : (∑ j ∈ s, a j * b j) ≤
      Real.sqrt (dyadicTransportConstant g) * Real.sqrt (dyadicCutoffDerivativeBound 0) *
        ‖hf.toLp f‖ ^ 2 := by
    calc
      _ ≤ Real.sqrt (∑ j ∈ s, (a j) ^ 2) * Real.sqrt (∑ j ∈ s, (b j) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s a b
      _ ≤ Real.sqrt (dyadicTransportConstant g * ‖hf.toLp f‖ ^ 2) *
          Real.sqrt (dyadicCutoffDerivativeBound 0 * ‖hf.toLp f‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [Real.sqrt_mul (dyadicTransportConstant_nonneg g),
          Real.sqrt_mul (dyadicCutoffDerivativeBound_nonneg 0), Real.sqrt_sq (norm_nonneg _)]
        ring
  change (∑ j ∈ s, |inner ℝ (schwartzActionL2 g (u j)) ((u (j + d)).toLp 2 volume)|) ≤ _
  calc
    _ ≤ ∑ j ∈ s, (((2 : ℝ) ^ d)⁻¹ / (2 * Real.pi)) * a j * b j :=
      Finset.sum_le_sum (fun j _ => dyadicBand_offset_correlation hf hs g j d)
    _ = (((2 : ℝ) ^ d)⁻¹ / (2 * Real.pi)) * (∑ j ∈ s, a j * b j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hab (by positivity)

end RealMobius
end TransposeFollowup
