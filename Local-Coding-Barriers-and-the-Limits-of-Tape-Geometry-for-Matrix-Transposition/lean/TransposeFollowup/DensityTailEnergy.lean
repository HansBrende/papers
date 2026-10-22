import TransposeFollowup.DyadicDensityLevels

/-! Removing a tail bounded by `a` costs at most `8*a` in squared
convolution energy, with a factor two on the retained high-density part.
No finite-volume support hypothesis is needed. -/
namespace TransposeFollowup
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

theorem densityConvolution_tail_energy (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) (hm : (∫⁻ x, f x ∂σ) ≤ 1) (a : ℝ≥0∞) :
    (∫⁻ x, densityConvolution σ f f x ^ 2 ∂σ) ≤ 8 * a +
      2 * ∫⁻ x, densityConvolution σ (densityHigh f a) (densityHigh f a) x ^ 2 ∂σ := by
  let l := densityLow f a
  let h := densityHigh f a
  have hl : Measurable l := densityLow_measurable hf a
  have hh : Measurable h := densityHigh_measurable hf a
  have hlm : (∫⁻ x, l x ∂σ) ≤ 1 := (lintegral_mono (densityLow_le f a)).trans hm
  have hhm : (∫⁻ x, h x ∂σ) ≤ 1 := (lintegral_mono (densityHigh_le f a)).trans hm
  have hla : ∀ x, l x ≤ a := densityLow_le_threshold f a
  have hsum : (fun x => l x + h x) = f := funext (densityLow_add_densityHigh f a)
  let u := densityConvolution σ l f
  let v := densityConvolution σ h l
  let w := densityConvolution σ h h
  have hu : Measurable u := densityConvolution_measurable σ hl hf
  have hv : Measurable v := densityConvolution_measurable σ hh hl
  have hdecomp (x : H) : densityConvolution σ f f x = (u x + v x) + w x := by
    calc
      _ = densityConvolution σ (fun y => l y + h y) f x := by rw [hsum]
      _ = u x + densityConvolution σ h f x := densityConvolution_add_left σ hl hf x
      _ = u x + densityConvolution σ h (fun y => l y + h y) x := by rw [hsum]
      _ = u x + (v x + w x) := by rw [densityConvolution_add_right σ hh hl]
      _ = _ := (add_assoc _ _ _).symm
  have hum : (∫⁻ x, u x ∂σ) ≤ 1 := by
    rw [densityConvolution_lintegral σ hl hf]
    simpa using mul_le_mul' hlm hm
  have hvm : (∫⁻ x, v x ∂σ) ≤ 1 := by
    rw [densityConvolution_lintegral σ hh hl]
    simpa using mul_le_mul' hhm hlm
  have hua (x : H) : u x ≤ a :=
    (densityConvolution_le_of_left_le σ hf hla x).trans (by simpa using mul_le_mul' le_rfl hm)
  have hva (x : H) : v x ≤ a :=
    (densityConvolution_le_of_right_le σ hh hla x).trans (by simpa using mul_le_mul' hhm le_rfl)
  have hue : (∫⁻ x, u x ^ 2 ∂σ) ≤ a :=
    (lintegral_sq_le_bound_mul_lintegral σ hu hua).trans (by simpa using mul_le_mul' le_rfl hum)
  have hve : (∫⁻ x, v x ^ 2 ∂σ) ≤ a :=
    (lintegral_sq_le_bound_mul_lintegral σ hv hva).trans (by simpa using mul_le_mul' le_rfl hvm)
  have he : (∫⁻ x, (u x + v x) ^ 2 ∂σ) ≤ 4 * a := by
    calc
      _ ≤ 2 * ((∫⁻ x, u x ^ 2 ∂σ) + ∫⁻ x, v x ^ 2 ∂σ) := lintegral_add_sq_le σ hu
      _ ≤ 2 * (a + a) := mul_le_mul' le_rfl (add_le_add hue hve)
      _ = _ := by ring
  calc
    _ = ∫⁻ x, ((u x + v x) + w x) ^ 2 ∂σ := lintegral_congr (fun x => by rw [hdecomp])
    _ ≤ 2 * ((∫⁻ x, (u x + v x) ^ 2 ∂σ) + ∫⁻ x, w x ^ 2 ∂σ) :=
      lintegral_add_sq_le σ (hu.add hv)
    _ ≤ 2 * (4 * a + ∫⁻ x, w x ^ 2 ∂σ) := mul_le_mul' le_rfl (add_le_add he le_rfl)
    _ = _ := by dsimp [w, h]; ring

end TransposeFollowup
