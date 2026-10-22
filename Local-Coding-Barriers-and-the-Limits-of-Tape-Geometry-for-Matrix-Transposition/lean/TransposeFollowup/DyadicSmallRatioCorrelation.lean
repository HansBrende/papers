import TransposeFollowup.DyadicMaskedCorrelation

/-! A small norm ratio on every dyadic band bounds the entire finite
quadratic correlation, with constants independent of the truncation. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

theorem dyadicBand_small_ratio_finite_correlation_le {c : ℕ}
    (G : Fin c → Group) (hc : 0 < c)
    (hG : ∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (D N : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : ∀ j, ‖complexAverage G ((smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume)‖ ≤
        r * ‖(smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume‖) :
    let v := ∑ j ∈ Finset.range N, (smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
    inner ℝ (complexAverage G v) v ≤
      2 * ((D : ℝ) * r * dyadicCutoffDerivativeBound 0 +
        ((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant) * ‖hf.toLp f‖ ^ 2 := by
  have h := dyadicMaskedBand_small_ratio_finite_correlation_le G hc hG
    (fun _ => True) hf hs D N hr (fun j _ => hsmall j)
  simpa only [dyadicMaskedBand, ite_true] using h

end TransposeFollowup.RealMobius
