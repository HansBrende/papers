import LeanMachine.PowerEnvelope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

set_option autoImplicit false

/-!
# Quantitative tails of real power envelopes

Mathlib's integral comparison gives the exact power-tail bound. Pointwise
domination then controls nonnegative sequences and tails multiplied by a
factor growing more slowly than the corresponding power.
-/

namespace LeanMachine.PowerTail

open Filter MeasureTheory
open scoped BigOperators Topology

/-- The inverse-power tail is bounded by the integral from its positive cutoff. -/
theorem tsum_tail_le {p H : ℝ} (hp : 1 < p) (hH : 0 ≤ H)
    {R : ℕ} (hR : 0 < R) :
    (∑' i : ℕ, H / ((i + R : ℕ) + 1 : ℝ) ^ p) ≤
      H * (R : ℝ) ^ (1 - p) / (p - 1) := by
  have hR' : 0 < (R : ℝ) := by exact_mod_cast hR
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Ici (R : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -p ≤ 0)).mono
      (fun _ hx => hR'.trans_le hx)
  have hsum := hanti.tsum_comp_add_le_integral R
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hR')
    (fun x hx => Real.rpow_nonneg (hR'.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) hR'] at hsum
  have h := mul_le_mul_of_nonneg_left hsum hH
  rw [← tsum_mul_left] at h
  convert h using 1
  · congr 1
    funext i
    rw [Real.rpow_neg (by positivity)]
    simp [div_eq_mul_inv]
  · rw [show -p + 1 = 1 - p by ring, show 1 - p = -(p - 1) by ring]
    simp only [div_neg, neg_div, neg_neg]
    ring

/-- Domination by a real power envelope proves genuine summability. -/
theorem summable_of_le {h : ℕ → ℝ} {p H : ℝ} (hp : 1 < p)
    (h0 : ∀ i, 0 ≤ h i) (hbound : ∀ i, h i ≤ H / (i + 1 : ℝ) ^ p) :
    Summable h :=
  Summable.of_nonneg_of_le h0 hbound (PowerEnvelope.summable hp H)

/-- The integral tail estimate transfers to every nonnegative dominated sequence. -/
theorem tail_le {h : ℕ → ℝ} {p H : ℝ} (hp : 1 < p) (hH : 0 ≤ H)
    (h0 : ∀ i, 0 ≤ h i) (hbound : ∀ i, h i ≤ H / (i + 1 : ℝ) ^ p)
    {R : ℕ} (hR : 0 < R) :
    (∑' i : ℕ, h (i + R)) ≤ H * (R : ℝ) ^ (1 - p) / (p - 1) := by
  exact ((summable_nat_add_iff R).mpr (summable_of_le hp h0 hbound)).tsum_le_tsum
    (fun i => hbound (i + R))
    ((summable_nat_add_iff R).mpr (PowerEnvelope.summable hp H))
    |>.trans (tsum_tail_le hp hH hR)

/-- A factor `f = o(R^p)` makes the tail times `f / (R + shift)` vanish.
The shift may be any fixed nonnegative real number. -/
theorem scaled_tail_tendsto_zero {h f : ℕ → ℝ} {p H : ℝ}
    (hp : 1 < p) (hH : 0 ≤ H) (h0 : ∀ i, 0 ≤ h i)
    (hbound : ∀ i, h i ≤ H / (i + 1 : ℝ) ^ p)
    (hf0 : ∀ R, 0 ≤ f R)
    (hf : Tendsto (fun R : ℕ => f R / (R : ℝ) ^ p) atTop (𝓝 0))
    (shift : ℝ) (hshift : 0 ≤ shift) :
    Tendsto (fun R : ℕ => (∑' i : ℕ, h (i + R)) * f R / (R + shift))
      atTop (𝓝 0) := by
  have ht0 : ∀ R, 0 ≤ ∑' i : ℕ, h (i + R) :=
    fun R => tsum_nonneg fun i => h0 (i + R)
  apply squeeze_zero'
    (Eventually.of_forall fun R => div_nonneg (mul_nonneg (ht0 R) (hf0 R))
      (add_nonneg (Nat.cast_nonneg R) hshift))
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hR' : 0 < (R : ℝ) := by exact_mod_cast hR
    calc
      (∑' i : ℕ, h (i + R)) * f R / (R + shift) ≤
          (∑' i : ℕ, h (i + R)) * f R / R :=
        div_le_div_of_nonneg_left (mul_nonneg (ht0 R) (hf0 R)) hR' (by linarith)
      _ ≤ (H * (R : ℝ) ^ (1 - p) / (p - 1)) * f R / R :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (tail_le hp hH h0 hbound hR) (hf0 R)) hR'.le
      _ = H / (p - 1) * (f R / (R : ℝ) ^ p) := by
        rw [Real.rpow_sub hR', Real.rpow_one]
        field_simp
  · simpa only [mul_zero] using hf.const_mul (H / (p - 1))

end LeanMachine.PowerTail
