import TransposeFollowup.GapBankBuckets
import Mathlib.Analysis.SpecificLimits.Basic

/-! Numerical consequences of the adaptive-forest budget. These internal
interfaces are instantiated by the actual protocol theorem, not assumed as
a model property. -/

namespace TransposeFollowup

open Filter
open scoped Topology
set_option autoImplicit false

theorem ceilDiv_cast_le (d M : ℕ) (hM : 0 < M) :
    (d ⌈/⌉ M : ℕ) ≤ (d : ℝ) / M + 1 := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have h := Nat.div_mul_le_self (d + M - 1) M
  have he : ((d ⌈/⌉ M) * M : ℕ) ≤ d + M :=
    h.trans (Nat.sub_le _ _)
  have hr : (d ⌈/⌉ M : ℕ) * (M : ℝ) ≤ d + M := by exact_mod_cast he
  have hh := (le_div_iff₀ hm).mpr hr
  convert hh using 1
  field_simp

/-- Dividing the actual finite budget by its payload gives the useful error
terms. The ceiling costs at most one extra row. -/
theorem adaptive_forest_normalized_budget
    (d M R sigma : ℕ) (hd : 0 < d) (hM : 0 < M)
    (W B nu Q K s D : ℝ) (hW : 0 < W) (hnu : 0 ≤ nu)
    (hbudget : (1 + 1 / (R : ℝ)) * B ≥ (d : ℝ) * W -
      W * nu * ((d ⌈/⌉ M : ℕ) + 2 * (sigma : ℝ)) - Q * ((K + 1) * s + D)) :
    (1 + 1 / (R : ℝ)) * (B / ((d : ℝ) * W)) ≥
      1 - nu * (1 / (M : ℝ) + (1 + 2 * (sigma : ℝ)) / d) -
        Q * ((K + 1) * s + D) / ((d : ℝ) * W) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hP : (0 : ℝ) < d * W := mul_pos hdR hW
  have hceil := ceilDiv_cast_le d M hM
  have herr : W * nu * ((d ⌈/⌉ M : ℕ) + 2 * (sigma : ℝ)) ≤
      W * nu * ((d : ℝ) / M + 1 + 2 * (sigma : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hW.le hnu)
  have h := hbudget.trans' (by linarith :
    (d : ℝ) * W - W * nu * ((d : ℝ) / M + 1 + 2 * (sigma : ℝ)) -
      Q * ((K + 1) * s + D) ≤ (d : ℝ) * W -
        W * nu * ((d ⌈/⌉ M : ℕ) + 2 * (sigma : ℝ)) - Q * ((K + 1) * s + D))
  have hdiv := div_le_div_of_nonneg_right h hP.le
  convert hdiv using 1 <;> field_simp
  ring

/-- One may first fix the fragmentation radius and bucket count, and only then
let the dimension grow. This avoids a choice of an unspecified slow sequence. -/
theorem adaptive_forest_near_linear
    (ratio widthError deficit : ℕ → ℝ) (nu : ℕ → ℝ) (coef : ℕ → ℕ → ℝ)
    (hwidth : Tendsto widthError atTop (𝓝 0))
    (hdeficit : Tendsto deficit atTop (𝓝 0))
    (hnu : ∀ R, 0 ≤ nu R)
    (hbudget : ∀ R : ℕ, 0 < R → ∀ M : ℕ, 0 < M →
      ∀ᶠ d in atTop,
        1 - nu R * (1 / (M : ℝ) + widthError d) - coef R M * deficit d ≤
          (1 + 1 / (R : ℝ)) * ratio d) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ d in atTop, 1 - eps ≤ ratio d := by
  intro eps heps
  obtain ⟨r, hr⟩ := exists_nat_one_div_lt (by positivity : 0 < eps / 4)
  let R := r + 1
  have hR : 0 < R := by dsimp [R]; omega
  have hRinv : 1 / (R : ℝ) < eps / 4 := by simpa [R] using hr
  have hnuR := hnu R
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt
    (by positivity : 0 < eps / (4 * (nu R + 1)))
  let M := m + 1
  have hM : 0 < M := by dsimp [M]; omega
  have hMsmall : nu R * (1 / (M : ℝ)) < eps / 4 := by
    have hpos : 0 < nu R + 1 := by linarith [hnu R]
    have hm' : 1 / (M : ℝ) < eps / (4 * (nu R + 1)) := by simpa [M] using hm
    have hmul := mul_lt_mul_of_pos_left hm' hpos
    have hunit : (0 : ℝ) < 1 / (M : ℝ) := by positivity
    have hcancel : (nu R + 1) * (eps / (4 * (nu R + 1))) = eps / 4 := by field_simp
    rw [hcancel] at hmul
    nlinarith
  have ht : Tendsto (fun d => nu R * widthError d + coef R M * deficit d) atTop (𝓝 0) := by
    simpa using (hwidth.const_mul (nu R)).add (hdeficit.const_mul (coef R M))
  have hsmall := ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < eps / 4))
  filter_upwards [hbudget R hR M hM, hsmall] with d hb hs
  by_contra hn
  have hrlt : ratio d < 1 - eps := lt_of_not_ge hn
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hi : 0 < 1 / (R : ℝ) := by positivity
  have hmul := mul_lt_mul_of_pos_left (by linarith : ratio d < 1) hi
  nlinarith

end TransposeFollowup
