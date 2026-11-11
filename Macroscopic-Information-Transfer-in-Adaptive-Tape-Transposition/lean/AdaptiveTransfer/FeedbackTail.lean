import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Numerical and finite weighted consequences of the whole-run feedback
product inequality. The native monitor/spool theorem is not assumed silently:
each success-count statement explicitly takes its product inequality, only
on nonempty sets. Empty success sets are covered by the conclusions.
-/

namespace AdaptiveTransfer.FeedbackTail

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The exact positive-part success count. Its only non-cardinality input is
the displayed whole-run product inequality; native correctness is not built
into the interface. -/
theorem success_count {P B d : ℕ} (hB : 0 < B) {c φ : ℝ} (hφ : 0 ≤ φ)
    (E : Finset (Fin P → Bool))
    (hproduct : E.Nonempty → c * d ≤
      (1 + φ / (P : ℝ)) * (1 + ((P : ℝ) - Real.logb 2 (E.card : ℝ)) / (B : ℝ))) :
    (E.card : ℝ) ≤ (2 : ℝ) ^
      ((P : ℝ) - B * max 0 (c * d / (1 + φ / (P : ℝ)) - 1)) := by
  classical
  rcases E.eq_empty_or_nonempty with hE | hE
  · rw [hE, card_empty, Nat.cast_zero]
    positivity
  have hn : (0 : ℝ) < E.card := by exact_mod_cast hE.card_pos
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hcard : E.card ≤ 2 ^ P := by simpa using card_le_univ E
  have hcard' : (E.card : ℝ) ≤ (2 : ℝ) ^ (P : ℝ) := by exact_mod_cast hcard
  have hlog : Real.logb 2 (E.card : ℝ) ≤ (P : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hn).mpr hcard'
  have hf : 0 < 1 + φ / (P : ℝ) := by positivity
  have hquot : c * d / (1 + φ / (P : ℝ)) ≤
      1 + ((P : ℝ) - Real.logb 2 (E.card : ℝ)) / (B : ℝ) := by
    apply (div_le_iff₀ hf).mpr
    simpa only [mul_comm] using hproduct hE
  have hdeficit : B * (c * d / (1 + φ / (P : ℝ)) - 1) ≤
      (P : ℝ) - Real.logb 2 (E.card : ℝ) := by
    have hh := (le_div_iff₀ hBr).mp
      (show c * d / (1 + φ / (P : ℝ)) - 1 ≤
        ((P : ℝ) - Real.logb 2 (E.card : ℝ)) / (B : ℝ) by linarith)
    nlinarith
  have hmax : B * max 0 (c * d / (1 + φ / (P : ℝ)) - 1) ≤
      (P : ℝ) - Real.logb 2 (E.card : ℝ) := by
    by_cases h : 0 ≤ c * d / (1 + φ / (P : ℝ)) - 1
    · simpa only [max_eq_right h] using hdeficit
    · rw [max_eq_left (le_of_not_ge h), mul_zero]
      linarith
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hn).mp
  linarith

/-- The explicit fixed-linear-feedback specialization, with the written
dimension threshold and rate `c/(2(1+s))`. -/
theorem fixed_linear_count {P B d : ℕ} (hPB : P = d * B) (hB : 0 < B)
    {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) (hd : 2 * (1 + s) / c ≤ (d : ℝ))
    (E : Finset (Fin P → Bool))
    (hproduct : E.Nonempty → c * d ≤
      (1 + s * (P : ℝ) / (P : ℝ)) *
        (1 + ((P : ℝ) - Real.logb 2 (E.card : ℝ)) / (B : ℝ))) :
    (E.card : ℝ) ≤ (2 : ℝ) ^ ((1 - c / (2 * (1 + s))) * (P : ℝ)) := by
  have hs1 : 0 < 1 + s := by linarith
  have hdpos : 0 < d := by
    have hh : (0 : ℝ) < d := (div_pos (by positivity) hc).trans_le hd
    exact_mod_cast hh
  have hP : 0 < P := by rw [hPB]; exact Nat.mul_pos hdpos hB
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hP)
  have hnorm : s * (P : ℝ) / (P : ℝ) = s := mul_div_cancel_right₀ s hPr
  have hcount := success_count hB (show 0 ≤ s * (P : ℝ) by positivity) E hproduct
  rw [hnorm] at hcount
  have hcd : 2 * (1 + s) ≤ c * d := by
    have hh := (div_le_iff₀ hc).mp hd
    nlinarith
  have hquot : c / (2 * (1 + s)) * d ≤ c * d / (1 + s) - 1 := by
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hs1).mpr
    have he : (c / (2 * (1 + s)) * d + 1) * (1 + s) = c * d / 2 + (1 + s) := by
      field_simp
    rw [he]
    linarith
  have hm := mul_le_mul_of_nonneg_left
    (hquot.trans (le_max_right 0 _)) (Nat.cast_nonneg (α := ℝ) B)
  have hPB' : (P : ℝ) = (d : ℝ) * B := by exact_mod_cast hPB
  exact hcount.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hPB']; nlinarith))

/-- The ambient joint success/low-feedback probability, at `α=c/4` and
the exact threshold `d≥1/α`. This is not a success-conditioned probability. -/
theorem linear_in_dimension_probability {P B d : ℕ} (hPB : P = d * B) (hB : 0 < B)
    {c : ℝ} (hc : 0 < c) (hd : 4 / c ≤ (d : ℝ))
    (E : Finset (Fin P → Bool))
    (hproduct : E.Nonempty → c * d ≤
      (1 + (c / 4 * (P : ℝ) * d) / (P : ℝ)) *
        (1 + ((P : ℝ) - Real.logb 2 (E.card : ℝ)) / (B : ℝ))) :
    (E.card : ℝ) / (2 : ℝ) ^ (P : ℝ) ≤ (2 : ℝ) ^ (-(B : ℝ)) := by
  have hdpos : 0 < d := by
    have hh : (0 : ℝ) < d := (div_pos (by norm_num) hc).trans_le hd
    exact_mod_cast hh
  have hP : 0 < P := by rw [hPB]; exact Nat.mul_pos hdpos hB
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hP)
  have hnorm : (c / 4 * (P : ℝ) * d) / (P : ℝ) = c / 4 * d := by field_simp
  have hcount := success_count hB (show 0 ≤ c / 4 * (P : ℝ) * d by positivity) E hproduct
  rw [hnorm] at hcount
  have hcd : 4 ≤ c * d := by
    have hh := (div_le_iff₀ hc).mp hd
    nlinarith
  have hf : 0 < 1 + c / 4 * (d : ℝ) := by positivity
  have hquot : 2 ≤ c * d / (1 + c / 4 * (d : ℝ)) := by
    apply (le_div_iff₀ hf).mpr
    nlinarith
  have hm : (B : ℝ) ≤ B * max 0 (c * d / (1 + c / 4 * (d : ℝ)) - 1) := by
    have ht : (1 : ℝ) ≤ c * d / (1 + c / 4 * (d : ℝ)) - 1 := by linarith
    have hh : (1 : ℝ) ≤ max 0 (c * d / (1 + c / 4 * (d : ℝ)) - 1) :=
      ht.trans (le_max_right _ _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) B)
  have hsmall : (E.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - B) :=
    hcount.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  calc
    (E.card : ℝ) / (2 : ℝ) ^ (P : ℝ) ≤
        (2 : ℝ) ^ ((P : ℝ) - B) / (2 : ℝ) ^ (P : ℝ) :=
      div_le_div_of_nonneg_right hsmall (by positivity)
    _ = (2 : ℝ) ^ (-(B : ℝ)) := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- A finite weighted span splits into short-span capacity and long-span
capacity. The same date may represent a version of an address also used by
other dates; only the finite declared weights are used. -/
theorem weighted_span_split {ι : Type*} (dates : Finset ι) (capacity span : ι → ℝ)
    {d β : ℝ} (hd : 0 ≤ d) (hβ : 0 ≤ β)
    (hcapacity : ∀ i ∈ dates, 0 ≤ capacity i) (hspan : ∀ i ∈ dates, span i ≤ d) :
    (∑ i ∈ dates, capacity i * span i) ≤
      β * d * (∑ i ∈ dates, capacity i) +
        d * ∑ i ∈ dates.filter (fun i => β * d ≤ span i), capacity i := by
  classical
  rw [sum_filter, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  by_cases hl : β * d ≤ span i
  · simp only [hl, ite_true]
    have hh := mul_le_mul_of_nonneg_left (hspan i hi) (hcapacity i hi)
    have hp : 0 ≤ β * d * capacity i := mul_nonneg (mul_nonneg hβ hd) (hcapacity i hi)
    nlinarith
  · simp only [hl, ite_false, mul_zero, add_zero]
    have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hl) (hcapacity i hi)
    nlinarith

/-- Large weighted feedback forces large total declared capacity among
dates of span at least `α d/(2u₀)`. -/
theorem long_span_capacity {ι : Type*} (dates : Finset ι) (capacity span : ι → ℝ)
    {P d u₀ α : ℝ} (hd : 0 < d) (hu : 0 < u₀) (hα : 0 ≤ α)
    (hcapacity : ∀ i ∈ dates, 0 ≤ capacity i) (hspan : ∀ i ∈ dates, span i ≤ d)
    (hW : (∑ i ∈ dates, capacity i) ≤ u₀ * P)
    (hfeedback : α * P * d < ∑ i ∈ dates, capacity i * span i) :
    α * P / 2 < ∑ i ∈ dates.filter (fun i => α / (2 * u₀) * d ≤ span i), capacity i := by
  have hs := weighted_span_split dates capacity span hd.le
    (show 0 ≤ α / (2 * u₀) by positivity) hcapacity hspan
  have hw := mul_le_mul_of_nonneg_left hW (show 0 ≤ α / (2 * u₀) * d by positivity)
  have he : α / (2 * u₀) * d * (u₀ * P) = α * P * d / 2 := by
    field_simp
  rw [he] at hw
  by_contra hn
  have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hd.le
  nlinarith

/-- For equal B-bit dated planes, the forced long-span capacity means more
than `αd/2` distinct dates. `P=dB`; spans may be bounded by d (so d-1 also
suffices), and the total declared capacity is at most `u₀P`. -/
theorem many_long_span_dates {ι : Type*} (dates : Finset ι) (span : ι → ℕ)
    {P B d : ℕ} (hPB : P = d * B) (hd : 0 < d) (hB : 0 < B)
    {u₀ α : ℝ} (hu : 0 < u₀) (hα : 0 ≤ α)
    (hspan : ∀ i ∈ dates, span i ≤ d)
    (hW : (B : ℝ) * dates.card ≤ u₀ * (P : ℝ))
    (hfeedback : α * (P : ℝ) * d < ∑ i ∈ dates, (B : ℝ) * span i) :
    α * (d : ℝ) / 2 <
      ((dates.filter fun i => α / (2 * u₀) * (d : ℝ) ≤ span i).card : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := long_span_capacity dates (fun _ => (B : ℝ)) (fun i => (span i : ℝ))
    hdR hu hα (fun _ _ => hBR.le) (fun i hi => by exact_mod_cast hspan i hi)
    (by simpa only [sum_const, nsmul_eq_mul, mul_comm] using hW) hfeedback
  simp only [sum_const, nsmul_eq_mul] at hh
  have hPB' : (P : ℝ) = (d : ℝ) * B := by exact_mod_cast hPB
  by_contra hn
  have hc := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hBR.le
  rw [hPB'] at hh
  nlinarith

end AdaptiveTransfer.FeedbackTail
