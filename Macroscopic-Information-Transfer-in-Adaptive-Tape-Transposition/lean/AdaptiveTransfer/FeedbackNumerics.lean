import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! The finite integer optimization in the feedback product bound. This
module does not construct a block program, transcript or native monitor. -/

namespace AdaptiveTransfer

theorem feedback_product_of_window_bounds (d : ℕ) (hd : 1 ≤ d)
    (a y q : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y) (_hq : 0 ≤ q)
    (hwindow : ∀ g w : ℕ, 1 ≤ g → g ≤ d → 1 ≤ w → w ≤ d →
      (d : ℝ) ≤ a * d / g + (⌈(d : ℝ) / w⌉₊ : ℝ) * y + q * g * w) :
    (d : ℝ) / 72 ≤ max 1 q * (1 + a) * (1 + y) := by
  let g : ℕ := max 1 ⌈4 * a⌉₊
  let w : ℕ := ⌈8 * (1 + y)⌉₊
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1 : 1 ≤ g := le_max_left _ _
  have hw1 : 1 ≤ w := Nat.one_le_ceil_iff.mpr (by linarith)
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hg1)
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hw1)
  have hag : 4 * a ≤ (g : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈4 * a⌉₊))
  have hyw : 8 * (1 + y) ≤ (w : ℝ) := Nat.le_ceil _
  have hq1 : (1 : ℝ) ≤ max 1 q := le_max_left _ _
  have hqq : q ≤ max 1 q := le_max_right _ _
  have hbase : 1 + a ≤ max 1 q * (1 + a) * (1 + y) := by
    have h₁ : 1 + a ≤ max 1 q * (1 + a) := by nlinarith
    have h₂ : 0 ≤ max 1 q * (1 + a) := by positivity
    nlinarith
  have hbase' : 1 + y ≤ max 1 q * (1 + a) * (1 + y) := by
    have h₁ : 1 ≤ max 1 q * (1 + a) := by nlinarith
    nlinarith
  by_cases hgd : g ≤ d
  · by_cases hwd : w ≤ d
    · have hwdR : (w : ℝ) ≤ d := by exact_mod_cast hwd
      have hfirst : a * d / g ≤ (d : ℝ) / 4 := by
        apply (div_le_iff₀ hgpos).mpr
        nlinarith
      have hdy : (d : ℝ) / w * y ≤ (d : ℝ) / 8 := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hwpos).mpr
        nlinarith
      have hceil : (⌈(d : ℝ) / w⌉₊ : ℝ) ≤ (d : ℝ) / w + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      have hsecond : (⌈(d : ℝ) / w⌉₊ : ℝ) * y ≤ (d : ℝ) / 4 := by
        have hm := mul_le_mul_of_nonneg_right hceil hy
        nlinarith
      have hgup : (g : ℝ) ≤ 4 * (1 + a) := by
        have hc := (Nat.ceil_lt_add_one (show 0 ≤ 4 * a by positivity)).le
        simp only [g, Nat.cast_max, Nat.cast_one]
        exact max_le (by linarith) (by linarith)
      have hwup : (w : ℝ) ≤ 9 * (1 + y) := by
        have hc := (Nat.ceil_lt_add_one (show 0 ≤ 8 * (1 + y) by positivity)).le
        dsimp [w]
        linarith
      have hprod : q * (g : ℝ) * w ≤ 36 * (max 1 q * (1 + a) * (1 + y)) := by
        calc q * (g : ℝ) * w ≤ max 1 q * (4 * (1 + a)) * (9 * (1 + y)) := by
              gcongr
          _ = _ := by ring
      have hh := hwindow g w hg1 hgd hw1 hwd
      linarith
    · have hwlt : d < w := lt_of_not_ge hwd
      have hh : (d : ℝ) < 8 * (1 + y) := Nat.lt_ceil.mp hwlt
      linarith
  · have hglt : d < g := lt_of_not_ge hgd
    have hc : d < ⌈4 * a⌉₊ := by
      dsimp [g] at hglt
      omega
    have hh : (d : ℝ) < 4 * a := Nat.lt_ceil.mp hc
    linarith

/-- The product bound in the manuscript's unnormalised matrix parameters. -/
theorem feedback_product_of_matrix_windows (d b Q : ℕ) (hd : 0 < d) (hb : 0 < b)
    (cost memoryDeficit : ℝ) (hc : 0 ≤ cost) (hm : 0 ≤ memoryDeficit)
    (hwindow : ∀ g w : ℕ, 1 ≤ g → g ≤ d → 1 ≤ w → w ≤ d →
      (d*d*b : ℕ) ≤ cost / g + (⌈(d : ℝ)/w⌉₊ : ℝ) * memoryDeficit +
        (Q : ℝ) * g * w * b) :
    (d : ℝ)/72 ≤ max 1 ((Q : ℝ)/d) * (1 + cost / (d*d*b : ℕ)) *
      (1 + memoryDeficit / (d*b : ℕ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply feedback_product_of_window_bounds d hd (cost / (d*d*b : ℕ))
    (memoryDeficit / (d*b : ℕ)) ((Q : ℝ)/d) (by positivity) (by positivity) (by positivity)
  intro g w hg hgd hw hwd
  have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hh := hwindow g w hg hgd hw hwd
  have he : (cost / (d*d*b : ℕ)) * d / g +
      (⌈(d : ℝ)/w⌉₊ : ℝ) * (memoryDeficit / (d*b : ℕ)) + (Q : ℝ)/d*g*w =
      (cost / g + (⌈(d : ℝ)/w⌉₊ : ℝ) * memoryDeficit + (Q : ℝ)*g*w*b) / (d*b : ℕ) := by
    push_cast
    field_simp
  rw [he]
  apply (le_div_iff₀ (show (0 : ℝ)<(d*b : ℕ) by positivity)).mpr
  simpa only [Nat.cast_mul, mul_assoc] using hh

end AdaptiveTransfer
