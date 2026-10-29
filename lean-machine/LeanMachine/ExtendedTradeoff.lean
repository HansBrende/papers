import LeanMachine.VanishingTradeoff
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.ENNReal

set_option autoImplicit false

/-! Quantitative two-term tradeoffs with unbounded nonnegative observables.
Both lower limits are extended-real; no finite upper bound is assumed. -/

namespace LeanMachine.ExtendedTradeoff

open Filter
open scoped ENNReal Topology

/-- A converging real lower bound passes directly to an extended lower limit. -/
theorem ofReal_le_liminf {a : ℕ → ℝ} {g : ℕ → ℝ≥0∞} {A : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) (h : ∀ᶠ n in atTop, ENNReal.ofReal (a n) ≤ g n) :
    ENNReal.ofReal A ≤ liminf g atTop := by
  calc
    _ = liminf (fun n => ENNReal.ofReal (a n)) atTop :=
      (ENNReal.tendsto_ofReal ha).liminf_eq.symm
    _ ≤ _ := liminf_le_liminf h

/-- A finite observable must pay the quadratic positive credit. -/
theorem finite_sq_le {μ A B C : ℝ} {g : ℝ≥0∞}
    (hμ : 0 < μ) (hB : 0 < B) (hb : 0 < A + B * g.toReal) (hg : g ≠ ⊤)
    (h : ∀ l > 0, ENNReal.ofReal ((μ - A * l - C / l) / (l * B)) ≤ g) :
    μ ^ 2 ≤ 4 * (A + B * g.toReal) * C :=
  VanishingTradeoff.sq_le (c := C) hμ hb (fun l hl => by
    have hreal := (ENNReal.ofReal_le_iff_le_toReal hg).mp (h l hl)
    have hmul := (div_le_iff₀ (mul_pos hl hB)).mp hreal
    convert add_le_add hmul (le_refl (A * l + C / l)) using 1 <;> ring)

/-- Positive credit with no reciprocal-width cost forces an infinite
observable, rather than an undefined zero-times-infinity expression. -/
theorem eq_top_of_zero_cost {μ A B : ℝ} {g : ℝ≥0∞}
    (hμ : 0 < μ) (hA : 0 < A) (hB : 0 < B)
    (h : ∀ l > 0, ENNReal.ofReal ((μ - A * l) / (l * B)) ≤ g) : g = ⊤ := by
  by_contra hg
  have hb : 0 < A + B * g.toReal :=
    add_pos_of_pos_of_nonneg hA (mul_nonneg hB.le ENNReal.toReal_nonneg)
  have hsq := finite_sq_le (C := 0) hμ hB hb hg (fun l hl => by
    simpa only [zero_div, sub_zero] using h l hl)
  have hnonpos : μ ^ 2 ≤ 0 := by simpa only [mul_zero] using hsq
  exact (not_lt_of_ge hnonpos) (pow_pos hμ 2)

/-- The positive-part density bound includes nonpositive credit. -/
theorem density_lower {μ A B C η : ℝ} {g : ℝ≥0∞}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hη : 0 < η)
    (h : ∀ l > 0, ENNReal.ofReal ((μ - A * l - C * η / l) / (l * B)) ≤ g) :
    ENNReal.ofReal (max μ 0 ^ 2 / (4 * C * B) - A * η / B) ≤
      ENNReal.ofReal η * g := by
  by_cases hg : g = ⊤
  · rw [hg, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hη).ne']
    exact le_top
  by_cases hμ : 0 < μ
  · have hb : 0 < A + B * g.toReal :=
      add_pos_of_pos_of_nonneg hA (mul_nonneg hB.le ENNReal.toReal_nonneg)
    have hsq := finite_sq_le hμ hB hb hg h
    have hreal : μ ^ 2 / (4 * C * B) - A * η / B ≤ η * g.toReal := by
      apply sub_le_iff_le_add.mpr
      apply (div_le_iff₀ (by positivity : 0 < 4 * C * B)).mpr
      have he : (η * g.toReal + A * η / B) * (4 * C * B) =
          4 * (A + B * g.toReal) * (C * η) := by field_simp; ring
      rw [he]
      exact hsq
    rw [max_eq_left hμ.le]
    calc
      _ ≤ ENNReal.ofReal (η * g.toReal) := ENNReal.ofReal_le_ofReal hreal
      _ = _ := by rw [ENNReal.ofReal_mul hη.le, ENNReal.ofReal_toReal hg]
  · have hzero : max μ 0 ^ 2 / (4 * C * B) - A * η / B ≤ 0 := by
      rw [max_eq_right (le_of_not_gt hμ)]
      simp only [zero_pow (by decide : 2 ≠ 0), zero_div, zero_sub]
      exact neg_nonpos.mpr (by positivity)
    rw [ENNReal.ofReal_eq_zero.mpr hzero]
    exact bot_le

/-- The quantitative density bound, with arbitrary infinite values and a
positive part covering nonpositive limiting credit. -/
theorem density_liminf {f η : ℕ → ℝ} {g : ℕ → ℝ≥0∞} {F A B C : ℝ}
    (hf : Tendsto f atTop (𝓝 F)) (hη : Tendsto η atTop (𝓝 0))
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hηpos : ∀ J, 0 < η J)
    (hbound : ∀ᶠ J in atTop, ∀ l > 0,
      ENNReal.ofReal ((f J - A * l - C * η J / l) / (l * B)) ≤ g J) :
    ENNReal.ofReal (max F 0 ^ 2 / (4 * C * B)) ≤
      liminf (fun J => ENNReal.ofReal (η J) * g J) atTop := by
  apply ofReal_le_liminf
    (a := fun J => max (f J) 0 ^ 2 / (4 * C * B) - A * η J / B)
  · simpa only [mul_zero, zero_div, sub_zero] using
      (((hf.max tendsto_const_nhds).pow 2).div_const (4 * C * B)).sub
        ((hη.const_mul A).div_const B)
  · exact hbound.mono fun J hJ => density_lower hA hB hC (hηpos J) hJ

/-- Normalize a positive constant in a weighted density bound. Infinite
observables are preserved by the extended-real scaling law. -/
theorem normalize_rate {g : ℕ → ℝ≥0∞} {d : ℕ → ℝ} {H Q : ℝ}
    (hH : 0 < H) (hd : ∀ J, 0 < d J)
    (h : ENNReal.ofReal Q ≤ liminf (fun J => ENNReal.ofReal (H / d J) * g J) atTop) :
    ENNReal.ofReal (Q / H) ≤ liminf (fun J => g J / ENNReal.ofReal (d J)) atTop := by
  have he : (fun J => ENNReal.ofReal (H / d J) * g J) =
      (fun J => ENNReal.ofReal H * (g J / ENNReal.ofReal (d J))) := by
    funext J
    rw [ENNReal.ofReal_div_of_pos (hd J)]
    simp only [div_eq_mul_inv, mul_left_comm, mul_comm]
  rw [he, ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top] at h
  rw [ENNReal.ofReal_div_of_pos hH]
  exact (ENNReal.div_le_iff' (ENNReal.ofReal_pos.mpr hH).ne' ENNReal.ofReal_ne_top).mpr h

/-- A positive reciprocal bound at every scale forces an infinite value. -/
theorem eq_top_of_div_le {Q : ℝ} {g : ℝ≥0∞} (hQ : 0 < Q)
    (h : ∀ H > 0, ENNReal.ofReal (Q / H) ≤ g) : g = ⊤ := by
  by_contra hg
  have hpos : 0 < g.toReal + 1 := by positivity
  have hb := (ENNReal.ofReal_le_iff_le_toReal hg).mp
    (h (Q / (g.toReal + 1)) (div_pos hQ hpos))
  have he : Q / (Q / (g.toReal + 1)) = g.toReal + 1 := by
    field_simp
  rw [he] at hb
  linarith

end LeanMachine.ExtendedTradeoff
