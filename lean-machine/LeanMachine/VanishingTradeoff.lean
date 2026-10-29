import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! A vanishing two-term tradeoff on arbitrarily late good indices.
No square-root minimizer, positive cost coefficient, or bounded budget is needed. -/

namespace LeanMachine.VanishingTradeoff

open Filter
open scoped Topology

/-- Testing at half the positive claimed credit bounds its square. -/
theorem sq_le {f b c : ℝ} (hf : 0 < f) (hb : 0 < b)
    (h : ∀ l > 0, f ≤ l * b + c / l) : f ^ 2 ≤ 4 * b * c := by
  have h' := h (f / (2 * b)) (by positivity)
  have he : f / (2 * b) * b = f / 2 := by field_simp
  have he' : c / (f / (2 * b)) = 2 * b * c / f := by field_simp
  rw [he, he'] at h'
  have hm := (le_div_iff₀ hf).mp (show f - f / 2 ≤ 2 * b * c / f by linarith)
  nlinarith only [hm]

/-- A converging credit cannot stay positive when its two-term upper bound
has arbitrarily late small products. Only the specified common indices are used. -/
theorem limit_le_zero {f η g : ℕ → ℝ} {F A B C : ℝ} {s : Set ℕ}
    (hf : Tendsto f atTop (𝓝 F)) (hη : Tendsto η atTop (𝓝 0))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hg : ∀ J ∈ s, 0 ≤ g J)
    (hsmall : ∀ ε > 0, ∀ J₀ : ℕ, ∃ J ≥ J₀, J ∈ s ∧ η J * g J < ε)
    (hbound : ∀ J ∈ s, ∀ l > 0, f J ≤ l * (A + B * g J) + C * η J / l) :
    F ≤ 0 := by
  by_contra hF
  have hF : 0 < F := lt_of_not_ge hF
  let k := 4 * C * (A + B + 1) + 1
  have hk : 0 < k := by dsimp [k]; positivity
  let ε := F ^ 2 / (8 * k)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hid : 8 * k * ε = F ^ 2 := by dsimp [ε]; field_simp
  clear_value ε
  have hev : ∀ᶠ J in atTop, F / 2 < f J ∧ η J < ε :=
    (hf.eventually (Ioi_mem_nhds (by linarith only [hF] : F / 2 < F))).and
      (hη.eventually (Iio_mem_nhds hε))
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp hev
  obtain ⟨J, hJJ, hJs, hprod⟩ := hsmall ε hε J₀
  obtain ⟨hfJ, hηJ⟩ := hJ₀ J hJJ
  have hfpos : 0 < f J := by linarith only [hF, hfJ]
  have hbpos : 0 < A + B * g J + 1 := by
    have := mul_nonneg hB (hg J hJs)
    linarith only [hA, this]
  have hsq := sq_le hfpos hbpos (fun l hl =>
    (hbound J hJs l hl).trans (by
      calc
        _ ≤ (l * (A + B * g J) + C * η J / l) + l := le_add_of_nonneg_right hl.le
        _ = l * (A + B * g J + 1) + C * η J / l := by ring))
  have hsum : (A + 1) * η J + B * (η J * g J) ≤ (A + B + 1) * ε := by
    have h1 := mul_le_mul_of_nonneg_left hηJ.le (by linarith only [hA] : 0 ≤ A + 1)
    have h2 := mul_le_mul_of_nonneg_left hprod.le hB
    nlinarith only [h1, h2]
  have hupper := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4 * C)
  have hlow : (F / 2) ^ 2 ≤ (f J) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfJ.le 2
  dsimp only [k] at hid
  nlinarith only [hsq, hupper, hlow, hid, hε]

end LeanMachine.VanishingTradeoff
