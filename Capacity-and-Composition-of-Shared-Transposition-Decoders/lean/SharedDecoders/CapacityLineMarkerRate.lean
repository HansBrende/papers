import SharedDecoders.CapacityLineMarker
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Density of the line-marker correctness set -/

namespace SharedDecoders.LineMarker

open Filter
open scoped Topology

variable {d : ℕ} [NeZero d] {A : Type*} [Zero A] [Fintype A]

theorem code_density :
    (Nat.card (Code (d := d) (A := A)) : ℝ) / (Fintype.card A : ℝ) ^ (d * d) =
      1 - 1 / (Fintype.card A : ℝ) ^ d + 1 / (Fintype.card A : ℝ) ^ (d * d) := by
  have hq : 0 < Fintype.card A := Fintype.card_pos
  have hqreal : 0 < (Fintype.card A : ℝ) := by exact_mod_cast hq
  have hqp : 1 ≤ Fintype.card A ^ d := Nat.one_le_pow _ _ (by omega)
  have hexp : d * d = d + d * (d - 1) := by
    have hd := NeZero.pos d
    nlinarith [Nat.sub_add_cancel (show 1 ≤ d by omega)]
  have hpow : (Fintype.card A : ℝ) ^ (d * d) =
      (Fintype.card A : ℝ) ^ d * (Fintype.card A : ℝ) ^ (d * (d - 1)) := by rw [hexp, pow_add]
  rw [code_card]
  push_cast [Nat.cast_sub hqp]
  rw [hpow]
  field_simp

noncomputable def positiveDensity (A : Type*) [Zero A] [Fintype A] (n : ℕ) : ℝ :=
  (Nat.card (Code (d := n + 1) (A := A)) : ℝ) /
    (Fintype.card A : ℝ) ^ ((n + 1) * (n + 1))

/-- At fixed alphabet size at least two, the actual line code has density tending to one. -/
theorem code_density_tendsto (hq : 2 ≤ Fintype.card A) :
    Tendsto (positiveDensity A) atTop (𝓝 1) := by
  have hqreal : (1 : ℝ) < Fintype.card A := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hq)
  have hqi : 0 ≤ (Fintype.card A : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi' : (Fintype.card A : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hqreal
  have h1 : Tendsto (fun n : ℕ => 1 / (Fintype.card A : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, inv_pow, one_div] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hqi hqi').comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => 1 / (Fintype.card A : ℝ) ^ ((n + 1) * (n + 1))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => by positivity) (fun n => ?_) h1
    apply div_le_div_of_nonneg_left (by norm_num) (pow_pos (by linarith) _)
    apply pow_le_pow_right₀ (by linarith)
    nlinarith
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).add h2
  change Tendsto (fun n : ℕ => (Nat.card (Code (d := n + 1) (A := A)) : ℝ) /
    (Fintype.card A : ℝ) ^ ((n + 1) * (n + 1))) atTop (𝓝 1)
  convert h.congr (fun n => (code_density (d := n + 1) (A := A)).symm) using 1
  norm_num

end SharedDecoders.LineMarker
