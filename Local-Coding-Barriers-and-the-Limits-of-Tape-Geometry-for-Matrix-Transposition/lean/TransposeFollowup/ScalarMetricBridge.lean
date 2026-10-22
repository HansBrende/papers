import TransposeFollowup.ExternalCoverAttainment
import OAI.MeasureTheory.Falconer.Geometry.ScalarCoverCount

/-! Compare OpenAI's scalar grid cells with Mathlib's native external
covering number, with arbitrary real centers and the same radius. -/
namespace TransposeFollowup.ScalarMetric
open Classical Set OAI.Falconer
open scoped ENNReal NNReal
set_option autoImplicit false

theorem externalCoveringNumber_le_scalarCells {δ : ℝ≥0} (hδ : 0 < δ)
    (E : Finset ℝ) :
    Metric.externalCoveringNumber δ (E : Set ℝ) ≤ (scalarCells δ E).card := by
  have hd : 0 < (δ : ℝ) := hδ
  let C := (scalarCells δ E).image (fun k : ℤ => (k : ℝ) * δ)
  have hc : Metric.IsCover δ (E : Set ℝ) (C : Set ℝ) := by
    intro x hx
    refine ⟨(⌊x / δ⌋ : ℝ) * δ, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⌊x / δ⌋, Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩
    · have hdist : dist x ((⌊x / δ⌋ : ℝ) * δ) ≤ (δ : ℝ) := by
        rw [Real.dist_eq, abs_le]
        have hlo := (le_div_iff₀ hd).mp (Int.floor_le (x / δ))
        have hhi := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (x / δ))
        constructor <;> nlinarith
      apply edist_le_coe.mpr
      exact_mod_cast hdist
  have hn : Metric.externalCoveringNumber δ (E : Set ℝ) ≤ (C.card : ℕ∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard] using hc.externalCoveringNumber_le_encard
  exact hn.trans (by exact_mod_cast (Finset.card_image_le (s := scalarCells δ E)))

theorem scalarCells_card_le_externalCoveringNumber {δ : ℝ≥0} (hδ : 0 < δ)
    (E : Finset ℝ) :
    ((scalarCells δ E).card : ℝ) ≤
      5 * (Metric.externalCoveringNumber δ (E : Set ℝ) : ℝ≥0∞).toReal := by
  have hfin : Metric.externalCoveringNumber δ (E : Set ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (externalCoveringNumber_le_scalarCells hδ E)
  obtain ⟨C, hC, hcard⟩ := Metric.exists_finset_card_eq_externalCoveringNumber hfin
  have hn := scalarCells_near_card_nat (show 0 < (δ : ℝ) from hδ) E C 1 (by
    intro x hx
    obtain ⟨c, hc, hd⟩ := hC hx
    refine ⟨c, hc, ?_⟩
    have hdist : dist x c ≤ (δ : ℝ) := by exact_mod_cast edist_le_coe.mp hd
    simpa only [Nat.cast_one, one_mul, Real.dist_eq] using hdist)
  have hbound : (scalarCells δ E).card ≤ 5 * C.card := by
    norm_num only at hn
    exact hn.trans (Nat.mul_le_mul_left 5 Finset.card_image_le)
  have he : (C.card : ℝ) =
      (Metric.externalCoveringNumber δ (E : Set ℝ) : ℝ≥0∞).toReal := by
    have hh : (C.card : ℝ≥0∞) = Metric.externalCoveringNumber δ (E : Set ℝ) := by
      exact_mod_cast hcard
    simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hh
  rw [← he]
  exact_mod_cast hbound

end TransposeFollowup.ScalarMetric
