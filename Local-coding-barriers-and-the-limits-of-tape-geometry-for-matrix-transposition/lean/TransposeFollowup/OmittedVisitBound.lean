import TransposeFollowup.CompactVisitMajorant
import TransposeFollowup.ConsecutiveDeletion

/-! The exact integrated cost of omitted visits. Only the compact-visit
majorant is required to be measurable; mathlib's one-measurable-summand
integral identity avoids an additional retained-pair measurability proof. -/
namespace TransposeFollowup.AffineMotion
open Classical Set MeasureTheory Transpose.Tape
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem lintegral_levelCross_delete_le {P : ℝ → ℝ} {c₀ : ℝ}
    (hP : LipschitzOnWith 1 P (Icc 0 c₀)) (β : ℝ → ℕ) (R : Set ℝ)
    (hE : IsCompact (Icc 0 c₀ \ R)) :
    (∫⁻ p, levelCross P ∅ β c₀ p) ≤
      (∫⁻ p, ({q ∈ crossPairs P ∅ β c₀ p | q.1 ∈ R ∧ q.2 ∈ R}.ncard : ℝ≥0∞)) +
        2*volume (Icc 0 c₀ \ R) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨F,hF,hdom,hint⟩ := compact_visit_majorant hP hE Set.sdiff_subset
    (ε:=(ε : ℝ)/2) (by exact div_pos hε (by norm_num))
  let G (p : ℝ) : ℝ≥0∞ := {q ∈ crossPairs P ∅ β c₀ p | q.1 ∈ R ∧ q.2 ∈ R}.ncard
  have hcount (p : ℝ) : ((levelSet P c₀ p \ R).ncard : ℝ≥0∞) ≤ F p := by
    have he : levelSet P c₀ p \ R={x | x ∈ Icc 0 c₀ \ R ∧ P x=p} := by
      ext x
      simp only [levelSet,Set.mem_sdiff,Set.mem_ofPred_eq]
      tauto
    calc
      _ ≤ ((levelSet P c₀ p \ R).encard : ℝ≥0∞) :=
        ENat.toENNReal_mono (Set.ncard_le_encard _)
      _ ≤ _ := by rw [he]; exact hdom p
  have hp (p : ℝ) : levelCross P ∅ β c₀ p ≤ G p+2*F p :=
    (levelCross_delete_le P β c₀ p R).trans (add_le_add le_rfl (mul_le_mul' (le_refl 2) (hcount p)))
  calc
    _ ≤ ∫⁻ p, G p+2*F p := lintegral_mono hp
    _ = (∫⁻ p, G p)+2*(∫⁻ p, F p) := by
      have h2F : Measurable (fun p => (2 : ℝ≥0∞)*F p) := measurable_const.mul hF
      rw [lintegral_add_right G h2F,lintegral_const_mul _ hF]
    _ ≤ (∫⁻ p, G p)+2*(volume (Icc 0 c₀ \ R)+ENNReal.ofReal ((ε : ℝ)/2)) :=
      add_le_add le_rfl (mul_le_mul' (le_refl 2) hint)
    _ = _ := by
      rw [mul_add,← add_assoc]
      congr 1
      rw [show (2 : ℝ≥0∞)=ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      rw [show (2 : ℝ)*((ε : ℝ)/2)=(ε : ℝ) by ring,ENNReal.ofReal_coe_nnreal]

end TransposeFollowup.AffineMotion
