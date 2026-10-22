import TransposeFollowup.RationalMobiusBounds

/-! An executable rational comparison test for the earlier real overlap
predicate. It is equivalent to strictly positive image-overlap length. -/

namespace TransposeFollowup
namespace RationalMobius

open Set MeasureTheory
set_option autoImplicit false

variable (F : RationalMobius)

def sourceLeft {n : ℕ} (i : Fin n) : ℚ := max F.lo ((i.val : ℚ) / n)

def sourceRight {n : ℕ} (i : Fin n) : ℚ := min F.hi (((i.val : ℚ) + 1) / n)

def overlapTest {n : ℕ} (i j : Fin n) : Bool :=
  decide (F.sourceLeft i < F.sourceRight i ∧
    max (F.evalQ (F.sourceLeft i)) ((j.val : ℚ) / n) <
    min (F.evalQ (F.sourceRight i)) (((j.val : ℚ) + 1) / n))

theorem sourceLeft_cast {n : ℕ} (i : Fin n) :
    (F.sourceLeft i : ℝ) = max (F.lo : ℝ) ((i.val : ℝ) / n) := by
  simp [sourceLeft]

theorem sourceRight_cast {n : ℕ} (i : Fin n) :
    (F.sourceRight i : ℝ) = min (F.hi : ℝ) (((i.val : ℝ) + 1) / n) := by
  simp [sourceRight]

theorem overlap_iff_endpoints {n : ℕ} (i j : Fin n) :
    F.bounded.Overlap i j ↔ F.sourceLeft i < F.sourceRight i ∧
      max (F.evalQ (F.sourceLeft i)) ((j.val : ℚ) / n) <
      min (F.evalQ (F.sourceRight i)) (((j.val : ℚ) + 1) / n) := by
  have hcell : ∀ (k : Fin n) (x : ℝ), InGridCell k x ↔
      x ∈ Ioo ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n) := by
    intro k x
    rw [← gridCell_eq_Ioo k]
    rfl
  change (∃ x ∈ Ioo (F.lo : ℝ) F.hi, InGridCell i x ∧ InGridCell j (F.eval x)) ↔ _
  simp_rw [hcell]
  rw [interval_overlap_iff F.continuousOn_eval F.strictMonoOn_eval,
    ← F.sourceLeft_cast i, ← F.sourceRight_cast i,
    F.eval_cast, F.eval_cast]
  have hleft : (((j.val : ℚ) / n : ℚ) : ℝ) = (j.val : ℝ) / n := by push_cast; rfl
  have hright : ((((j.val : ℚ) + 1) / n : ℚ) : ℝ) = ((j.val : ℝ) + 1) / n := by push_cast; rfl
  rw [← hleft, ← hright, ← Rat.cast_max, ← Rat.cast_min]
  norm_cast

theorem overlapTest_spec {n : ℕ} (i j : Fin n) :
    F.overlapTest i j = true ↔ F.bounded.Overlap i j := by
  simp only [overlapTest, decide_eq_true_eq]
  exact (F.overlap_iff_endpoints i j).symm

theorem overlapTest_positive {n : ℕ} (i j : Fin n) :
    F.overlapTest i j = true ↔
      0 < volume.real (clippedImage F.eval F.lo F.hi
        ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)
        ((j.val : ℝ) / n) (((j.val : ℝ) + 1) / n)) := by
  rw [clippedImage_positive_iff F.continuousOn_eval F.strictMonoOn_eval,
    clippedImage_nonempty_iff F.continuousOn_eval F.strictMonoOn_eval,
    ← F.sourceLeft_cast i, ← F.sourceRight_cast i, F.eval_cast, F.eval_cast]
  simp only [overlapTest, decide_eq_true_eq]
  have hleft : (((j.val : ℚ) / n : ℚ) : ℝ) = (j.val : ℝ) / n := by push_cast; rfl
  have hright : ((((j.val : ℚ) + 1) / n : ℚ) : ℝ) = ((j.val : ℝ) + 1) / n := by push_cast; rfl
  rw [← hleft, ← hright, ← Rat.cast_max, ← Rat.cast_min]
  norm_cast

end RationalMobius
end TransposeFollowup
