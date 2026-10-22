import TransposeFollowup.IntegerEndpoints

/-! An integer-only overlap predicate. Nonempty clipped source intervals
ensure positive image denominators, so two cross-products suffice. -/

namespace TransposeFollowup
namespace RationalMobius

set_option autoImplicit false
variable (F : RationalMobius)

theorem sourcePair_lt_iff {n : ℕ} (i : Fin n) :
    (F.leftPair i).1 * (F.rightPair i).2 < (F.rightPair i).1 * (F.leftPair i).2 ↔
      F.sourceLeft i < F.sourceRight i := by
  rw [← F.leftPair_value i, ← F.rightPair_value i]
  rw [div_lt_div_iff₀ (by exact_mod_cast F.leftPair_den_pos i)
    (by exact_mod_cast F.rightPair_den_pos i)]
  norm_cast

theorem source_bounds_of_lt {n : ℕ} (i : Fin n) (h : F.sourceLeft i < F.sourceRight i) :
    F.sourceLeft i ∈ Set.Icc F.lo F.hi ∧ F.sourceRight i ∈ Set.Icc F.lo F.hi := by
  have hl : F.lo ≤ F.sourceLeft i := le_max_left _ _
  have hr : F.sourceRight i ≤ F.hi := min_le_left _ _
  exact ⟨⟨hl, h.le.trans hr⟩, ⟨hl.trans h.le, hr⟩⟩

theorem imagePair_den_pos {n : ℕ} (i : Fin n) (h : F.sourceLeft i < F.sourceRight i) :
    0 < (F.imagePair (F.leftPair i)).2 ∧ 0 < (F.imagePair (F.rightPair i)).2 := by
  have hx := F.source_bounds_of_lt i h
  exact ⟨F.integerDenominator_pos _ _ (F.leftPair_den_pos i) (by rw [F.leftPair_value i]; exact hx.1),
    F.integerDenominator_pos _ _ (F.rightPair_den_pos i) (by rw [F.rightPair_value i]; exact hx.2)⟩

theorem evalQ_source_strict {n : ℕ} (i : Fin n) (h : F.sourceLeft i < F.sourceRight i) :
    F.evalQ (F.sourceLeft i) < F.evalQ (F.sourceRight i) := by
  have hx := F.source_bounds_of_lt i h
  have hr := F.strictMonoOn_eval (a := (F.sourceLeft i : ℝ)) (b := (F.sourceRight i : ℝ))
    ⟨by exact_mod_cast hx.1.1, by exact_mod_cast hx.1.2⟩
    ⟨by exact_mod_cast hx.2.1, by exact_mod_cast hx.2.2⟩
    (by exact_mod_cast h)
  rw [F.eval_cast, F.eval_cast] at hr
  exact_mod_cast hr

theorem overlapTest_iff_two_crossings {n : ℕ} (i j : Fin n) :
    F.overlapTest i j = true ↔ F.sourceLeft i < F.sourceRight i ∧
      F.evalQ (F.sourceLeft i) < ((j.val : ℚ) + 1) / n ∧
      (j.val : ℚ) / n < F.evalQ (F.sourceRight i) := by
  simp only [overlapTest, decide_eq_true_eq, max_lt_iff, lt_min_iff]
  constructor
  · rintro ⟨hs, ⟨_, hb⟩, ⟨ha, _⟩⟩
    exact ⟨hs, ha, hb⟩
  · rintro ⟨hs, ha, hb⟩
    have hn : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by have := j.isLt; omega)
    exact ⟨hs, ⟨F.evalQ_source_strict i hs, hb⟩, ⟨ha, (div_lt_div_iff_of_pos_right hn).mpr (by linarith)⟩⟩

theorem left_crossing_iff {n : ℕ} (i j : Fin n) (h : F.sourceLeft i < F.sourceRight i) :
    (F.imagePair (F.leftPair i)).1 * (n : ℤ) <
        ((j.val : ℤ) + 1) * (F.imagePair (F.leftPair i)).2 ↔
      F.evalQ (F.sourceLeft i) < ((j.val : ℚ) + 1) / n := by
  have hn : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by have := j.isLt; omega)
  rw [← F.leftImagePair_value i]
  rw [div_lt_div_iff₀ (by exact_mod_cast (F.imagePair_den_pos i h).1) hn]
  norm_cast

theorem right_crossing_iff {n : ℕ} (i j : Fin n) (h : F.sourceLeft i < F.sourceRight i) :
    (j.val : ℤ) * (F.imagePair (F.rightPair i)).2 <
        (F.imagePair (F.rightPair i)).1 * (n : ℤ) ↔
      (j.val : ℚ) / n < F.evalQ (F.sourceRight i) := by
  have hn : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by have := j.isLt; omega)
  rw [← F.rightImagePair_value i]
  rw [div_lt_div_iff₀ hn (by exact_mod_cast (F.imagePair_den_pos i h).2)]
  norm_cast

def integerOverlapTest {n : ℕ} (i j : Fin n) : Bool :=
  let l := F.leftPair i
  let r := F.rightPair i
  let L := F.imagePair l
  let R := F.imagePair r
  decide (l.1 * r.2 < r.1 * l.2 ∧
    L.1 * (n : ℤ) < ((j.val : ℤ) + 1) * L.2 ∧
    (j.val : ℤ) * R.2 < R.1 * (n : ℤ))

theorem integerOverlapTest_spec {n : ℕ} (i j : Fin n) :
    F.integerOverlapTest i j = true ↔ F.bounded.Overlap i j := by
  rw [← F.overlapTest_spec, F.overlapTest_iff_two_crossings]
  simp only [integerOverlapTest, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hl, hr⟩
    have h := (F.sourcePair_lt_iff i).mp hs
    exact ⟨h, (F.left_crossing_iff i j h).mp hl, (F.right_crossing_iff i j h).mp hr⟩
  · rintro ⟨h, hl, hr⟩
    exact ⟨(F.sourcePair_lt_iff i).mpr h, (F.left_crossing_iff i j h).mpr hl,
      (F.right_crossing_iff i j h).mpr hr⟩

end RationalMobius
end TransposeFollowup
