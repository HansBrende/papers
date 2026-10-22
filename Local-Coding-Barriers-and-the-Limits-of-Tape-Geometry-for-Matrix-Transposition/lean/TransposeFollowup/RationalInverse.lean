import TransposeFollowup.RationalNeighbors

/-! An explicit rational inverse replaces the earlier classical inverse for
this map class. Applying the same bounded neighbor algorithm to it lists
all incoming neighbors as well. -/

namespace TransposeFollowup
namespace RationalMobius

open Set
set_option autoImplicit false

variable (F : RationalMobius)

theorem inverse_denom_mul {x : ℝ} (hx : x ∈ Icc (F.lo : ℝ) F.hi) :
    (-(F.c : ℝ) * F.eval x + F.a) * F.denom x = F.delta := by
  have hd : F.eval x * F.denom x = (F.a : ℝ) * x + F.b :=
    div_mul_cancel₀ _ (F.denom_pos hx).ne'
  calc
    _ = -(F.c : ℝ) * (F.eval x * F.denom x) + F.a * F.denom x := by ring
    _ = _ := by rw [hd]; dsimp [denom, delta]; push_cast; ring

theorem inverse_denom_pos {x : ℝ} (hx : x ∈ Icc (F.lo : ℝ) F.hi) :
    0 < -(F.c : ℝ) * F.eval x + F.a := by
  have hp : 0 < (-(F.c : ℝ) * F.eval x + F.a) * F.denom x :=
    (F.inverse_denom_mul hx).symm ▸ F.delta_pos
  exact (mul_pos_iff_of_pos_right (F.denom_pos hx)).mp hp

def inverse : RationalMobius where
  a := F.d
  b := -F.b
  c := -F.c
  d := F.a
  lo := F.evalQ F.lo
  hi := F.evalQ F.hi
  interval_nonempty := by
    have hh : (F.lo : ℝ) < F.hi := by exact_mod_cast F.interval_nonempty
    have hm := F.strictMonoOn_eval ⟨le_rfl, hh.le⟩ ⟨hh.le, le_rfl⟩ hh
    rw [F.eval_cast, F.eval_cast] at hm
    exact_mod_cast hm
  determinant_pos := by nlinarith [F.determinant_pos]
  denominator_lo_pos := by
    have hh : (F.lo : ℝ) ≤ F.hi := by exact_mod_cast F.interval_nonempty.le
    have hp := F.inverse_denom_pos ⟨le_rfl, hh⟩
    rw [F.eval_cast] at hp
    exact_mod_cast hp
  denominator_hi_pos := by
    have hh : (F.lo : ℝ) ≤ F.hi := by exact_mod_cast F.interval_nonempty.le
    have hp := F.inverse_denom_pos ⟨hh, le_rfl⟩
    rw [F.eval_cast] at hp
    exact_mod_cast hp

theorem inverse_eval_eval {x : ℝ} (hx : x ∈ Icc (F.lo : ℝ) F.hi) :
    F.inverse.eval (F.eval x) = x := by
  have hd : F.eval x * F.denom x = (F.a : ℝ) * x + F.b :=
    div_mul_cancel₀ _ (F.denom_pos hx).ne'
  have hn : ((F.d : ℝ) * F.eval x - F.b) * F.denom x = (F.delta : ℝ) * x := by
    calc
      _ = (F.d : ℝ) * (F.eval x * F.denom x) - F.b * F.denom x := by ring
      _ = _ := by rw [hd]; dsimp [denom, delta]; push_cast; ring
  have hden := F.inverse_denom_mul hx
  change (((F.d : ℚ) : ℝ) * F.eval x + ((-F.b : ℚ) : ℝ)) /
    (((-F.c : ℚ) : ℝ) * F.eval x + F.a) = x
  simp only [Rat.cast_neg, ← sub_eq_add_neg]
  apply (div_eq_iff (F.inverse_denom_pos hx).ne').mpr
  apply mul_right_cancel₀ (F.denom_pos hx).ne'
  calc
    _ = (F.delta : ℝ) * x := hn
    _ = (x * (-(F.c : ℝ) * F.eval x + F.a)) * F.denom x := by
      rw [mul_assoc, hden, mul_comm]

theorem image_open :
    F.eval '' Ioo (F.lo : ℝ) F.hi = Ioo (F.inverse.lo : ℝ) F.inverse.hi := by
  rw [F.continuousOn_eval.image_Ioo_of_strictMonoOn
    (by exact_mod_cast F.interval_nonempty.le) F.strictMonoOn_eval, F.eval_cast, F.eval_cast]
  rfl

theorem inverse_overlap_iff {n : ℕ} (i j : Fin n) :
    F.inverse.bounded.Overlap i j ↔ F.bounded.Overlap j i := by
  constructor
  · rintro ⟨y, hy, hyi, hyj⟩
    have him : y ∈ F.eval '' Ioo (F.lo : ℝ) F.hi := by rw [F.image_open]; exact hy
    obtain ⟨x, hx, rfl⟩ := him
    change InGridCell j (F.inverse.eval (F.eval x)) at hyj
    rw [F.inverse_eval_eval (Ioo_subset_Icc_self hx)] at hyj
    exact ⟨x, hx, hyj, hyi⟩
  · rintro ⟨x, hx, hxj, hxi⟩
    refine ⟨F.eval x, ?_, hxi, ?_⟩
    · change F.eval x ∈ Ioo (F.inverse.lo : ℝ) F.inverse.hi
      rw [← F.image_open]
      exact ⟨x, hx, rfl⟩
    · change InGridCell j (F.inverse.eval (F.eval x))
      rwa [F.inverse_eval_eval (Ioo_subset_Icc_self hx)]

def incomingNeighbors {n : ℕ} (j : Fin n) : Finset (Fin n) := F.inverse.neighbors j

theorem mem_incomingNeighbors {n : ℕ} (i j : Fin n) :
    i ∈ F.incomingNeighbors j ↔ F.bounded.Overlap i j := by
  exact (F.inverse.mem_neighbors j i).trans (F.inverse_overlap_iff j i)

theorem incomingNeighbors_card_le {n : ℕ} (j : Fin n) :
    (F.incomingNeighbors j).card ≤ F.inverse.distortion + 1 := F.inverse.neighbors_card_le j

end RationalMobius
end TransposeFollowup
