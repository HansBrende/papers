import BoundedNesting.OneWalk
import Mathlib.Tactic

/-! The exact first-read geometry behind sparse imported symbols. -/

namespace AdaptiveTransfer

open BoundedNesting Finset

/-- An earlier version feeding the first run-read outside the entry window is
an actual consecutive return, and the entry time witnesses its excursion. -/
theorem outside_first_read_is_long_return {y : ℕ → ℤ} {T a p t H : ℕ}
    (hat : a ≤ t) (htT : t < T) (hpt : p < t) (hsame : y p = y t)
    (hfirst : ∀ u, a ≤ u → u < t → y u ≠ y t)
    (hlast : ∀ u, p < u → u < t → y u ≠ y t)
    (hfar : (H : ℤ) < |y t - y a|) :
    p < a ∧ a < t ∧ IsHop y T p t ∧ (H : ℤ) < |y a - y p| := by
  have hat' : a < t := by
    by_contra hn
    have heq : a = t := by omega
    subst a
    simp at hfar
    omega
  have hpa : p < a := by
    by_contra hn
    exact hfirst p (by omega) hpt hsame
  refine ⟨hpa, hat', ⟨by omega, htT, hsame.symm, ?_⟩, ?_⟩
  · intro u hu
    obtain ⟨hpu, hut⟩ := mem_Ioo.mp hu
    simpa [hsame] using hlast u hpu hut
  · simpa [hsame, abs_sub_comm] using hfar

/-- At a handoff, one ordinary old-position write can cross a sparse threshold
by at most one cell; the new snapshot is still in the enlarged sparse domain. -/
theorem promoted_weight_eq {before after m : ℕ}
    (hbefore : before ≤ m) (hone : after ≤ before + 1) (hdense : m < after) :
    after = m + 1 := by omega

end AdaptiveTransfer
