import BoundedStackDepth.Basic

/-!
# Hops of one walk: sides and owners

Thin wrappers around the eighth paper's walk library (`BoundedNesting`), stated for a single walk.

* `IsHop.upper_or_lower`: a long hop of a walk is an upper hop or a lower hop (`above_of_step`).
* `isOwner_hopOwner_of_upper`: for an upper hop, the earlier paper's `hopOwner` (the first time strictly
  inside at the largest distance from the cell, `hopOwner_spec`) is the owner in the sense of `IsOwner`.

Lower hops are treated as the upper hops of the reflected walk `−x` (`Decomposition.lean`).
-/

namespace BoundedStackDepth

open BoundedNesting Finset

/-- A long hop of a walk is an upper hop or a lower hop. -/
theorem IsHop.upper_or_lower {x : ℕ → ℤ} (hx : IsWalk x) {T p u : ℕ} (hh : IsHop x T p u) :
    IsUpperHop x p u ∨ IsLowerHop x p u := by
  have hne : x (p + 1) ≠ x p := hh.2.2.2 (p + 1) (mem_Ioo.mpr ⟨by omega, by have := hh.1; omega⟩)
  rcases lt_or_gt_of_ne hne with hdn | hup
  · right
    have hneg := above_of_step hx.neg (T := T) (p := p) (u := u)
      ⟨hh.1, hh.2.1, by simp [hh.2.2.1], fun t ht => by
        have := hh.2.2.2 t ht; simpa using this⟩ (by simpa using hdn)
    exact ⟨hh.1, hh.2.2.1, fun t h1 h2 => by have := hneg t h1 h2; simpa using this⟩
  · left
    exact ⟨hh.1, hh.2.2.1, above_of_step hx hh hup⟩

/-- For an upper hop, `hopOwner` is the owner in the sense of `IsOwner`. -/
theorem isOwner_hopOwner_of_upper {x : ℕ → ℤ} {p u : ℕ} (hu : IsUpperHop x p u) :
    IsOwner x p u (hopOwner x p u) := by
  obtain ⟨h1, h2, h3, h4⟩ := hopOwner_spec x hu.long
  have key : ∀ t, p < t → t < u → |x t - x p| = x t - x p := fun t ht1 ht2 =>
    abs_of_pos (by have := hu.above t ht1 ht2; linarith)
  refine ⟨h1, h2, fun t ht1 ht2 => ?_, fun t ht1 ht2 => ?_⟩
  · have := h3 t ht1 ht2
    rw [key t ht1 ht2, key _ h1 h2] at this
    linarith
  · have := h4 t ht1 ht2
    rw [key t ht1 (by omega), key _ h1 h2] at this
    linarith

end BoundedStackDepth
