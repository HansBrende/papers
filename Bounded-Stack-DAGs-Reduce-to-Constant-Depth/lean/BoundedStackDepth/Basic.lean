import Mathlib
import BoundedNesting.Stacks

/-!
# Basic definitions: bands and the random grid

* `band M = ⌊log₂ M⌋` for `M ≥ 1`, and `band 0 = 0` (Mathlib's `Nat.log 2`).
* The grid of width `h₀ ≥ 1` with offset `r < h₀`: the *group* of a band `b` is
  `grp h₀ r b = ⌊(b + r)/h₀⌋`, and the *floor* of a group `g` is `flr h₀ r g = max(h₀ g − r, 0)`
  (truncated subtraction). The floors `flr h₀ r g`, `g ≥ 1`, are the *grid floors* of offset `r`.
-/

namespace BoundedStackDepth

/-- The band of `M`: `⌊log₂ M⌋` for `M ≥ 1`, and `0` for `M = 0`. -/
def band (M : ℕ) : ℕ := Nat.log 2 M

/-- The group of the band `b` in the grid of width `h₀` and offset `r`. -/
def grp (h₀ r b : ℕ) : ℕ := (b + r) / h₀

/-- The floor of the group `g` in the grid of width `h₀` and offset `r` (truncated at `0`). -/
def flr (h₀ r g : ℕ) : ℕ := h₀ * g - r

end BoundedStackDepth
