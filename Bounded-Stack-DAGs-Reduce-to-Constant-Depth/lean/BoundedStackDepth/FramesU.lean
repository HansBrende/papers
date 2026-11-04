import BoundedStackDepth.Decomposition
import BoundedStackDepth.FrameSystem

/-!
# The frames of class U: definitions

For one walk `x` and horizon `T` (class U uses the upper hops of `x`; class L is the same construction on
`fun t => -x t`), the frames of Theorem A are read off the canonical decomposition by tops
(`Decomposition.lean`).

* `ladderHop τ z`: the ladder hop of the top `τ` at cell `z`; `ladL τ z` and `ladD τ z` are its ends,
  the last visit to `z` before `τ` and the first visit after it.
* `base τ` (the cell of the outermost ladder hop) and `exc τ` (the canonical excursion, that hop).
* For each level `w` strictly between the base and the top: the *hanging frame* `[L(w−1)+1, L(w))` and
  the *descent frame* `[D(w)+1, D(w−1))` (`hangFrame`, `descFrame`; they may be empty).
* The restart points (`restartPts`): the *passages* `D(base + 2^e)`, `2^e < height`, and the starts of the
  canonical excursions, except those that are descent-ladder times strictly inside another excursion
  (the first excursion of a descent structure restarts one step later, at its frame's start).

With the root `[0, T)` these form the frame system of class U. Its laminarity is proved
in `Excursions.lean`.
-/

namespace BoundedStackDepth

open BoundedNesting Finset

variable (x : ℕ → ℤ) (T : ℕ)

/-- The base cell of `τ`: the cell of its outermost ladder hop. -/
noncomputable def base (τ : ℕ) : ℤ := x τ - height x T τ

open Classical in
/-- The ladder hop of `τ` at cell `z` (`(0, 0)` if there is none). -/
noncomputable def ladderHop (τ : ℕ) (z : ℤ) : ℕ × ℕ :=
  if h : ∃ e ∈ ladder x T τ, x e.1 = z then h.choose else (0, 0)

/-- `L τ z`: the start of the ladder hop of `τ` at cell `z`, the last visit to `z` before `τ`. -/
noncomputable def ladL (τ : ℕ) (z : ℤ) : ℕ := (ladderHop x T τ z).1

/-- `D τ z`: the end of the ladder hop of `τ` at cell `z`, the first visit to `z` after `τ`. -/
noncomputable def ladD (τ : ℕ) (z : ℤ) : ℕ := (ladderHop x T τ z).2

/-- The canonical excursion of `τ`: its outermost ladder hop. -/
noncomputable def exc (τ : ℕ) : ℕ × ℕ := ladderHop x T τ (base x T τ)

/-- The levels of the structures of `τ`: strictly between its base and its top. -/
noncomputable def levels (τ : ℕ) : Finset ℤ := Ioo (base x T τ) (x τ)

/-- The hanging frame of `τ` at level `w`: `[L(w − 1) + 1, L(w))`. -/
noncomputable def hangFrame (τ : ℕ) (w : ℤ) : ℕ × ℕ := (ladL x T τ (w - 1) + 1, ladL x T τ w)

/-- The descent frame of `τ` at level `w`: `[D(w) + 1, D(w − 1))`. -/
noncomputable def descFrame (τ : ℕ) (w : ℤ) : ℕ × ℕ := (ladD x T τ w + 1, ladD x T τ (w - 1))

/-- The suspend frames: the hanging and descent frames of every top at every level. -/
noncomputable def suspendFrames : Finset (ℕ × ℕ) :=
  (tops x T).biUnion fun τ =>
    (levels x T τ).image (hangFrame x T τ) ∪ (levels x T τ).image (descFrame x T τ)

/-- The passages of `τ`: `D(base + 2^e)` for `2^e < height`. -/
noncomputable def passages (τ : ℕ) : Finset ℕ :=
  ((range (height x T τ)).filter (fun e => 2 ^ e < height x T τ)).image
    (fun e => ladD x T τ (base x T τ + 2 ^ e))

/-- The descent-ladder times strictly inside excursions: `D τ w` for the levels `w` of `τ`. -/
noncomputable def innerDescents : Finset ℕ := (tops x T).biUnion fun τ => (levels x T τ).image (ladD x T τ)

/-- The restart points of class U: the passages, and the excursion starts that are not inner descent
times. -/
noncomputable def restartPts : Finset ℕ :=
  (tops x T).biUnion (passages x T) ∪ ((tops x T).image (fun τ => (exc x T τ).1) \ innerDescents x T)

end BoundedStackDepth
