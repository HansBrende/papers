import BoundedStackDepth.Basic

/-!
# The break-bit display at one time

At a fixed time, every frame head `v < n` has a stack of *entries*. Entry `e` has a *window*
`[bot e, top e]` of groups: `top e` is the group of the frozen band of its parent segment, and `bot e` is
the current maximum of the head's band group and of the tops of the entries stacked inside `e`. Every entry
carries an independent bit; it is *broken* when its bit is `0`. The *seeds* are the band groups of all
heads.

The display is the least set of entries closed under three rules:
* `zero`: an entry whose window starts at `0` is displayed (a fresh entry);
* `seed`: an unbroken entry whose window contains a seed is displayed;
* `step`: an unbroken entry whose window contains the top of a displayed entry is displayed.

The shown set is `{0}` together with the seeds and the tops of the displayed entries.

The only structural fact used about stacks is the *candidate property* `OneCandidate`: for every head and
every value `y`, at most one entry of that head has `bot e ≤ y < top e`. It holds because windows along a
stack are ordered (the top of an inner entry is at most the bottom of the next outer one).
-/

namespace BoundedStackDepth

open Finset

variable {ι : Type*}

/-- The display at one time, as an inductive (least fixed point) predicate on entries. -/
inductive Disp (bot top : ι → ℕ) (unbroken : ι → Prop) (seeds : Finset ℕ) : ι → Prop
  /-- A fresh entry, whose window starts at `0`, is displayed. -/
  | zero {e : ι} : bot e = 0 → Disp bot top unbroken seeds e
  /-- An unbroken entry whose window contains a seed is displayed. -/
  | seed {e : ι} (s : ℕ) : s ∈ seeds → unbroken e → bot e ≤ s → s ≤ top e →
      Disp bot top unbroken seeds e
  /-- An unbroken entry whose window contains the top of a displayed entry is displayed. -/
  | step {e e' : ι} : Disp bot top unbroken seeds e' → unbroken e → bot e ≤ top e' → top e' ≤ top e →
      Disp bot top unbroken seeds e

/-- The candidate property: for every head and every value `y`, at most one entry of that head has
`bot e ≤ y < top e`. -/
def OneCandidate {n : ℕ} (head : ι → Fin n) (bot top : ι → ℕ) : Prop :=
  ∀ (v : Fin n) (y : ℕ) (e e' : ι), head e = v → head e' = v → bot e ≤ y → y < top e →
    bot e' ≤ y → y < top e' → e = e'

variable [Fintype ι]

open Classical in
/-- The displayed values: the seeds and the tops of the displayed entries. -/
noncomputable def dispVals (bot top : ι → ℕ) (unbroken : ι → Prop) (seeds : Finset ℕ) : Finset ℕ :=
  seeds ∪ (univ.filter (Disp bot top unbroken seeds)).image top

/-- The shown set: `0`, the seeds and the tops of the displayed entries. -/
noncomputable def shownSet (bot top : ι → ℕ) (unbroken : ι → Prop) (seeds : Finset ℕ) : Finset ℕ :=
  insert 0 (dispVals bot top unbroken seeds)

end BoundedStackDepth
