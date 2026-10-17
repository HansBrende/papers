import Transpose.Tape.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Definitions: Theorem M* in level form for interval labellings

**Slots and rescaled trajectories.**
* `cellBits M = G = max(1, ⌈log₂(g+1)⌉)`: bits per work cell. (For `g ≥ 1` this is
  `⌈log₂(g+1)⌉`; for `g = 0` that value is `0`, which would leave `⌈nb/G⌉` undefined, so `G = 1`.)
* `slotLen M n = r = ⌈n b / G⌉` with `b = entryBits n`: the slot length and the block size.
* `horizon M c = c₀ = c G + 1`.
* `rescaledTraj M n t u = P_t^{(n)}(u)`: the block of work head `t` at the first step of slot
  `⌊u n⌋`, divided by `n`, on the reference input `zeroInput n` (for an oblivious machine every
  matrix input has the same trajectory).

**Levels.**
* `levelSet P c₀ p = Λ(p) = P⁻¹(p) ∩ [0, c₀]`.
* `ConsecIn Λ s s'`: `s < s'` are consecutive points of `Λ`.
* `crossPairs`: the consecutive pairs of `Λ(p)` lying off `S` with different labels.
* `levelCross P S β c₀ p = κ(p)`: their number when `Λ(p)` is finite, and `0` otherwise (for lower
  bounds on `∫ κ` this is stronger than `⊤`; infinite level sets form a null set of levels).
* `levelExcess P c₀ p = #Λ(p) − 1` (truncated at `0`): the excess multiplicity of the level `p`.

**Excised sets and labellings.**
* `FinUnionIcc S`: `S` is a finite union of closed intervals.
* `PiecewiseConstOn β S c₀`: `β` is constant on every interval of `[0, c₀] ∖ S` that avoids a fixed
  finite set. This is implied by "constant on finitely many intervals" (take the endpoints).

**Walks** (for Theorem M\* beyond machines: code-carrying diagrams and abstract walks).
* `blockTraj r n h u`: the rescaled block trajectory of a walk `h : ℕ → ℤ` (block size `r`), i.e.
  the block at the first step of slot `⌊u n⌋`, divided by `n`. `rescaledTraj` and `rescaledTrajOf`
  are its instances for machines; `TSDiagram.rescaled` for diagrams (walks frozen at `T`).
* `CutIneq n G r T D s h`: **the cut inequality of Discrete Isoperimetry** for the pair residencies
  of `k` walks: for every slot labelling with at most `m` slots per label and `M_b` label changes,
  `(n − M_b)(n − 2m) b ≤ (M_b + 1) D + M_b s + r G (3k M_b + Σ_t χ_t)`. Machines satisfy it on a trace
  class, code-carrying diagrams on the set where their code is correct (`MStarDiagram.lean`), and
  Theorem M\* holds for every family of walks satisfying it with `(D + s)/L → 0`
  (`MStarWalk.lean`).

**Long label-crossing chords** (`𝒳_t(n)`).
* `longCross R S β n η N`: the chords `(x, z)` of the residency `R` (target slot `z < N`) with gap
  `z - x ≥ η n`, both ends off `S` at macro times `x/n`, `z/n`, and different labels there; recorded
  as pairs (target slot, block), like `crossChords`.
-/

namespace Transpose.Tape

open Transpose MeasureTheory

open scoped ENNReal

/-! ## Slots and rescaled trajectories -/

/-- `G = max(1, ⌈log₂(g+1)⌉)`: bits per work cell, at least `1`. -/
def cellBits (M : TM) : ℕ := max 1 (Nat.clog 2 (M.g + 1))

/-- The slot length and block size `r = ⌈n b / G⌉` for size `n`, with `b = entryBits n`. -/
def slotLen (M : TM) (n : ℕ) : ℕ := (n * entryBits n + cellBits M - 1) / cellBits M

/-- The time horizon `c₀ = c G + 1`. -/
noncomputable def horizon (M : TM) (c : ℝ) : ℝ := c * cellBits M + 1

/-- The reference input of size `n`: the encoding of the all-zero matrix. -/
def zeroInput (n : ℕ) : List Bool := encode n (entryBits n) (fun _ _ _ => false)

/-- The rescaled trajectory `P_t^{(n)}(u)`: the block of work head `t` at the first step of slot
`⌊u n⌋` (slot length and block size `r = slotLen M n`), divided by `n`. -/
noncomputable def rescaledTraj (M : TM) (n : ℕ) (t : Fin M.k) (u : ℝ) : ℝ :=
  (curBlock (slotLen M n) (fun τ => workTraj M (zeroInput n) τ t) (⌊u * n⌋₊ * slotLen M n) : ℝ) /
    n

/-! ## Walks: rescaled block trajectories and the cut inequality -/

/-- The rescaled block trajectory of a walk `h` at size `n` (block size `r`): the block of the walk at
the first step of slot `⌊u n⌋`, divided by `n`. -/
noncomputable def blockTraj (r n : ℕ) (h : ℕ → ℤ) (u : ℝ) : ℝ :=
  (curBlock r h (⌊u * n⌋₊ * r) : ℝ) / n

/-- **The cut inequality of Discrete Isoperimetry** at one size, for the pair residencies of the `k`
walks `h t` (block size `r`, length `T`, `N = ⌈T/r⌉` slots): for every slot labelling with at most
`m` slots per label and `M_b` label changes,
`(n − M_b)(n − 2m) b ≤ (M_b + 1) D + M_b s + r G (3k M_b + Σ_t χ_t)`, where `χ_t` counts the chords
of tape `t` between slots of different labels. -/
def CutIneq {k : ℕ} (n G r T D s : ℕ) (h : Fin k → ℕ → ℤ) : Prop :=
  ∀ (lab : ℕ → ℕ) (m : ℕ),
    (∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) →
    (n - labelChanges lab (numSlots r T)) * (n - 2 * m) * entryBits n ≤
      (labelChanges lab (numSlots r T) + 1) * D + labelChanges lab (numSlots r T) * s +
        r * G * (3 * k * labelChanges lab (numSlots r T) +
          ∑ t, (crossChords (pairRes r (h t) T) lab (numSlots r T)).card)

/-! ## Level sets and `κ` -/

/-- The level set `Λ(p) = P⁻¹(p) ∩ [0, c₀]`. -/
def levelSet (P : ℝ → ℝ) (c₀ p : ℝ) : Set ℝ := {s | s ∈ Set.Icc 0 c₀ ∧ P s = p}

/-- `s < s'` are consecutive points of `Λ`: both lie in `Λ` and no point of `Λ` lies strictly
between them. -/
def ConsecIn (Λ : Set ℝ) (s s' : ℝ) : Prop :=
  s ∈ Λ ∧ s' ∈ Λ ∧ s < s' ∧ ∀ x ∈ Λ, ¬(s < x ∧ x < s')

/-- The consecutive pairs `s < s'` of `Λ(p)` with `s, s' ∉ S` and `β s ≠ β s'`. -/
def crossPairs (P : ℝ → ℝ) (S : Set ℝ) (β : ℝ → ℕ) (c₀ p : ℝ) : Set (ℝ × ℝ) :=
  {q | ConsecIn (levelSet P c₀ p) q.1 q.2 ∧ q.1 ∉ S ∧ q.2 ∉ S ∧ β q.1 ≠ β q.2}

open Classical in
/-- `κ(p)`: the number of consecutive pairs of the level set `Λ(p)` that lie off `S` and carry
different labels, when `Λ(p)` is finite; `0` when `Λ(p)` is infinite. -/
noncomputable def levelCross (P : ℝ → ℝ) (S : Set ℝ) (β : ℝ → ℕ) (c₀ p : ℝ) : ℝ≥0∞ :=
  if (levelSet P c₀ p).Finite then ((crossPairs P S β c₀ p).ncard : ℝ≥0∞) else 0

/-- The excess multiplicity of the level `p`: `#Λ(p) − 1`, truncated at `0` (and `⊤` when `Λ(p)` is
infinite, which happens only on a null set of levels for Lipschitz `P`). It bounds `κ(p)` for every
`S` and `β` (`levelCross_le_levelExcess`). -/
noncomputable def levelExcess (P : ℝ → ℝ) (c₀ p : ℝ) : ℝ≥0∞ :=
  ((levelSet P c₀ p).encard : ℝ≥0∞) - 1

/-! ## Excised sets and labellings -/

/-- `S` is a finite union of closed intervals (`S = ∅` allowed). -/
def FinUnionIcc (S : Set ℝ) : Prop := ∃ I : Finset (ℝ × ℝ), S = ⋃ x ∈ I, Set.Icc x.1 x.2

/-- `β` is constant on every interval `[u, v] ⊆ [0, c₀] ∖ S` avoiding some fixed finite set `Z`.
A labelling of `[0, c₀] ∖ S` that is constant on finitely many intervals has this property (take
`Z` = their endpoints). Values on `S` are irrelevant. -/
def PiecewiseConstOn (β : ℝ → ℕ) (S : Set ℝ) (c₀ : ℝ) : Prop :=
  ∃ Z : Finset ℝ, ∀ u v, 0 ≤ u → u ≤ v → v ≤ c₀ →
    (∀ x ∈ Set.Icc u v, x ∉ S ∧ x ∉ (Z : Set ℝ)) → β u = β v

/-! ## Long label-crossing chords -/

open Classical in
/-- `𝒳(n)`: the chords `(x, z)` of the residency `R` with target slot `z < N`, gap `z - x ≥ η n`,
both ends off `S` (at macro times `x/n` and `z/n`) and different labels there. Each is recorded as
the pair (target slot, block). -/
noncomputable def longCross (R : ℕ → Finset ℤ) (S : Set ℝ) (β : ℝ → ℕ) (n : ℕ) (η : ℝ)
    (N : ℕ) : Finset (ℕ × ℤ) :=
  (Finset.range N).biUnion (fun z =>
    ((R z).filter (fun σ => ∃ x, IsChord R σ x z ∧ η * n ≤ (z : ℝ) - x ∧
        (x : ℝ) / n ∉ S ∧ (z : ℝ) / n ∉ S ∧ β ((x : ℝ) / n) ≠ β ((z : ℝ) / n))).image
      (fun σ => (z, σ)))

end Transpose.Tape
