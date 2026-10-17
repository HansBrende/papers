import Mathlib
import Transpose.Statement
import Transpose.Eventually

/-!
# Definitions: runs, entry data, cut sets, blocks and residency

Definitions for the Locality Lemma, the Cut Lemma and the block-network bookkeeping, stated against
the frozen model of `Transpose/Statement.lean`.

* **Runs.** `run M w τ` is the configuration at time `τ` (before step `τ`), frozen once `M` halts.
  `transAt M w τ` is the transition taken at step `τ`. It records the new state, the input move,
  the symbol written and the move on every work tape, and the output bit appended. `outBit` is
  its output component. `HaltsAt M w T` says that steps `0, …, T-1` execute and the
  configuration at time `T` is halting.
* **Obliviousness.** `ObliviousOn M W T` holds when every input of `W` halts after exactly `T`
  steps, and any two inputs of `W` give the same input-head position, the same work-head
  positions and the same output-append decision at every time.
* **Entry data of a step set `J`.**
  * `entryPoints J`: the steps `τ ≠ 0` of `J` whose predecessor is not in `J` (the state is
    needed there; at time `0` it is the constant initial state).
  * `entryCells wp J`: the pairs `(t, τ)` with `τ ∈ J` such that the cell under work head `t` at
    time `τ` was last written at a step outside `J`.
  * Cells never written before `τ` are blank for every input, so they carry no information and
    are not counted. This makes the counting bound stronger than if they were counted.
* **Cut sets for transposition.**
  * `cutSet`: the input positions that are not read during `J` but whose output copy is
    appended during `J`.
  * `srcRows`, `snkCols` and `cutPairs`: `src(J)`, `snk(J)` and `S_J`.
* **Blocks and residency** (the Residency Lemma and the Charging Lemma).
  * `blockOf`: the block of a position; `curBlock`: the head's block.
  * `prevBlock`: `prev_τ`, which uses the most recent block change *at or before* `τ`.
  * `pairRes`: the pair residency `R_y`.
  * `touchRes`: the optional touched residency.
  * `IsChord`: chords of a residency.
  * `slotSteps`, `memBoundaries`, `chordsInto`, `entryTimes`, `labelChanges`, `crossChords`:
    counting objects for the cut bound.
-/

namespace Transpose.Tape

open Transpose

/-! ## Runs as total functions of time -/

/-- The configuration of `M` on input `w` at time `τ`, i.e. before step `τ`. Once `M` halts the
configuration stays frozen. -/
def run (M : TM) (w : List Bool) : ℕ → Config M
  | 0 => init M
  | τ + 1 => (step M w (run M w τ)).getD (run M w τ)

/-- The symbol under work head `t` at time `τ`. -/
def headSym (M : TM) (w : List Bool) (τ : ℕ) (t : Fin M.k) : Fin (M.g + 1) :=
  (run M w τ).work t ((run M w τ).workPos t)

/-- The input symbol under the input head at time `τ` (`none` outside the input). -/
def inSym (M : TM) (w : List Bool) (τ : ℕ) : Option Bool :=
  readInput w (run M w τ).inPos

/-- The transition taken at step `τ`: the value of `δ` on the configuration at time `τ`. It is
`none` exactly when the configuration at time `τ` is halting. Otherwise it records the new
state, the input-head move, for each work tape the symbol written and the head move, and the
output bit appended (if any). -/
def transAt (M : TM) (w : List Bool) (τ : ℕ) :
    Option (Fin (M.q + 1) × Dir × (Fin M.k → Fin (M.g + 1) × Dir) × Option Bool) :=
  M.δ (run M w τ).state (inSym M w τ) (headSym M w τ)

/-- The output bit appended at step `τ`, if any. -/
def outBit (M : TM) (w : List Bool) (τ : ℕ) : Option Bool :=
  (transAt M w τ).bind (fun x => x.2.2.2)

/-- The symbol written on work tape `t` at step `τ`. Once the machine has halted, "writing" leaves
the old symbol, so this is the symbol under the head at time `τ`. -/
def writtenSym (M : TM) (w : List Bool) (τ : ℕ) (t : Fin M.k) : Fin (M.g + 1) :=
  match transAt M w τ with
  | some (_, _, acts, _) => (acts t).1
  | none => headSym M w τ t

/-- `M` halts on `w` after exactly `T` steps: steps `0, …, T-1` are executed and the
configuration at time `T` is halting. -/
def HaltsAt (M : TM) (w : List Bool) (T : ℕ) : Prop :=
  (∀ τ < T, transAt M w τ ≠ none) ∧ transAt M w T = none

/-- Input-head trajectory. -/
def inTraj (M : TM) (w : List Bool) : ℕ → ℤ := fun τ => (run M w τ).inPos

/-- Work-head trajectories. -/
def workTraj (M : TM) (w : List Bool) : ℕ → Fin M.k → ℤ := fun τ => (run M w τ).workPos

/-! ## Obliviousness and transposition -/

/-- `M` is **oblivious on `W` with running time `T`**. Every input of `W` makes `M` halt after
exactly `T` steps. Any two inputs of `W` give the same input-head position, the same work-head
positions and the same output-append decision (whether a bit is appended) at every time.

Every time includes `τ = T`, so the head moves of the last step are fixed too. This is slightly
stronger than constraining only the steps `τ < T`. -/
def ObliviousOn (M : TM) (W : Set (List Bool)) (T : ℕ) : Prop :=
  (∀ w ∈ W, HaltsAt M w T) ∧
  ∀ w ∈ W, ∀ w' ∈ W, ∀ τ,
    (run M w τ).inPos = (run M w' τ).inPos ∧
    (run M w τ).workPos = (run M w' τ).workPos ∧
    (outBit M w τ).isSome = (outBit M w' τ).isSome

/-- The inputs of length `ℓ`. "Oblivious at length `ℓ`" is `ObliviousOn M (inputsOfLength ℓ) T`. -/
def inputsOfLength (ℓ : ℕ) : Set (List Bool) := {w | w.length = ℓ}

/-- The encodings of `n × n` matrices with `b`-bit entries. This is `inputsOfLength (n * n * b)`
(lemma `matrixInputs_eq`). -/
def matrixInputs (n b : ℕ) : Set (List Bool) := Set.range (encode n b)

/-- `M` transposes `n × n` matrices with `b`-bit entries: on the encoding of every matrix it halts
with the encoding of the transpose as its output. No time bound is imposed. -/
def Transposes (M : TM) (n b : ℕ) : Prop :=
  ∀ A : Matrix, ∃ t, ComputesWithin M (encode n b A) (encode n b (transpose A)) t

/-! ## Entry data of a step set -/

/-- `σ` is the last step before `τ` at which a head with trajectory `pos` was on the cell it
occupies at time `τ`. Every step writes the cell under each work head, so `σ` is the last step
before `τ` that wrote that cell. -/
def IsLastVisit (pos : ℕ → ℤ) (τ σ : ℕ) : Prop :=
  σ < τ ∧ pos σ = pos τ ∧ ∀ ρ, σ < ρ → ρ < τ → pos ρ ≠ pos τ

/-- The entry points of a step set `J`: the steps `τ ≠ 0` of `J` whose predecessor is not in `J`.

Step `0` is never an entry point. At time `0` the state is the initial state `0` for every input,
so it carries no information. Also counting `0` when `0 ∈ J` would add a slot-0 term to the
bound. -/
def entryPoints (J : Finset ℕ) : Finset ℕ :=
  J.filter (fun τ => τ ≠ 0 ∧ τ - 1 ∉ J)

open Classical in
/-- The entry cells of a step set `J` for the work-head trajectories `wp`: the pairs `(t, τ)`
with `τ ∈ J` such that the cell under work head `t` at time `τ` was last written at a step
outside `J`. Cells never written before `τ` are blank for every input and are not included. -/
noncomputable def entryCells {k : ℕ} (wp : ℕ → Fin k → ℤ) (J : Finset ℕ) :
    Finset (Fin k × ℕ) :=
  (Finset.univ ×ˢ J).filter (fun p => ∃ σ, σ ∉ J ∧ IsLastVisit (fun s => wp s p.1) p.2 σ)

/-! ## Output positions and the transposition of bit positions -/

/-- On input `w`, output position `o` (counted from `0`) is appended at a step of `J`. -/
def AppendedDuring (M : TM) (w : List Bool) (J : Finset ℕ) (o : ℕ) : Prop :=
  ∃ τ ∈ J, (outBit M w τ).isSome ∧ (run M w τ).outRev.length = o

/-- Where input bit `d` appears in the transposed output: input bit `(i n + j) b + t`
(bit `t` of entry `(i, j)`) is output bit `(j n + i) b + t` (lemma `tpos_spec`). -/
def tpos (n b d : ℕ) : ℕ := ((d / b % n) * n + d / b / n) * b + d % b

open Classical in
/-- The **cut set** of `J` (bit form), for the common trajectory of `w₀`: input positions
`d < n²b` that are read at no step of `J` but whose copy in the transposed output is appended at
a step of `J`. -/
noncomputable def cutSet (M : TM) (w₀ : List Bool) (n b : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (Finset.range (n * n * b)).filter (fun d =>
    (∀ τ ∈ J, (run M w₀ τ).inPos ≠ (d : ℤ)) ∧ AppendedDuring M w₀ J (tpos n b d))

open Classical in
/-- `src(J)`: the rows `i < n` such that some input position of row `i`, i.e. of
`[i n b, (i+1) n b)`, is read at a step of `J`. -/
noncomputable def srcRows (M : TM) (w₀ : List Bool) (n b : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => ∃ τ ∈ J,
    ((i * n * b : ℕ) : ℤ) ≤ (run M w₀ τ).inPos ∧ (run M w₀ τ).inPos < (((i + 1) * n * b : ℕ) : ℤ))

open Classical in
/-- `snk(J)`: the columns `j < n` all of whose `n b` output bits (output positions
`[j n b, (j+1) n b)`) are appended at steps of `J`. -/
noncomputable def snkCols (M : TM) (w₀ : List Bool) (n b : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun j =>
    ∀ o, j * n * b ≤ o → o < (j + 1) * n * b → AppendedDuring M w₀ J o)

/-- `S_J = {(i, j) : j ∈ snk(J), i ∉ src(J)}`. -/
noncomputable def cutPairs (M : TM) (w₀ : List Bool) (n b : ℕ) (J : Finset ℕ) :
    Finset (ℕ × ℕ) :=
  (Finset.range n \ srcRows M w₀ n b J) ×ˢ snkCols M w₀ n b J

/-! ## Blocks, slots and residency -/

/-- The block `⌊p / r⌋` of position `p`. Integer division `/` on `ℤ` is Euclidean, so this is
the floor for `r > 0`. -/
def blockOf (r : ℕ) (p : ℤ) : ℤ := p / (r : ℤ)

/-- `cur_τ`: the block of the head with trajectory `h` at time `τ`. -/
def curBlock (r : ℕ) (h : ℕ → ℤ) (τ : ℕ) : ℤ := blockOf r (h τ)

/-- A head trajectory with unit steps. Every head of the frozen model has this property. -/
def UnitSteps (h : ℕ → ℤ) : Prop := ∀ τ, |h (τ + 1) - h τ| ≤ 1

/-- The number of nonempty slots, `⌈T / r⌉`. -/
def numSlots (r T : ℕ) : ℕ := (T + r - 1) / r

/-- Slot `y`: the steps `[y r, (y+1) r) ∩ [0, T)`. -/
def slotOf (r T y : ℕ) : Finset ℕ := (Finset.Ico (y * r) (y * r + r)).filter (· < T)

/-- The most recent change of block at or before `τ`: the largest `σ ∈ [1, τ]` with
`cur_σ ≠ cur_{σ-1}`, or `0` if there is none. (`Nat.findGreatest` returns `0` when no `σ ≤ τ`
qualifies, and `0` itself never qualifies.) -/
def lastBlockChange (r : ℕ) (h : ℕ → ℤ) (τ : ℕ) : ℕ :=
  Nat.findGreatest (fun σ => 1 ≤ σ ∧ curBlock r h σ ≠ curBlock r h (σ - 1)) τ

/-- `prev_τ`: the block the head occupied immediately before its most recent change of block
**at or before** `τ`. That is `cur_{σ-1}` for the largest `σ ∈ [1, τ]` with
`cur_σ ≠ cur_{σ-1}`, or `none` if there is no such `σ`. -/
def prevBlock (r : ℕ) (h : ℕ → ℤ) (τ : ℕ) : Option ℤ :=
  if 1 ≤ lastBlockChange r h τ then some (curBlock r h (lastBlockChange r h τ - 1)) else none

/-- The resident pair at time `τ`: `{cur_τ, prev_τ}` (just `{cur_τ}` if `prev_τ` is `none`). -/
def residentPair (r : ℕ) (h : ℕ → ℤ) (τ : ℕ) : Finset ℤ :=
  insert (curBlock r h τ) (prevBlock r h τ).toFinset

/-- `R_y`, pair residency: the blocks resident at slot `y`, i.e. the union of the resident pairs
over the steps of slot `y`. -/
def pairRes (r : ℕ) (h : ℕ → ℤ) (T y : ℕ) : Finset ℤ :=
  (slotOf r T y).biUnion (residentPair r h)

/-- Touched residency (optional variant): the blocks the head occupies at some step of slot `y`. -/
def touchRes (r : ℕ) (h : ℕ → ℤ) (T y : ℕ) : Finset ℤ :=
  (slotOf r T y).image (curBlock r h)

/-- A **pair change** at step `τ`: the head enters a block outside the previous resident pair. -/
def PairChange (r : ℕ) (h : ℕ → ℤ) (τ : ℕ) : Prop :=
  1 ≤ τ ∧ curBlock r h τ ∉ residentPair r h (τ - 1)

/-- A **chord** of block `β` for a residency `R` (resident blocks per slot): `x` is the last slot
of a visit of `β` (a maximal run of slots at which `β` is resident) and `z` is the first slot of
the next visit. -/
def IsChord (R : ℕ → Finset ℤ) (β : ℤ) (x z : ℕ) : Prop :=
  x + 1 < z ∧ β ∈ R x ∧ β ∈ R z ∧ ∀ y, x < y → y < z → β ∉ R y

open Classical in
/-- The steps `< T` lying in slots of `U`: the union `J` of these slots. -/
noncomputable def slotSteps (r : ℕ) (U : Set ℕ) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun τ => τ / r ∈ U)

open Classical in
/-- `μ(J)`: the memory boundaries of the slot set `U` among the slots `< N`. These are the
slots `z ≥ 1` of `U` with `z - 1 ∉ U`.

Slot `0` is excluded: its first step carries the constant initial state, and no memory-boundary
charge falls on slot `0`. With this convention `Σ_u μ(J_u) ≤ M_b` (in fact `=`) for a partition. -/
noncomputable def memBoundaries (U : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun z => z ∈ U ∧ 1 ≤ z ∧ z - 1 ∉ U)

open Classical in
/-- For one tape, the chords of the residency `R` that enter the slot set `U` (source slot not in
`U`, target slot in `U` and `< N`), as pairs (target slot, block). `χ(J)` is the sum over the
work tapes. -/
noncomputable def chordsInto (R : ℕ → Finset ℤ) (U : Set ℕ) (N : ℕ) : Finset (ℕ × ℤ) :=
  ((Finset.range N).filter (· ∈ U)).biUnion (fun z =>
    ((R z).filter (fun β => ∃ x, x ∉ U ∧ IsChord R β x z)).image (fun β => (z, β)))

open Classical in
/-- For one tape, the external reads of the union of slots of `U`. These are the steps `τ < T`
in slots of `U` such that the cell under the head at time `τ` was last written in a slot outside
`U`. `e₂(J)` is the sum over the work tapes (lemma `entryCells_slotSteps_card`). -/
noncomputable def entryTimes (r : ℕ) (h : ℕ → ℤ) (U : Set ℕ) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun τ => τ / r ∈ U ∧ ∃ σ, σ / r ∉ U ∧ IsLastVisit h τ σ)

/-- `R` is an **admissible residency** with constant `c` for the trajectory `h` (slot length
`r`, time `T`): the head's block at every step `τ < T` is resident at the slot of `τ`, and no slot
has more than `c` resident blocks. Pair residency is admissible with `c = 3` (the Residency
Lemma); touched residency is admissible with `c = 2`. -/
def AdmissibleRes (r : ℕ) (h : ℕ → ℤ) (T : ℕ) (R : ℕ → Finset ℤ) (c : ℕ) : Prop :=
  (∀ τ < T, curBlock r h τ ∈ R (τ / r)) ∧ ∀ y, (R y).card ≤ c

/-- `M_b`: the number of slots `y ∈ [1, N)` whose label differs from that of slot `y - 1`. -/
def labelChanges (lab : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun y => 1 ≤ y ∧ lab y ≠ lab (y - 1))).card

open Classical in
/-- `χ_cross` for one tape: the chords of the residency `R` (target slot `< N`) whose two slots
carry different labels, as pairs (target slot, block). -/
noncomputable def crossChords (R : ℕ → Finset ℤ) (lab : ℕ → ℕ) (N : ℕ) : Finset (ℕ × ℤ) :=
  (Finset.range N).biUnion (fun z =>
    ((R z).filter (fun β => ∃ x, lab x ≠ lab z ∧ IsChord R β x z)).image (fun β => (z, β)))

/-- The parts of a slot labelling, as step sets: the steps `< T` whose slot has label `ℓ`. -/
noncomputable def labelPart (r : ℕ) (lab : ℕ → ℕ) (T ℓ : ℕ) : Finset ℕ :=
  slotSteps r {y | lab y = ℓ} T

end Transpose.Tape
