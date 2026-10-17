import Transpose.Tape.DefsTrace

/-!
# The coding core: `CE_TM` and the Tape Coding Conjecture

The conjectures are statements about the graph class of block images of TM time–space networks,
with arbitrary causal codes. The Tape Coding Conjecture is the robust form.

**Time–space diagrams.** `TSDiagram k` records:
* a length `T`;
* `k` work-head walks and an input-head walk;
* an output schedule: `out τ` is the number of output bits before step `τ`.

`Valid L` requires that every walk starts at cell `0` and moves by unit steps, and that the output
schedule starts at `0`, grows by at most one bit per step and equals `L` from time `T` on. No
transition function appears: the conjecture is about head motions and codes only.

**The block network** (block size `r`) of a diagram:
* nodes: the slots `y < ⌈T/r⌉`, in their causal order (the spine);
* `memEdges`: the edges `y → y+1`;
* `chordEdges`: an edge `x → z` whenever some work tape has a chord `x → z` of its pair residency,
  i.e. a block resident at slots `x` and `z` and at no slot in between;
* `rowsAt y`: the input rows the input walk touches during slot `y` (multi-homed sources);
* `outNode o`: the slot during which output position `o` is produced (the sink of `o`).

**Codes.** In a `NetCode`:
* edge `e = (u, v)` carries a natural number computed by `enc e` from the values on the edges into
  `u` and the input visible at `u` (the bits of the rows attached at `u`);
* output position `o` is computed by `dec o` from the same data at node `outNode o`;
* `inVals` evaluates the code along the spine.

A code `Solves` complete exchange on `F` within capacities `cap` if, for every input of `F`, every
edge value is `< 2^{cap e}` and every output bit is the transposed input bit. `CapProfile` bounds the
capacities by the block profile of the block network, a block being `r G` bits:
* a memory edge `y → y+1` carries at most the blocks resident at slot `y`, over all tapes (at most
  `3k`), and nothing else;
* a chord edge carries one block per work tape having that chord (`chordTapes`).

This is at most the profile of `3k` blocks plus `O(1)` bits at every `k`. The variants with a
uniform profile of `m(k) ≥ 3k` blocks per memory edge (`RobustNoCode_TM_with`), or with
`s(k, n) ≤ C(k) n w` (for `n ≥ 1`) extra bits per memory edge (`RobustNoCode_TM_bits`), are equivalent
(`Transpose/Tape/Statements/Coding.lean`); the profile of `3k` blocks plus `O(1)` bits lies between
`m(k) = 3k` and `m(k) = 3k + 1` for large `n`. `profileCap` gives the profile's capacities
explicitly; the no-code targets are stated at these capacities.
The simulation of a machine's run also carries the state on its memory edges, and, on a trace class
of an adaptive machine, the head positions (`O(log n)` bits); for an oblivious machine the positions
are fixed. The reduction adds one stationary tape, whose resident block carries them.

**Distances and flows.**
* `ball` and `netDist`: undirected hop distance.
* `rowDist d`: the distance from the nodes holding the row of input bit `d` to the sink of its
  transposed position (`0` when the row has no source node).
* `Routing` and `RoutesAt`: a fractional multicommodity flow with one commodity per input bit, routing
  `rate` units along walks within the edge capacities. Only bits whose row has a source node are
  commodities; a row with no source node carries no demand.

**The conjectures.** These are the `ε`-forms of "for some `γ(n) = o(log n)`", with `log n` measured
by `w = entryBits n`. The constants are `k` (tapes), `G` (bits per cell, block size `r = ⌈n w/G⌉`),
`c` (time bound `T ≤ c L`), `C` (co-entropy bound `C n w`) and `ε`.
* `RobustCE_TM`: for every choice of the constants and all large `n`, consider a valid `k`-tape
  diagram of length `≤ c L` whose block network carries a causal code solving complete exchange on a
  set `F` of inputs of co-entropy `≤ C n w`, within capacities `cap` in the block profile. Then the
  demand is fractionally routable at rate `1/(ε w)` within `cap`. That is, the coding rate is at most
  `ε w` times the multicommodity-flow rate.
* `RobustCE_TM_dist`: the same, with the conclusion `Σ_d rowDist d ≤ ε w Σ_e cap e`, i.e. the flow
  rate replaced by its volume bound.
* `RobustNoCode_TM`: for all large `n`, no such code exists (at the profile capacities `profileCap`).
* `RobustNoCode_TM_bits s`: the same with `s k n` extra bits on every memory edge.
* `CE_TM`, `CE_TM_dist` and `NoCode_TM`: independent uniform sources (`F` = all inputs).
* The infinitely-often forms `RobustNoCode_TM_io`, `RobustCE_TM_io`, `RobustCE_TM_dist_io` and
  `NoCode_TM_io`: "for infinitely many `n`" in place of "for all large `n`".
* Robust versus plain: `NoCode_TM_coent m` (no code at co-entropy `≤ m(n)`, a ladder from
  `NoCode_TM` at `m = 0` to `RobustNoCode_TM` at `m = C n w`), `NoCode_TM_hintBits s` and
  `NoCode_TM_hint` (no code even when every node also sees a hint that is any function of the whole
  input, supplied by an oracle coordinator; equivalent to `RobustNoCode_TM`), and `NoCode_TM_bits s`
  (plain, with a side channel of `s` bits per memory edge whose contents the code computes itself;
  equivalent to `NoCode_TM`).
* `NoCode_TM_coent_io m` (co-entropy `m`, infinitely many `n`), `NoCode_TM_coent_end m` (diagrams
  with the output in the last `L` steps) and `NoCode_TM_coent_end_io m` (both restrictions).
* `RobustCE_TM_gamma` and `RobustCE_TM_gamma_per` (the γ-form, one `γ` for all constants or per
  constants), `RobustCE_TM_lin` (the flow form at co-entropy `C n`).

The three robust forms, the flow, distance and no-code forms of the Tape Coding Conjecture, are
equivalent (`Transpose/Tape/Statements/Coding.lean`), and so are the three plain forms. A code
solving complete exchange has rate `1`. In a block network almost every distance is `Ω(log n)` and the
capacities sum to `O(L)`, so the volume bound caps the flow rate at `O(1/log n)`. Hence "the gap is
`o(log n)`" says exactly that no code exists for large `n`.
* `ObliviousLinearTimeTransposable`: (T) for machines that are oblivious at every size.
* `runDiagram M w₀ T`: the time–space diagram of the run of a machine.
* `rescaled`: the rescaled work walks of a diagram (frozen at `T`), for Theorem M\* on diagrams
  (`MStarDiagram.lean`).
-/

namespace Transpose.Tape

open Transpose

/-! ## Time–space diagrams and their block networks -/

/-- A `k`-tape **time–space diagram**: a length `T`, the work-head walks, the input-head walk and the
output schedule (`out τ` = number of output bits before step `τ`). -/
structure TSDiagram (k : ℕ) where
  T : ℕ
  work : Fin k → ℕ → ℤ
  inp : ℕ → ℤ
  out : ℕ → ℕ

namespace TSDiagram

variable {k : ℕ}

/-- A **valid** diagram for an output of length `L`: the walks start at cell `0` and move by unit
steps; the output schedule starts at `0`, grows by at most one bit per step and equals `L` from time
`T` on. -/
def Valid (D : TSDiagram k) (L : ℕ) : Prop :=
  (∀ t, D.work t 0 = 0 ∧ UnitSteps (D.work t)) ∧ D.inp 0 = 0 ∧ UnitSteps D.inp ∧
    D.out 0 = 0 ∧ (∀ τ, D.out τ ≤ D.out (τ + 1) ∧ D.out (τ + 1) ≤ D.out τ + 1) ∧
    ∀ τ, D.T ≤ τ → D.out τ = L

/-- The nodes of the block network: the slots `y < ⌈T/r⌉`. -/
def nodes (D : TSDiagram k) (r : ℕ) : ℕ := numSlots r D.T

/-- The memory edges `y → y + 1`. -/
def memEdges (D : TSDiagram k) (r : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (D.nodes r)).filter (fun y => y + 1 < D.nodes r)).image (fun y => (y, y + 1))

open Classical in
/-- The chord edges: `x → z` whenever some work tape has a chord `x → z` of its pair residency. -/
noncomputable def chordEdges (D : TSDiagram k) (r : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (D.nodes r) ×ˢ Finset.range (D.nodes r)).filter
    (fun p => ∃ (t : Fin k) (β : ℤ), IsChord (pairRes r (D.work t) D.T) β p.1 p.2)

/-- The edges of the block network. -/
noncomputable def edges (D : TSDiagram k) (r : ℕ) : Finset (ℕ × ℕ) :=
  D.memEdges r ∪ D.chordEdges r

open Classical in
/-- The input rows attached at node `y`: those the input walk touches during slot `y`. -/
noncomputable def rowsAt (D : TSDiagram k) (n w r y : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => ∃ τ ∈ slotOf r D.T y,
    ((i * n * w : ℕ) : ℤ) ≤ D.inp τ ∧ D.inp τ < (((i + 1) * n * w : ℕ) : ℤ))

/-- The node producing output position `o`: the last slot `y < ⌈T/r⌉` whose first step comes after
fewer than `o + 1` output bits, i.e. the slot during which bit `o` is appended. -/
def outNode (D : TSDiagram k) (r o : ℕ) : ℕ :=
  Nat.findGreatest (fun y => D.out (y * r) ≤ o) (D.nodes r - 1)

/-- The input visible at node `y`: the bits of the rows attached at `y` (other bits read `false`). -/
noncomputable def visible (D : TSDiagram k) (n w r y : ℕ) {L : ℕ} (x : Fin L → Bool) : ℕ → Bool :=
  fun d => if h : d < L then (if d / (n * w) ∈ D.rowsAt n w r y then x ⟨d, h⟩ else false) else false

end TSDiagram

/-! ## Causal network codes -/

/-- A **causal network code**. The value on edge `e = (u, v)` is `enc e f x`, where `f` gives the
values on the edges into `u` and `x` is the input visible at `u`. The bit at output position `o` is
`dec o f x`, with `f` and `x` taken at the sink of `o`. -/
structure NetCode where
  enc : ℕ × ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ
  dec : ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → Bool

namespace NetCode

/-- The values on the edges into node `v` (`0` on every other pair), given the visible inputs
`vis u` at every node `u`. The code is evaluated along the spine: an edge `(u, v) ∈ E` with `u < v`
is computed at `u` from the values into `u`. -/
noncomputable def inVals (C : NetCode) (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool) (v : ℕ)
    (e : ℕ × ℕ) : ℕ :=
  if _h : e ∈ E ∧ e.2 = v ∧ e.1 < v then C.enc e (fun e' => C.inVals E vis e.1 e') (vis e.1) else 0
termination_by v
decreasing_by exact _h.2.2

/-- The value on edge `e`. -/
noncomputable def edgeVal (C : NetCode) (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool) (e : ℕ × ℕ) : ℕ :=
  C.enc e (C.inVals E vis e.1) (vis e.1)

/-- The bit at output position `o`, computed at node `s`. -/
noncomputable def outVal (C : NetCode) (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool) (s o : ℕ) :
    Bool :=
  C.dec o (C.inVals E vis s) (vis s)

end NetCode

/-! ## Distances and flows -/

open Classical in
/-- The undirected ball of radius `j` around node `a` in the network on the nodes `< N` with edge
set `E`. -/
noncomputable def ball (E : Finset (ℕ × ℕ)) (N a : ℕ) : ℕ → Finset ℕ
  | 0 => {a}
  | j + 1 => ball E N a j ∪
      (Finset.range N).filter (fun v => ∃ u ∈ ball E N a j, (u, v) ∈ E ∨ (v, u) ∈ E)

open Classical in
/-- The undirected hop distance from `a` to `s` (`0` if `s` is unreachable). -/
noncomputable def netDist (E : Finset (ℕ × ℕ)) (N a s : ℕ) : ℕ :=
  if h : ∃ j, s ∈ ball E N a j then Nat.find h else 0

/-- A walk in the undirected network: consecutive nodes are joined by an edge. -/
def IsWalk (E : Finset (ℕ × ℕ)) (P : List ℕ) : Prop :=
  List.IsChain (fun u v => (u, v) ∈ E ∨ (v, u) ∈ E) P

open Classical in
/-- The number of times the walk `P` traverses the edge `e` (in either direction). -/
noncomputable def traversals (e : ℕ × ℕ) : List ℕ → ℕ
  | u :: v :: rest => (if (u, v) = e ∨ (v, u) = e then 1 else 0) + traversals e (v :: rest)
  | _ => 0

/-- A fractional multicommodity flow: for each commodity `d`, finitely many walks with weights. -/
structure Routing where
  paths : ℕ → Finset (List ℕ)
  wt : ℕ → List ℕ → ℝ

namespace TSDiagram

variable {k : ℕ}

/-- The block size at size `n` for `G` bits per cell: `r = ⌈n w / G⌉` with `w = entryBits n`. -/
def blockSize (G n : ℕ) : ℕ := (n * entryBits n + G - 1) / G

open Classical in
/-- `rowDist d`: the distance from the nodes holding the row of input bit `d` to the sink of its
transposed position, or `0` if the row has no source node. -/
noncomputable def rowDist (D : TSDiagram k) (n w r d : ℕ) : ℕ :=
  if h : ((Finset.range (D.nodes r)).filter (fun a => d / (n * w) ∈ D.rowsAt n w r a)).Nonempty
  then ((Finset.range (D.nodes r)).filter (fun a => d / (n * w) ∈ D.rowsAt n w r a)).inf' h
    (fun a => netDist (D.edges r) (D.nodes r) a (D.outNode r (tpos n w d)))
  else 0

/-- The code `code` **solves complete exchange** on the block network of `D` at size `n` (`G` bits
per cell) for the inputs of `F`, within the capacities `cap`. For every input of `F`, every edge
value is `< 2^{cap e}` and every output bit is the transposed input bit. -/
def Solves (D : TSDiagram k) (n G : ℕ) (cap : ℕ × ℕ → ℕ)
    (F : Set (Fin (n * n * entryBits n) → Bool)) (code : NetCode) : Prop :=
  ∀ x ∈ F,
    (∀ e ∈ D.edges (blockSize G n),
      code.edgeVal (D.edges (blockSize G n))
        (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ cap e) ∧
    ∀ (d : ℕ) (hd : d < n * n * entryBits n),
      code.outVal (D.edges (blockSize G n)) (fun y => D.visible n (entryBits n) (blockSize G n) y x)
        (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d) = x ⟨d, hd⟩

open Classical in
/-- The number of work tapes with a chord `e.1 → e.2` (block size `r`). -/
noncomputable def chordTapes (D : TSDiagram k) (r : ℕ) (e : ℕ × ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin k => ∃ β : ℤ, IsChord (pairRes r (D.work t) D.T) β e.1 e.2)).card

/-- The capacities are within the **block profile**, a block being `r G` bits (`r = ⌈n w/G⌉` cells
of `G` bits):
* a memory edge `y → y + 1` carries at most the blocks resident at slot `y`, over all work tapes
  (at most `3` per tape), and nothing else;
* a chord edge carries at most one block per work tape having that chord. -/
def CapProfile (D : TSDiagram k) (n G : ℕ) (cap : ℕ × ℕ → ℕ) : Prop :=
  (∀ e ∈ D.memEdges (blockSize G n),
    cap e ≤ (∑ t, (pairRes (blockSize G n) (D.work t) D.T e.1).card) * (blockSize G n * G)) ∧
  ∀ e ∈ D.chordEdges (blockSize G n), cap e ≤ D.chordTapes (blockSize G n) e * (blockSize G n * G)

/-- **Block capacities**: a memory edge `y → y + 1` gets `mem y` blocks plus `s` bits, a chord edge
one block per work tape having that chord, and every other pair `0` (a block is `r G` bits). -/
noncomputable def blockCap (D : TSDiagram k) (n G : ℕ) (mem : ℕ → ℕ) (s : ℕ) (e : ℕ × ℕ) : ℕ :=
  if e ∈ D.memEdges (blockSize G n) then mem e.1 * (blockSize G n * G) + s
  else if e ∈ D.chordEdges (blockSize G n) then
    D.chordTapes (blockSize G n) e * (blockSize G n * G)
  else 0

/-- The **per-node profile capacities**: on a memory edge `y → y + 1` the blocks resident at slot `y`
(over all work tapes, at most `3k`), on a chord edge one block per work tape having that chord, and
`0` off the edges. On the edges these are the largest capacities within `CapProfile` (which does not
constrain the other pairs, where no value is carried). -/
noncomputable def profileCap (D : TSDiagram k) (n G : ℕ) : ℕ × ℕ → ℕ :=
  D.blockCap n G (fun y => ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) 0

/-- The **rescaled walk** of work tape `t` at size `n` (`G` bits per cell, block size
`r = blockSize G n`), for Theorem M\* on diagrams: the block of the walk at the first step of slot
`⌊u n⌋`, divided by `n`. The walk is frozen at time `T` (the diagram ends there; for a machine's run,
`runDiagram`, the heads are frozen after halting anyway). -/
noncomputable def rescaled (D : TSDiagram k) (n G : ℕ) (t : Fin k) (u : ℝ) : ℝ :=
  (curBlock (blockSize G n) (fun τ => D.work t (min τ D.T)) (⌊u * n⌋₊ * blockSize G n) : ℝ) / n

/-- The rows attached at the nodes of a set `U` of nodes (the sources inside `U`). -/
noncomputable def rowsIn (D : TSDiagram k) (n w r : ℕ) (U : Set ℕ) [DecidablePred (· ∈ U)] :
    Finset ℕ :=
  ((Finset.range (D.nodes r)).filter (· ∈ U)).biUnion (fun y => D.rowsAt n w r y)

/-- The columns whose output positions are all produced at nodes of `U` (the sinks inside `U`). -/
noncomputable def colsIn (D : TSDiagram k) (n w r : ℕ) (U : Set ℕ) [DecidablePred (· ∈ U)] :
    Finset ℕ :=
  (Finset.range n).filter (fun j => ∀ o, j * n * w ≤ o → o < (j + 1) * n * w → D.outNode r o ∈ U)

/-- The edges entering a set `U` of nodes. -/
noncomputable def edgesInto (D : TSDiagram k) (r : ℕ) (U : Set ℕ) [DecidablePred (· ∈ U)] :
    Finset (ℕ × ℕ) :=
  (D.edges r).filter (fun e => e.1 ∉ U ∧ e.2 ∈ U)

/-- The routing `ρ` routes `rate` units of every commodity within the capacities `cap`. The
commodities are the input bits `d < L` whose row has a source node; each is routed along walks from a
source node of its row to the sink of its transposed position. -/
def RoutesAt (D : TSDiagram k) (n G : ℕ) (cap : ℕ × ℕ → ℕ) (ρ : Routing) (rate : ℝ) : Prop :=
  (∀ d < n * n * entryBits n,
    (∃ a < D.nodes (blockSize G n),
      d / (n * entryBits n) ∈ D.rowsAt n (entryBits n) (blockSize G n) a) →
    (∀ P ∈ ρ.paths d, 0 ≤ ρ.wt d P ∧ IsWalk (D.edges (blockSize G n)) P ∧
      (∃ a, P.head? = some a ∧ a < D.nodes (blockSize G n) ∧
        d / (n * entryBits n) ∈ D.rowsAt n (entryBits n) (blockSize G n) a) ∧
      P.getLast? = some (D.outNode (blockSize G n) (tpos n (entryBits n) d))) ∧
    ∑ P ∈ ρ.paths d, ρ.wt d P = rate) ∧
  ∀ e ∈ D.edges (blockSize G n),
    ∑ d ∈ (Finset.range (n * n * entryBits n)).filter (fun d => ∃ a < D.nodes (blockSize G n),
        d / (n * entryBits n) ∈ D.rowsAt n (entryBits n) (blockSize G n) a),
      ∑ P ∈ ρ.paths d, ρ.wt d P * (traversals e P : ℝ) ≤ cap e

end TSDiagram

/-! ## The conjectures -/

open TSDiagram in
/-- **Robust CE_TM** (the Tape Coding Conjecture, flow form). For every number of tapes
`k`, bits per cell `G ≥ 1`, time constant `c`, co-entropy constant `C` and `ε > 0`, the following
holds for all large `n` (with `w = entryBits n`, `L = n² w`, block size `r = ⌈n w/G⌉`). Take a valid
`k`-tape diagram of length `≤ c L`, capacities `cap` within the block profile, and a set `F` of
inputs of co-entropy `≤ C n w`. If some causal code solves complete exchange on `F` within `cap`,
then the demand is fractionally routable at rate `1/(ε w)` within `cap`: coding beats multicommodity
flow by at most the factor `ε w`. -/
def RobustCE_TM : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, D.Solves n G cap F code →
      ∃ ρ : Routing, D.RoutesAt n G cap ρ (1 / (ε * entryBits n))

open TSDiagram in
/-- **Robust CE_TM, distance form**: the flow rate is replaced by its volume bound,
`Σ_d rowDist d ≤ ε w Σ_e cap e`. It is equivalent to `RobustCE_TM` (weak duality gives one
direction, the equivalence with `RobustNoCode_TM` the other). -/
def RobustCE_TM_dist : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, D.Solves n G cap F code →
      ((∑ d ∈ Finset.range (n * n * entryBits n),
          D.rowDist n (entryBits n) (blockSize G n) d : ℕ) : ℝ) ≤
        ε * entryBits n * ∑ e ∈ D.edges (blockSize G n), (cap e : ℝ)

open TSDiagram in
/-- **CE_TM** (independent uniform sources): `RobustCE_TM` for codes correct on all inputs. -/
def CE_TM : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ code : NetCode, D.Solves n G cap Set.univ code →
      ∃ ρ : Routing, D.RoutesAt n G cap ρ (1 / (ε * entryBits n))

open TSDiagram in
/-- **CE_TM, distance form.** -/
def CE_TM_dist : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ code : NetCode, D.Solves n G cap Set.univ code →
      ((∑ d ∈ Finset.range (n * n * entryBits n),
          D.rowDist n (entryBits n) (blockSize G n) d : ℕ) : ℝ) ≤
        ε * entryBits n * ∑ e ∈ D.edges (blockSize G n), (cap e : ℝ)

open TSDiagram in
/-- **No code (robust form).** For every number of tapes `k`, bits per cell `G ≥ 1`, time constant
`c` and co-entropy constant `C`, the following holds for all large `n`. No causal code solves complete
exchange at the block-profile capacities (`profileCap`: the resident blocks on a memory edge, one
block per tape on a chord edge), on the block network of a valid `k`-tape diagram of length `≤ c L`,
for a set of inputs of co-entropy `≤ C n w`. Since `Solves` is monotone in the capacities, this is
the same as ruling out codes within every `cap` satisfying `CapProfile`
(`robustNoCode_iff_forall_cap`). This is equivalent to `RobustCE_TM` and to `RobustCE_TM_dist`: a
code that solves complete exchange has rate `1`, while the volume bound caps the flow rate at
`O(1/log n)`. -/
def RobustNoCode_TM : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code

open TSDiagram in
/-- **No code** (independent uniform sources): `RobustNoCode_TM` for codes correct on all inputs.
This is equivalent to `CE_TM` and to `CE_TM_dist`. -/
def NoCode_TM : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) Set.univ code

open TSDiagram in
/-- `RobustNoCode_TM` with `s k n` extra bits on every memory edge of a `k`-tape diagram: the per-node
blocks plus `s k n` bits. It rules out every machine family whose state bits plus head-position bits
fit in `s k n` (`no_fast_transposer_of_robustNoCode_bits`); for instance `s k n = (3k + 4) ⌈log₂ n⌉`,
i.e. `O(log n)` bits, already rules out every fixed machine. For `s k n ≤ C(k) n w` (for `n ≥ 1`) it is
equivalent to `RobustNoCode_TM` (`robustNoCode_bits_iff`; `robustNoCode_logBits_iff` for this `s`). -/
def RobustNoCode_TM_bits (s : ℕ → ℕ → ℕ) : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode,
      ¬ D.Solves n G (D.blockCap n G
        (fun y => ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) (s k n)) F code

open TSDiagram in
/-- `RobustNoCode_TM` with the uniform memory profile of `m k` blocks for `k`-tape diagrams. For every
unbounded `m` (equivalently, `3k ≤ m (k + a)` for some `a`, for every `k`: `exists_shift_iff_unbounded`;
for instance `3k`, `3k + 1`, or one block per tape `m k = k`) it is equivalent to `RobustNoCode_TM`
(`robustNoCode_with_iff`). The profile of `3k` blocks plus `O(1)` (or `O(log n)`) bits lies between
`m k = 3k` and `m k = 3k + 1` for large `n`. -/
def RobustNoCode_TM_with (m : ℕ → ℕ) : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, ¬ D.Solves n G (D.blockCap n G (fun _ => m k) 0) F code

/-- Every input row is attached at some node: the input walk touches every row. -/
def TSDiagram.AllRowsAttached {k : ℕ} (D : TSDiagram k) (n w r : ℕ) : Prop :=
  ∀ i < n, ∃ a < D.nodes r, i ∈ D.rowsAt n w r a

open TSDiagram in
/-- `RobustNoCode_TM` restricted to diagrams whose input walk attaches every row. It is equivalent to
`RobustNoCode_TM` (`robustNoCode_iff_attached`: append an input sweep). -/
def RobustNoCode_TM_att : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    D.AllRowsAttached n (entryBits n) (blockSize G n) →
    ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code

open TSDiagram in
/-- **Robust CE_TM on diagrams with every row attached** (flow form). Every commodity has a source
node, so no convention for rows without one is involved. It is equivalent to `RobustNoCode_TM`, and
hence to `RobustCE_TM` (`robustCE_TM_att_iff`). -/
def RobustCE_TM_att : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    D.AllRowsAttached n (entryBits n) (blockSize G n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, D.Solves n G cap F code →
      ∃ ρ : Routing, D.RoutesAt n G cap ρ (1 / (ε * entryBits n))

/-! ### Infinitely-often forms

¬(T) needs only one failing size per machine, while a linear-time transposer gives codes at *every*
large `n`. So "for all large `n`" may be weakened to "for infinitely many `n`" (`∀ n₀, ∃ n ≥ n₀`).
These forms are formally weaker targets that still refute (T) (`NoCode_TM_io`: oblivious (T)). -/

open TSDiagram in
/-- **No code, infinitely often**: `RobustNoCode_TM` with "for all large `n`" weakened to "for
infinitely many `n`". It still refutes (T) (`not_linearTimeTransposable_of_robustNoCode_io`), and it is
equivalent to the infinitely-often flow and distance forms. -/
def RobustNoCode_TM_io : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code

open TSDiagram in
/-- **Robust CE_TM, infinitely often** (flow form): `RobustCE_TM` for infinitely many `n`. -/
def RobustCE_TM_io : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∀ ε : ℝ, 0 < ε → ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, D.Solves n G cap F code →
      ∃ ρ : Routing, D.RoutesAt n G cap ρ (1 / (ε * entryBits n))

open TSDiagram in
/-- **Robust CE_TM, distance form, infinitely often.** -/
def RobustCE_TM_dist_io : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∀ ε : ℝ, 0 < ε → ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, D.Solves n G cap F code →
      ((∑ d ∈ Finset.range (n * n * entryBits n),
          D.rowDist n (entryBits n) (blockSize G n) d : ℕ) : ℝ) ≤
        ε * entryBits n * ∑ e ∈ D.edges (blockSize G n), (cap e : ℝ)

open TSDiagram in
/-- **No code for independent sources, infinitely often**: `NoCode_TM` for infinitely many `n`. It
still refutes oblivious (T). -/
def NoCode_TM_io : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) Set.univ code

/-! ### Robust versus plain: hints and side channels -/

open TSDiagram in
/-- **No code on a set of co-entropy `≤ m(n)`**: for all constants and all large `n`, no causal code
solves complete exchange at the profile capacities on a set `F` of inputs with `2^L ≤ 2^{m n} |F|`.
This is a ladder between the plain and the robust target: `m = 0` is `NoCode_TM`
(`noCode_iff_coent_zero`), and `m = C n w` for every `C` is `RobustNoCode_TM`
(`robustNoCode_iff_coent`). -/
def NoCode_TM_coent (m : ℕ → ℕ) : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ m n * F.ncard →
    ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code

open TSDiagram in
/-- **No code even with an `s(n)`-bit oracle hint**: for all constants and all large `n`, no
family of causal codes `codes h`, indexed by a hint `h = hint x < 2^{s n}` that may be *any function
of the whole input* (as if a coordinator saw the input and told every node; the hint is uncharged:
no edge carries it and no node computes it), solves complete exchange on every input at the profile
capacities. Equivalently, the inputs cannot be covered by `2^{s n}`
sets each carrying a code. It agrees with `NoCode_TM_coent` up to `3 w + 1` bits
(`hintBits_of_coent`, `coent_of_hintBits`). -/
def NoCode_TM_hintBits (s : ℕ → ℕ) : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (hint : (Fin (n * n * entryBits n) → Bool) → ℕ) (codes : ℕ → NetCode),
      (∀ x, hint x < 2 ^ s n) →
      ¬ ∀ x, D.Solves n G (D.profileCap n G) {x} (codes (hint x))

/-- **No code even with an oracle `O(n w)`-bit hint** (the coordinator form of the robust
target): `NoCode_TM_hintBits (C n w)` for every `C`. It is equivalent to `RobustNoCode_TM`
(`robustNoCode_iff_hint`); with a constant hint (`C = 0`) it gives `NoCode_TM`. -/
def NoCode_TM_hint : Prop :=
  ∀ C : ℕ, NoCode_TM_hintBits (fun n => C * n * entryBits n)

open TSDiagram in
/-- **No code at co-entropy `≤ m(n)`, for infinitely many `n`**: for all constants, arbitrarily large
`n` exist at which no causal code solves complete exchange at the profile capacities on a set of
co-entropy `≤ m n`. It is weaker than `NoCode_TM_coent m` (`coent_io_of_coent`). -/
def NoCode_TM_coent_io (m : ℕ → ℕ) : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ m n * F.ncard →
    ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code

open TSDiagram in
/-- **No code at co-entropy `≤ m(n)` on diagrams with the output at the end**: as `NoCode_TM_coent`,
but only for diagrams that append one output bit per step in their last `L` steps
(`D.out τ = L − (D.T − τ)`). It is weaker than `NoCode_TM_coent m`; a fast transposer gives such
diagrams (`codes_coentLinear_at`). -/
def NoCode_TM_coent_end (m : ℕ → ℕ) : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    (∀ τ ≤ D.T, D.out τ = n * n * entryBits n - (D.T - τ)) →
    ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ m n * F.ncard →
    ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code

open TSDiagram in
/-- **No code at co-entropy `≤ m(n)` on diagrams with the output at the end, for infinitely many
`n`**: `NoCode_TM_coent_end` with "for all large `n`" weakened to "for infinitely many `n`". It is
weaker than both `NoCode_TM_coent_end m` and `NoCode_TM_coent_io m`, and at `m = C n` (every `C`) it
still refutes (T) (`not_linearTimeTransposable_of_coentLinear_end_io`). -/
def NoCode_TM_coent_end_io (m : ℕ → ℕ) : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    (∀ τ ≤ D.T, D.out τ = n * n * entryBits n - (D.T - τ)) →
    ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ m n * F.ncard →
    ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code

open TSDiagram in
/-- **Robust CE_TM in the γ-form**: for some `γ(n) > 0` with `γ(n) ≤ ε w` eventually
for every `ε > 0` (so `γ = o(log n)`, measured by `w`), every solving code's demand is routable at
rate `1/γ(n)`: coding beats flow by at most the factor `γ(n)`. Here one `γ` serves all constants
`k, G, c, C`; the per-constant reading is `RobustCE_TM_gamma_per`. Both are equivalent to
`RobustNoCode_TM` (`robustCE_TM_gamma_iff`, `robustCE_TM_gamma_per_iff`). -/
def RobustCE_TM_gamma : Prop :=
  ∃ γ : ℕ → ℝ, (∀ n, 0 < γ n) ∧ (∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n → γ n ≤ ε * entryBits n) ∧
    ∀ (k G c C : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, D.Solves n G cap F code →
      ∃ ρ : Routing, D.RoutesAt n G cap ρ (1 / γ n)

open TSDiagram in
/-- **Robust CE_TM in the γ-form, per constants**: as `RobustCE_TM_gamma`, but `γ` may depend on
`k, G, c, C` (the natural reading of "for some `γ(n) = o(log n)`"). It is also equivalent to
`RobustNoCode_TM` (`robustCE_TM_gamma_per_iff`). -/
def RobustCE_TM_gamma_per : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∃ γ : ℕ → ℝ, (∀ n, 0 < γ n) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n → γ n ≤ ε * entryBits n) ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
    ∀ code : NetCode, D.Solves n G cap F code →
      ∃ ρ : Routing, D.RoutesAt n G cap ρ (1 / γ n)

open TSDiagram in
/-- **CE_TM at co-entropy `O(n)`** (the flow form at the linear rung): `RobustCE_TM` with co-entropy
`C n` in place of `C n w`. It is equivalent to `∀ C, NoCode_TM_coent (C n)` (`robustCE_TM_lin_iff`),
hence it refutes (T). -/
def RobustCE_TM_lin : Prop :=
  ∀ (k G c C : ℕ), 1 ≤ G → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
      2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n) * F.ncard →
    ∀ code : NetCode, D.Solves n G cap F code →
      ∃ ρ : Routing, D.RoutesAt n G cap ρ (1 / (ε * entryBits n))

open TSDiagram in
/-- `NoCode_TM` with `s k n` extra bits on every memory edge: a side channel along the spine whose
contents the code computes itself (charged, unlike the oracle hint of `NoCode_TM_hintBits`). For
`s k n ≤ C(k) n w` it is equivalent to `NoCode_TM` (`noCode_bits_iff`). -/
def NoCode_TM_bits (s : ℕ → ℕ → ℕ) : Prop :=
  ∀ (k G c : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
    ∀ code : NetCode,
      ¬ D.Solves n G (D.blockCap n G
        (fun y => ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) (s k n)) Set.univ code

/-- **(T) for oblivious machines**: some machine transposes within linear time `c (L + 1)` and is
oblivious on the `n × n` matrix inputs of every size `n ≥ 1`. -/
def ObliviousLinearTimeTransposable : Prop :=
  ∃ (M : TM) (c : ℕ), TransposesWithin M (fun L => c * (L + 1)) ∧
    ∀ n, 1 ≤ n → ∃ T, ObliviousOn M (matrixInputs n (entryBits n)) T

/-! ## The diagram of a run -/

/-- The time–space diagram of the run of `M` on `w₀`, of length `T`: the work-head and input-head
trajectories and the output length. -/
def runDiagram (M : TM) (w₀ : List Bool) (T : ℕ) : TSDiagram M.k where
  T := T
  work := fun t τ => workTraj M w₀ τ t
  inp := inTraj M w₀
  out := fun τ => (run M w₀ τ).outRev.length

end Transpose.Tape
