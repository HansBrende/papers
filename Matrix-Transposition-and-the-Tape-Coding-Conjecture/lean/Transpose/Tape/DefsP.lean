import Transpose.Tape.Defs

/-!
# Definitions: passes and the dependency forest (Theorem P)

**Passes.**
* `MonoOn h a e`: the positions of `h` at the times `a, …, e` are monotone. Equivalently, the
  moves at the steps `[a, e)` are all non-left or all non-right.
* `AllMono M w a e`: every head of `M` on `w` (input and work heads) is monotone on `[a, e)`.
* `PassPartition M w T r p`: `[0, T)` splits into `r` consecutive passes `[p i, p (i+1))` with
  every head monotone in each.
* `greedyBound` and `greedyPasses`: the greedy passes.
* `addrCount k r = Σ_{i<r} (k+1)^i`: the address count `𝓗 = ((k+1)^r - 1)/k`.

**The dependency forest** of an output segment `[o₁, o₂)`, for a fixed (common) head trajectory.
* `rootNode`: in each pass, the steps during which the output length moves inside the segment.
* `sSet`: the S-set. For a node `J` with first step `a`, tape `t` and an earlier pass `P'`, it is
  the cells the head accesses during `J`, other than its cell at `a`, whose last visit before `a`
  lies in pass `P'`.
* `childNode`: the steps of pass `P'` at which the head is in the hull `[min S, max S]`.
* `addrsBelow` and `addresses`: addresses are lists of (pass, tape) with strictly decreasing passes
  below a root pass `P₀ < r`. There are at most `𝓗` of them.
* `forestNode`: the node at an address. `forest`: the union of all nodes of a segment.
* `readSet`: the input positions in `[0, L)` read during a step set `J` (`I_J`).
* `combSet`: the input bits whose transposed copy lies in the output segment (the comb).
-/

namespace Transpose.Tape

open Transpose

/-! ## Passes -/

/-- The positions of the trajectory `h` at the times `a, …, e` are monotone: either every step
of `[a, e)` is non-decreasing, or every step is non-increasing. -/
def MonoOn (h : ℕ → ℤ) (a e : ℕ) : Prop :=
  (∀ τ, a ≤ τ → τ < e → h τ ≤ h (τ + 1)) ∨ (∀ τ, a ≤ τ → τ < e → h (τ + 1) ≤ h τ)

/-- Every head of `M` on input `w` (the input head and every work head) is monotone on the steps
`[a, e)`. -/
def AllMono (M : TM) (w : List Bool) (a e : ℕ) : Prop :=
  MonoOn (inTraj M w) a e ∧ ∀ t : Fin M.k, MonoOn (fun τ => workTraj M w τ t) a e

/-- `p` splits the steps `[0, T)` into `r` consecutive passes `[p i, p (i+1))`, `i < r`, with every
head monotone in each pass. Passes may be empty. Such a `p` exists exactly when the greedy pass
count is at most `r` (`passPartition_iff`). -/
def PassPartition (M : TM) (w : List Bool) (T r : ℕ) (p : ℕ → ℕ) : Prop :=
  p 0 = 0 ∧ p r = T ∧ (∀ i < r, p i ≤ p (i + 1)) ∧ ∀ i < r, AllMono M w (p i) (p (i + 1))

open Classical in
/-- The greedy passes. Pass `0` starts at step `0`. Each pass is extended as far as possible, up
to `T`, subject to every head being monotone in it. `greedyBound M w T i` is the first step of
pass `i`. -/
noncomputable def greedyBound (M : TM) (w : List Bool) (T : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => Nat.findGreatest
      (fun e => greedyBound M w T i ≤ e ∧ AllMono M w (greedyBound M w T i) e) T

open Classical in
/-- The number of greedy passes: the least `i` with `greedyBound M w T i = T`. -/
noncomputable def greedyPasses (M : TM) (w : List Bool) (T : ℕ) : ℕ :=
  if h : ∃ i, greedyBound M w T i = T then Nat.find h else 0

/-- The address count `𝓗 = Σ_{i<r} (k+1)^i = ((k+1)^r - 1)/k`. -/
def addrCount (k r : ℕ) : ℕ := ∑ i ∈ Finset.range r, (k + 1) ^ i

/-! ## The dependency forest -/

/-- The steps of pass `P`. -/
def passSteps (p : ℕ → ℕ) (P : ℕ) : Finset ℕ := Finset.Ico (p P) (p (P + 1))

/-- The first step of a nonempty step set (`0` for the empty set). -/
noncomputable def firstStep (J : Finset ℕ) : ℕ := if hJ : J.Nonempty then J.min' hJ else 0

/-- `σ` is the last visit to cell `c` before time `a` by a head with trajectory `h`. -/
def IsLastVisitTo (h : ℕ → ℤ) (c : ℤ) (a σ : ℕ) : Prop :=
  σ < a ∧ h σ = c ∧ ∀ ρ, σ < ρ → ρ < a → h ρ ≠ c

open Classical in
/-- The S-set of node `J` for a tape with trajectory `h` and a pass `P'`. It consists of the cells
`h τ`, `τ ∈ J`, other than the cell `h a` at the first step `a` of `J`, whose last visit before `a`
lies in pass `P'`. -/
noncomputable def sSet (h : ℕ → ℤ) (p : ℕ → ℕ) (J : Finset ℕ) (P' : ℕ) : Finset ℤ :=
  (J.image h).filter (fun c => c ≠ h (firstStep J) ∧
    ∃ σ ∈ passSteps p P', IsLastVisitTo h c (firstStep J) σ)

open Classical in
/-- The child of node `J` for this tape and pass `P'`: the steps of pass `P'` at which the head is
in the hull `[min S, max S]` of the S-set. It is empty when the S-set is empty. -/
noncomputable def childNode (h : ℕ → ℤ) (p : ℕ → ℕ) (J : Finset ℕ) (P' : ℕ) : Finset ℕ :=
  if hS : (sSet h p J P').Nonempty then
    (passSteps p P').filter (fun τ => (sSet h p J P').min' hS ≤ h τ ∧ h τ ≤ (sSet h p J P').max' hS)
  else ∅

open Classical in
/-- The root of the output segment `[o₁, o₂)` in pass `P`: the steps of pass `P` during which the
output length moves inside the segment (`len τ < o₂` and `o₁ < len (τ + 1)`). When
`o₁ < o₂ ≤` (final output length), the roots taken over all passes are exactly the steps from the
first to the last append of the segment's bits. -/
noncomputable def rootNode (len : ℕ → ℕ) (p : ℕ → ℕ) (o₁ o₂ P : ℕ) : Finset ℕ :=
  (passSteps p P).filter (fun τ => len τ < o₂ ∧ o₁ < len (τ + 1))

/-- The output length (number of bits appended before time `τ`) on input `w`. -/
def outLen (M : TM) (w : List Bool) (τ : ℕ) : ℕ := (run M w τ).outRev.length

/-- The node at address `(P₀, l)`. Start at the root in pass `P₀`; then, for each entry `(P', t)`
of `l` in order, pass to the child for work tape `t` and pass `P'`. -/
noncomputable def forestNode (M : TM) (w : List Bool) (p : ℕ → ℕ) (o₁ o₂ P₀ : ℕ)
    (l : List (ℕ × Fin M.k)) : Finset ℕ :=
  l.foldl (fun J x => childNode (fun τ => workTraj M w τ x.2) p J x.1)
    (rootNode (outLen M w) p o₁ o₂ P₀)

/-- Addresses below pass `P`: lists of (pass, tape) whose passes are strictly decreasing and
`< P`. They are built pass by pass. -/
def addrsBelow (k : ℕ) : ℕ → Finset (List (ℕ × Fin k))
  | 0 => {[]}
  | P + 1 => addrsBelow k P ∪
      Finset.univ.biUnion (fun t : Fin k => (addrsBelow k P).image (fun l => (P, t) :: l))

/-- All addresses: a root pass `P₀ < r` together with an address below `P₀`. -/
def addresses (k r : ℕ) : Finset (ℕ × List (ℕ × Fin k)) :=
  (Finset.range r).biUnion (fun P₀ => (addrsBelow k P₀).image (fun l => (P₀, l)))

/-- The dependency forest of the output segment `[o₁, o₂)`: the union of its nodes over all
addresses. -/
noncomputable def forest (M : TM) (w : List Bool) (p : ℕ → ℕ) (r o₁ o₂ : ℕ) : Finset ℕ :=
  (addresses M.k r).biUnion (fun α => forestNode M w p o₁ o₂ α.1 α.2)

open Classical in
/-- The input positions in `[0, L)` read at the steps of `J` (input trajectory `ip`). -/
noncomputable def readSet (ip : ℕ → ℤ) (L : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun d => ∃ τ ∈ J, ip τ = (d : ℤ))

/-- The comb of the output segment `[o₁, o₂)`: the input bits `d < n²b` whose copy in the
transposed output lies in `[o₁, o₂)`. For column `j`, i.e. `[j n b, (j+1) n b)`, this is
`comb_j = ⋃_{i<n} [(i n + j) b, (i n + j + 1) b)`. -/
def combSet (n b o₁ o₂ : ℕ) : Finset ℕ :=
  (Finset.range (n * n * b)).filter (fun d => o₁ ≤ tpos n b d ∧ tpos n b d < o₂)

/-! ## Groups of columns -/

/-- The number of groups of `γ` consecutive columns: `⌈n / γ⌉`. -/
def numGroups (n γ : ℕ) : ℕ := (n + γ - 1) / γ

/-- The first output position of group `s` (columns `[s γ, min((s+1) γ, n))`). -/
def segLo (n b γ s : ℕ) : ℕ := min (s * γ) n * (n * b)

/-- The end of the output range of group `s`. -/
def segHi (n b γ s : ℕ) : ℕ := min ((s + 1) * γ) n * (n * b)

end Transpose.Tape
