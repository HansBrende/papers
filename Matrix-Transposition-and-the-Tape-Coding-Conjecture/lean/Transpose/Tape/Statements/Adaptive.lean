import Transpose.Tape.Statements.Core
import Transpose.Tape.DefsPP
import Transpose.Tape.PPrime
import Transpose.Tape.PPrimeExamples
import Transpose.Tape.DefsTrace
import Transpose.Tape.MStarAdaptive
import Transpose.Tape.OffsetsCounterexample
import Transpose.Tape.MStarRobust

/-!
# Statements: adaptive machines

Theorem P′ (data-dependent heads) and the Block Locality Lemma, with its consequences for adaptive
machines (the Cut Lemma, Discrete Isoperimetry and Theorem M\* on trace classes), are fully proved,
together with their robust forms (machines correct only on a trace class, or on a large set of
inputs). Each statement is proved by an `Impl` result, of the same name except:
* `theoremPprime_hyps_tr2k` and `theoremPprime_hyps_tr2dd`, assembled from public or `Impl` lemmas;
* the `_on` forms of the trace-class results, proved by the `Impl` result without the suffix (whose
  correctness hypothesis is `Impl.ClassCorrect`, the class-correctness condition spelled out in the
  statement); the forms with `Transposes` derive it by `Impl.classCorrect_of_transposes`.

## Theorem P′: data-dependent heads

Definitions: `DefsP.lean` (passes and forests, as for Theorem P) and `DefsPP.lean` (node codes).

Theorem P′ drops obliviousness. Every input `w` has its own running time `T_w ≤ T`, its own pass
partition into `r` passes and its own dependency forests. The proof conditions on the *structure*
of a column's forest. Here a node's structure is `nodeCode`: its first and last steps, and the
positions of all heads and the output length at its first step. Its side information is
`sideCode`: the state and the `k` symbols under the work heads at its first step.

* `locality_anchored`: the Locality Lemma for arbitrary step sets with data-dependent heads. Two
  runs agree on a step set `J` if they agree at its anchors, every non-anchor step has its
  predecessor in `J`, every cell read at a non-anchor step was last written inside `J` (or never) in
  either run, and the input bits agree wherever the input heads agree.
* `forest_agree` (the Forest Lemma, data-dependent form): two inputs whose forests for a segment
  have the same node and side codes, and whose bits agree at the positions read by both forests,
  have the same forest and run identically on it.
* `forest_comb_agree`: for a correct transposer, such inputs agree on the segment's comb.
* `kraft_group`, the information count for data-dependent heads: summed over all inputs `v`,
  `Σ_v 2^{|comb ∖ U(v)|} ≤ 2^{n²b} · ((2T+1)^{k+4} (q+1)(g+1)^k)^𝓗`, where `U(v)` is the set of input
  positions read by `v`'s forest. In the oblivious case all forests coincide, and this is
  `forest_info` up to the structure factor.
* Theorem P′: `theoremPprime_grouped` (the grouped form P′_γ, log-free), `theoremPprime_grouped_bits`,
  `theoremPprime` (`γ = 1`), `theoremPprime_bits`, `theoremPprime_div`, `theoremPprime_pow`,
  `theoremPprime_gamma` (the bits form with `+1` of Theorem P with `σ` replaced by `σ + γ`, for the
  structure cost `γ = ⌈log₂ r⌉ + 2(k+2)⌈log₂(2T+3)⌉`), `theoremPprime_ratio` (the ratio form
  `𝓗 ≥ n/(2 + (σ+γ+1)/b)`) and `theoremPprime_greedy`.
* `theoremPprime_hyps_of_oblivious`: an oblivious transposer with an `r`-pass partition satisfies
  the hypotheses of Theorem P′. `theoremPprime_hyps_tr2k`: they are satisfiable with `k = 1`.
  `theoremPprime_hyps_tr2dd`: they hold for a machine whose running time depends on the input.
* `theoremPprime_no_five_pass`: a concrete instance where the conclusion excludes `5` passes with
  `T ≥ L`. `theoremPprime_linearTime`: Theorem P′ for a machine satisfying the frozen
  `TransposesWithin`.

Remarks on the proof:
* The structure cost per node is `(k+4)⌈log₂(2T+1)⌉` bits, below the structure cost `γ` of
  `theoremPprime_gamma`. There is no last-visit profile term (a proof through last-visit profiles
  pays `O(k r² log T)`, or `O(k r log T)`, bits per column for it), so the ratio form
  `𝓗 ≥ n/(2 + (σ+γ+1)/b)` holds as stated, without an error term `− O(k log³ n / b)`.
* Entropy is replaced by counting. The per-group count `kraft_group` is a Kraft inequality, and the
  groups are combined by AM–GM.
* Removing the hypothesis on `T` (via the run-length lemma of Grohe–Schweikardt) is not formalized;
  `T` stays a hypothesis. So `r ≥ log_{k+1} n − O(1)` for every machine follows here only when
  `log T = O(b)`, e.g. for `T ≤ poly(L)`.
* The intermediate case (oblivious heads, data-dependent output schedule) is not covered at a cost
  of `2⌈log₂(T+1)⌉` bits per column; Theorem P′ covers it with its per-node cost.

## The Block Locality Lemma, trace classes and the popular trace

Definitions: `DefsTrace.lean`. The block-level trace records, per slot, the pair residency, the
input rows touched and the output positions.

* `locality_entry`: a variant of `locality_anchored` (neither implies the other) in which reads may
  come from outside `J`, provided the cell's content at some earlier time `a` agrees and all later
  visits (in either run) lie in `J`.
* `block_locality` (**the Block Locality Lemma**): two inputs with the same block-level trace run
  identically on a union of slots `J` if they agree on: the state and **all head positions** at each
  memory boundary of `J`; the contents of the blocks resident there; the contents of the blocks
  entering `J` by chords, at entry; and the input rows touched during `J`.
  `block_locality_offsets_counterexample`: the version that records only the work-head offsets
  within their blocks is false (last paragraph).
* `traceClass_of_oblivious`: for an oblivious machine the matrix inputs form one trace class with
  `D = 0`; `traceClass_of_obliviousOn`: so does any set of matrix inputs on which the machine is
  oblivious. `traceClass_of_mem`: any member of a class is a representative.
* Representative independence: `rescaledTrajOf_close` (members of a class are within `4/n` of each
  other) and `tendstoUniformlyOn_of_mem` (so the limits are class invariants).
* `exists_popular_traceClass` (**the popular trace**): every machine has, at every size, a trace class
  with `2^L ≤ traceCount · |F|`; `traceBits_le`: `⌈log₂ traceCount⌉ ≤ C n b` for `T ≤ c L` (so
  `D = O(n log n)`, i.e. `O(1)` blocks per label class).

## The Cut Lemma and Discrete Isoperimetry on trace classes

* `cut_bound_trace` (**the Cut Lemma on a trace class**):
  `2^{b|S_J|} |F| ≤ 2^L · ((q+1)(2T+1)^{k+1})^μ · (g+1)^{r(3kμ + χ)}`; `cut_bound_trace_bits`:
  `b|S_J| − D ≤` entry bits when `2^L ≤ 2^D |F|`.
* `isoperimetry_trace` (**Discrete Isoperimetry on a trace class**): the labelled-partition form,
  losing `D` per label class, i.e. at most `(M_b + 1) D` in all.

## Theorem M* for trace classes, adaptive, robust and non-uniform machines

* `theoremMStar_level_class`: Theorem M\* (level form) for trace classes with `D = o(L)`, along any
  sequence on which the representatives' rescaled trajectories converge.
* `theoremMStar_level_adaptive`: for **every** machine that transposes in time `≤ c L`, popular trace
  classes with `D = o(L)` exist, convergent subsequences of their representatives' trajectories exist,
  and every such subsequential limit is 1-Lipschitz and satisfies (★).
  `no_stationary_limits_class_on`: the limits cannot all be `0`.
* `adaptive_hyps_of_linearTime`, `linearTimeTransposable_popular_limits`: the link to the frozen
  statement (T): under `LinearTimeTransposable`, the popular-trace limits of some machine satisfy (★)
  along every sequence of sizes.
* **Robust forms.** The trace-class results use correctness only on the class itself:
  `cut_bound_trace_on`, `cut_bound_trace_bits_on`, `isoperimetry_trace_on`,
  `mstar_discrete_class_on` (the discrete M\* inequality at one size), `theoremMStar_level_class_on`
  and `no_stationary_limits_class_on` assume only that `M` outputs the transposed encoding on every
  input of the class (the forms above, with `Transposes`, follow). `theoremMStar_level_robust`: a
  machine that is fast and correct only on sets `W_i` of co-entropy `m_i = o(L_i)` (so on a fraction
  `2^{-o(L)}` of the inputs: possibly exponentially small in `n`, e.g. `2^{-C n b}`, but not
  `2^{-εL}`) has popular trace classes `F_i ⊆ W_i` with `D_i ≤ m_i + C n_i b_i`, and every
  subsequential limit of their representatives' trajectories satisfies (★).
  `theoremMStar_excess_robust`: the labelling-free form (total excess multiplicity `≥ 1`, range
  bound, not all monotone).
* **Non-uniform machines.** `theoremMStar_class_nonuniform`: the class form for non-uniform
  machines, with convergent subsequences (the one route from machines to codes;
  `theoremMStar_level_class_on` is its case of one machine). `theoremMStar_level_nonuniform` and
  `theoremMStar_excess_nonuniform`: `theoremMStar_level_robust` and `theoremMStar_excess_robust`
  for non-uniform machines (one machine `M_i` per size with `k` work tapes and `G` bits per cell,
  any transition tables, `⌈log₂(q_i+1)⌉ = o(L_i)` states' bits), which are their case of one
  machine.

All machine forms of M\* are corollaries of Theorem M\* for code-carrying diagrams, hence of
Theorem M\* for walks (`theoremMStar_walk`, `Transpose/Tape/Statements/Coding.lean`).

## Robust forms of Theorem P′

`forest_comb_agree_on` and `kraft_group_on` need correctness only on the inputs involved, and no
halting. `theoremPprime_grouped_on` (and `_bits`, `theoremPprime_on`, `_on_bits`, `_on_div`,
`_on_pow`, `_on_greedy`): a machine that, only on a set `W` of co-entropy `≤ m`, has the transposed
output at a time `T' ≤ T` with an `r`-pass partition of `[0, T')` pays `m` bits per group of `γ`
columns. `theoremPprime_on_robust`: at co-entropy `C n b` (grouping `γ = 2C`),
`C n b ≤ 2C² b + 𝓗 (2C(2C+1) b + 2(σ + (k+4)⌈log₂(2T+1)⌉))`; `theoremPprime_on_robust_gamma`: any
grouping `γ`. `theoremPprime_grouped`, `theoremPprime_grouped_bits` and hence all of Theorem P′ are
proved as the case `W` = all inputs, `m = 0`.

## Why the Block Locality Lemma records full head positions

Recording only the work-head *offsets within their blocks* at memory boundaries is not enough: the
pair residency of a slot is an unordered union, so two runs can share the whole trace and all the
other listed data while their heads stand in different blocks at the same offset (for example
`r = 4`: one head moves `3 → 4 → 5 → 6 → 5`, the other `3 → 4 → 3 → 2 → 1`; afterwards both
residencies are `{0, 1}` forever and both offsets are `1`). A correct transposer can branch on the
input bit into these two motions and then output whether the cell under the head is marked;
`block_locality_offsets_counterexample` is such a machine, checked in the frozen model.
`block_locality` therefore records the full head positions: `(k+1)⌈log₂(2T+1)⌉` bits per memory
boundary, against `k⌈log₂(3r)⌉ + ⌈log₂(2T+1)⌉` for a minimal correct version (each work head's
block is one of the at most 3 resident blocks). This is harmless: the cost is `O(log T)` per memory
boundary, and there are `O(1)` memory boundaries per label class.
-/

namespace Transpose.Tape

open Transpose

/-! # Theorem P′: data-dependent heads -/

/-- **The Locality Lemma, anchored form (data-dependent heads, arbitrary step sets).** Let `J` be
a set of steps and `A` a set of *anchors*. Suppose that:
* every step of `J` that is not an anchor has its predecessor in `J`;
* at every anchor in `J` the two runs have the same state, head positions, output length and symbols
  under the work heads;
* at every non-anchor step of `J`, in either run, the cell under each work head was last written
  inside `J`, or never;
* at every step of `J` at which the two input heads are at the same position, the two inputs have
  the same symbol there.

Then the two runs agree at every step of `J`: same state, head positions, output length, symbols
under the work heads and transition. -/
theorem locality_anchored {M : TM} {w w' : List Bool} {J : Finset ℕ} {A : Set ℕ}
    (hpred : ∀ τ ∈ J, τ ∉ A → 1 ≤ τ ∧ τ - 1 ∈ J)
    (hanchor : ∀ τ ∈ J, τ ∈ A →
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧ headSym M w τ = headSym M w' τ)
    (hread : ∀ τ ∈ J, τ ∉ A → ∀ (t : Fin M.k) (σ : ℕ),
      (IsLastVisit (fun s => workTraj M w s t) τ σ → σ ∈ J) ∧
      (IsLastVisit (fun s => workTraj M w' s t) τ σ → σ ∈ J))
    (hinput : ∀ τ ∈ J, (run M w τ).inPos = (run M w' τ).inPos →
      readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ :=
  Impl.locality_anchored hpred hanchor hread hinput

/-- **The Forest Lemma, data-dependent form.** Let `w` and `w'` have the same length `L`, and let
`p`, `p'` be pass partitions into `r` passes of `[0, T)` on `w` and of `[0, T')` on `w'`. Suppose that
at every address the forest nodes of the output segment `[o₁, o₂)` have the same structure code and
the same side information, and that `w` and `w'` agree at every position `< L` read by both forests.
Then the two forests have the same node at every address, and the two runs agree at every step of
the forest. -/
theorem forest_agree {M : TM} {w w' : List Bool} {L T T' r : ℕ} {p p' : ℕ → ℕ}
    (hw : w.length = L) (hw' : w'.length = L)
    (hp : PassPartition M w T r p) (hp' : PassPartition M w' T' r p') {o₁ o₂ : ℕ}
    (hcode : ∀ α ∈ addresses M.k r,
      nodeCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          nodeCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2) ∧
        sideCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          sideCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2))
    (hinput : ∀ d ∈ readSet (inTraj M w) L (forest M w p r o₁ o₂),
      d ∈ readSet (inTraj M w') L (forest M w' p' r o₁ o₂) → nth w d = nth w' d) :
    (∀ α ∈ addresses M.k r, forestNode M w p o₁ o₂ α.1 α.2 = forestNode M w' p' o₁ o₂ α.1 α.2) ∧
    ∀ τ ∈ forest M w p r o₁ o₂,
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ :=
  Impl.forest_agree hw hw' hp hp' hcode hinput

/-- **The comb is determined by the codes and the commonly read bits.** Let `M` transpose `n × n`
matrices with `b`-bit entries. Let `w` and `w'` be inputs that halt at `T` and `T'`, with pass
partitions `p` and `p'` of `[0, T)` and `[0, T')` into `r` passes. Assume the hypotheses of
`forest_agree` for a segment `[o₁, o₂)` (any `o₁, o₂`). Then `w` and `w'` agree on the segment's
comb (the input bits whose transposed copies lie in the segment). -/
theorem forest_comb_agree {M : TM} {n b T T' r : ℕ} {w w' : List Bool} {p p' : ℕ → ℕ}
    (hcorr : Transposes M n b) (hw : w ∈ matrixInputs n b) (hw' : w' ∈ matrixInputs n b)
    (hT : HaltsAt M w T) (hT' : HaltsAt M w' T')
    (hp : PassPartition M w T r p) (hp' : PassPartition M w' T' r p') {o₁ o₂ : ℕ}
    (hcode : ∀ α ∈ addresses M.k r,
      nodeCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          nodeCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2) ∧
        sideCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          sideCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2))
    (hinput : ∀ d ∈ readSet (inTraj M w) (n * n * b) (forest M w p r o₁ o₂),
      d ∈ readSet (inTraj M w') (n * n * b) (forest M w' p' r o₁ o₂) → nth w d = nth w' d) :
    ∀ d ∈ combSet n b o₁ o₂, nth w d = nth w' d :=
  Impl.forest_comb_agree hcorr hw hw' hT hT' hp hp' hcode hinput

/-- **The information count for data-dependent heads (Kraft form).** Let `M` transpose `n × n`
matrices with `b`-bit entries, `L = n²b`. For every input `v` (a word of length `L`) fix a halting
time `T_v ≤ T` and a pass partition `p_v` of `[0, T_v)` into `r` passes. Fix an output segment
`[o₁, o₂)` (any `o₁, o₂`), and let `U(v)` be the set of input positions read by `v`'s forest of the
segment. Then

  `Σ_v 2^{|comb ∖ U(v)|} ≤ 2^L · ((2T+1)^{k+4} (q+1)(g+1)^k)^𝓗`, where `𝓗 = Σ_{i<r} (k+1)^i`. -/
theorem kraft_group {M : TM} {n b T r : ℕ} (hcorr : Transposes M n b)
    (Tv : (Fin (n * n * b) → Bool) → ℕ) (pv : (Fin (n * n * b) → Bool) → ℕ → ℕ)
    (hTv : ∀ v, Tv v ≤ T) (hhalt : ∀ v, HaltsAt M (List.ofFn v) (Tv v))
    (hpv : ∀ v, PassPartition M (List.ofFn v) (Tv v) r (pv v)) {o₁ o₂ : ℕ} :
    ∑ v, 2 ^ (combSet n b o₁ o₂ \ readSet (inTraj M (List.ofFn v)) (n * n * b)
        (forest M (List.ofFn v) (pv v) r o₁ o₂)).card ≤
      2 ^ (n * n * b) * (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ addrCount M.k r :=
  Impl.kraft_group hcorr Tv pv hTv hhalt hpv

/-- **Theorem P′_γ (any deterministic machine, grouped columns), log-free.** Let `M` transpose
`n × n` matrices with `b`-bit entries. Suppose that on every input it halts within `T` steps and that
its run splits into at most `r` passes. Then for every `γ ≥ 1`

  `2^{n²b} ≤ 2^{𝓗 (γ+1) n b} · ((2T+1)^{k+4} (q+1)(g+1)^k)^{⌈n/γ⌉ 𝓗}`, where `𝓗 = Σ_{i<r} (k+1)^i`. -/
theorem theoremPprime_grouped {M : TM} {n b T r γ : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p)
    (hγ : 1 ≤ γ) :
    2 ^ (n * n * b) ≤
      2 ^ (addrCount M.k r * ((γ + 1) * n * b)) *
        (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ (numGroups n γ * addrCount M.k r) :=
  Impl.theoremPprime_grouped hcorr hrun hγ

/-- **Theorem P′_γ, bits form:** `n²b ≤ 𝓗 ((γ+1) n b + ⌈n/γ⌉ (σ + (k+4)⌈log₂(2T+1)⌉))`, with
`σ = ⌈log₂(q+1)⌉ + k ⌈log₂(g+1)⌉`. -/
theorem theoremPprime_grouped_bits {M : TM} {n b T r γ : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p)
    (hγ : 1 ≤ γ) :
    n * n * b ≤ addrCount M.k r * ((γ + 1) * n * b + numGroups n γ *
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  Impl.theoremPprime_grouped_bits hcorr hrun hγ

/-- **Theorem P′, log-free form.** Let `M` transpose `n × n` matrices with `b`-bit entries,
halting within `T` steps with at most `r` passes on every input. Then

  `2^{n²b} ≤ 2^{2 n b 𝓗} · ((2T+1)^{k+4} (q+1)(g+1)^k)^{n 𝓗}`. -/
theorem theoremPprime {M : TM} {n b T r : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    2 ^ (n * n * b) ≤
      2 ^ (addrCount M.k r * (2 * n * b)) *
        (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ (n * addrCount M.k r) :=
  Impl.theoremPprime hcorr hrun

/-- **Theorem P′, bits form:** `n²b ≤ 𝓗 · n (2b + σ + (k+4)⌈log₂(2T+1)⌉)`. -/
theorem theoremPprime_bits {M : TM} {n b T r : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    n * n * b ≤ addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1)))) :=
  Impl.theoremPprime_bits hcorr hrun

/-- **Theorem P′, per-`n` form:** `n b ≤ 𝓗 (2b + σ + (k+4)⌈log₂(2T+1)⌉)`. -/
theorem theoremPprime_div {M : TM} {n b T r : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    n * b ≤ addrCount M.k r * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  Impl.theoremPprime_div hcorr hrun

/-- **Theorem P′, power form:** `k n b ≤ ((k+1)^r - 1)(2b + σ + (k+4)⌈log₂(2T+1)⌉)`. -/
theorem theoremPprime_pow {M : TM} {n b T r : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    M.k * (n * b) ≤ ((M.k + 1) ^ r - 1) * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  Impl.theoremPprime_pow hcorr hrun

/-- **Theorem P′ with the structure cost `γ = ⌈log₂ r⌉ + 2(k+2)⌈log₂(2T+3)⌉`**: the bound of
Theorem P holds with `σ` replaced by `σ + γ`. The bound is stated in the bits form with `+1`,
`n²b ≤ 𝓗 · (n (2b + σ + γ) + 1)`; for `n, b ≥ 1` it implies the ratio form
`𝓗 ≥ n / (2 + (σ + γ + 1)/b)` (`theoremPprime_ratio`). -/
theorem theoremPprime_gamma {M : TM} {n b T r : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    n * n * b ≤ addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) +
        (Nat.clog 2 r + 2 * (M.k + 2) * Nat.clog 2 (2 * T + 3)))) + 1) :=
  Impl.theoremPprime_gamma hcorr hrun

/-- **Theorem P′ with greedy pass counts**: every input halts within `T` steps and its
greedy pass count is at most `r`. -/
theorem theoremPprime_greedy {M : TM} {n b T r : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, HaltsAt M w T' ∧ greedyPasses M w T' ≤ r) :
    n * n * b ≤ addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1)))) :=
  Impl.theoremPprime_greedy hcorr hrun

/-- **Theorem P′ covers Theorem P's machines.** An oblivious machine with a pass partition of its
common run into `r` passes satisfies the hypotheses of Theorem P′ (with the same `T` and `r`). -/
theorem theoremPprime_hyps_of_oblivious {M : TM} {n b T r : ℕ}
    (hobl : ObliviousOn M (matrixInputs n b) T) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) :
    ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p :=
  Impl.theoremPprime_hyps_of_oblivious hobl hw₀ hp

/-- **Non-vacuity of Theorem P′'s hypotheses with `k = 1`.** `Witness.tr2k` transposes `2 × 2`
matrices with `1`-bit entries, and on every input it halts within `5` steps with a pass partition. -/
theorem theoremPprime_hyps_tr2k : Witness.tr2k.k = 1 ∧ ∃ (T r : ℕ), Transposes Witness.tr2k 2 1 ∧
    ∀ w ∈ matrixInputs 2 1, ∃ T' ≤ T, ∃ p, HaltsAt Witness.tr2k w T' ∧
      PassPartition Witness.tr2k w T' r p :=
  ⟨rfl, 5, _, tr2k_transposes,
    theoremPprime_hyps_of_oblivious tr2k_obliviousOn ⟨_, rfl⟩
      (greedy_passPartition _ (encode 2 1 (fun _ _ _ => false)) 5)⟩

/-- **Non-vacuity with data-dependent running times.** `Witness.tr2dd` transposes `2 × 2` matrices
with `1`-bit entries; its running time is `6` or `5` depending on the first bit, so it is oblivious
for no `T`; and it satisfies the hypotheses of Theorem P′ with `T = 6` and one pass. -/
theorem theoremPprime_hyps_tr2dd : Transposes Witness.tr2dd 2 1 ∧
    (∀ T, ¬ ObliviousOn Witness.tr2dd (matrixInputs 2 1) T) ∧
    ∀ w ∈ matrixInputs 2 1, ∃ T' ≤ 6, ∃ p,
      HaltsAt Witness.tr2dd w T' ∧ PassPartition Witness.tr2dd w T' 1 p :=
  ⟨Impl.tr2dd_transposes, Impl.tr2dd_not_oblivious, Impl.tr2dd_hrun⟩

/-- **The conclusion of Theorem P′ is a real constraint.** A machine with one work tape, at most
`2^8` states and at most `4` work symbols that halts within `2^30` steps on every `1024 × 1024`
input with `10`-bit entries (so `T ≥ L = 10 · 2^20`) cannot transpose with `5` passes. (The same
bound does not exclude `6` passes.) -/
theorem theoremPprime_no_five_pass (M : TM) (hk : M.k = 1) (hq : M.q + 1 ≤ 2 ^ 8)
    (hg : M.g + 1 ≤ 2 ^ 2) (hcorr : Transposes M 1024 10)
    (hrun : ∀ w ∈ matrixInputs 1024 10, ∃ T' ≤ 2 ^ 30, ∃ p,
      HaltsAt M w T' ∧ PassPartition M w T' 5 p) : False :=
  Impl.theoremPprime_no_five_pass M hk hq hg hcorr hrun

/-- **Theorem P′ in ratio form** `𝓗 ≥ n / (2 + (σ + γ + 1)/b)`, for `b ≥ 1`, with
`σ = ⌈log₂(q+1)⌉ + k⌈log₂(g+1)⌉` and `γ = ⌈log₂ r⌉ + 2(k+2)⌈log₂(2T+3)⌉`. -/
theorem theoremPprime_ratio {M : TM} {n b T r : ℕ} (hb : 1 ≤ b)
    (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    ((n : ℝ) / (2 + (((Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) : ℕ) : ℝ) +
        ((Nat.clog 2 r + 2 * (M.k + 2) * Nat.clog 2 (2 * T + 3) : ℕ) : ℝ) + 1) / b))
      ≤ (addrCount M.k r : ℝ) :=
  Impl.theoremPprime_ratio hb hcorr hrun

/-- **Theorem P′ against the frozen statement.** If `M` transposes within `c (L + 1)` steps
(`TransposesWithin`, as in `LinearTimeTransposable`) and every run on `n × n` inputs has at most
`r` greedy passes, then `n²b ≤ 𝓗 · n (2b + σ + (k+4)⌈log₂(2c(L+1)+1)⌉)` with `b = entryBits n`. -/
theorem theoremPprime_linearTime {M : TM} {c : ℕ} (h : TransposesWithin M (fun L => c * (L + 1)))
    {n r : ℕ}
    (hr : ∀ w ∈ matrixInputs n (entryBits n), ∀ T', HaltsAt M w T' → greedyPasses M w T' ≤ r) :
    n * n * entryBits n ≤ addrCount M.k r * (n * (2 * entryBits n +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) +
        (M.k + 4) * Nat.clog 2 (2 * (c * (inputLength n + 1)) + 1)))) :=
  Impl.theoremPprime_linearTime h hr

/-! # The Block Locality Lemma and adaptive machines -/

open MeasureTheory Filter Topology

open scoped ENNReal

/-- **The Locality Lemma, entry form (data-dependent heads, reads from outside `J`).** A variant
of `locality_anchored` (neither implies the other): a cell read at a non-anchor step `τ` may have
been written outside `J`, provided that for some time `a ≤ τ` the cell's contents at time `a` agree
in the two runs, and every visit to the cell during `[a, τ)`, in either run, lies in `J`. -/
theorem locality_entry {M : TM} {w w' : List Bool} {J : Finset ℕ} {A : Set ℕ}
    (hpred : ∀ τ ∈ J, τ ∉ A → 1 ≤ τ ∧ τ - 1 ∈ J)
    (hanchor : ∀ τ ∈ J, τ ∈ A →
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧ headSym M w τ = headSym M w' τ)
    (hread : ∀ τ ∈ J, τ ∉ A → ∀ t : Fin M.k, ∃ a ≤ τ,
      (run M w a).work t (workTraj M w τ t) = (run M w' a).work t (workTraj M w τ t) ∧
      ∀ σ, a ≤ σ → σ < τ →
        (workTraj M w σ t = workTraj M w τ t ∨ workTraj M w' σ t = workTraj M w τ t) → σ ∈ J)
    (hinput : ∀ τ ∈ J, (run M w τ).inPos = (run M w' τ).inPos →
      readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ :=
  Impl.locality_entry hpred hanchor hread hinput

/-- **The Block Locality Lemma.** Let `w`, `w'` be inputs of length `n²b` with the same block-level
trace (slot length `r ≥ 1`, time `T`), and let `J` be the union of the slots of `U`. Suppose they
agree on:
* at each memory boundary `z` of `J`: the state and the positions of all heads at time `z r`, and
  the contents of the blocks resident at slot `z`;
* for each chord entering `J` (source slot outside `U`, target slot `z ∈ U`): the contents of its
  block at time `z r`;
* the input rows touched during `J`.

Then the two runs agree at every step of `J`: same state, head positions, output length, symbols
under the work heads and transition. -/
theorem block_locality {M : TM} {n b r T : ℕ} (hr : 1 ≤ r) {w w' : List Bool}
    (hw : w.length = n * n * b) (hw' : w'.length = n * n * b)
    (htrace : SameTrace M n b r T w w') (U : Set ℕ)
    (hmem : ∀ z ∈ memBoundaries U (numSlots r T),
      (run M w (z * r)).state = (run M w' (z * r)).state ∧
      (run M w (z * r)).inPos = (run M w' (z * r)).inPos ∧
      (run M w (z * r)).workPos = (run M w' (z * r)).workPos ∧
      ∀ (t : Fin M.k) (c : ℤ), blockOf r c ∈ pairRes r (fun τ => workTraj M w τ t) T z →
        (run M w (z * r)).work t c = (run M w' (z * r)).work t c)
    (hchord : ∀ (t : Fin M.k),
      ∀ p ∈ chordsInto (pairRes r (fun τ => workTraj M w τ t) T) U (numSlots r T),
      ∀ c : ℤ, blockOf r c = p.2 → (run M w (p.1 * r)).work t c = (run M w' (p.1 * r)).work t c)
    (hrows : ∀ d < n * n * b, d / (n * b) ∈ srcRows M w n b (slotSteps r U T) →
      nth w d = nth w' d) :
    ∀ τ ∈ slotSteps r U T,
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ :=
  Impl.block_locality hr hw hw' htrace U hmem hchord hrows

/-- **The Cut Lemma on a trace class** (the adaptive Cut Lemma). Let `M`
transpose `n × n` matrices with `b`-bit entries, and let `F` be a trace class (halting time `T`, slot
length `r ≥ 1`, representative `w₀`). For every union `J` of slots, with `S_J = cutPairs`, `μ` its
memory boundaries and `χ` the chords entering it,

  `2^{b |S_J|} · |F| ≤ 2^{n²b} · ((q+1)(2T+1)^{k+1})^μ · (g+1)^{r (3kμ + χ)}`. -/
theorem cut_bound_trace {M : TM} {n b r T : ℕ} (hr : 1 ≤ r) (hcorr : Transposes M n b)
    {F : Set (List Bool)} {w₀ : List Bool} (hF : TraceClass M n b r T F w₀) (U : Set ℕ) :
    2 ^ (b * (cutPairs M w₀ n b (slotSteps r U T)).card) * F.ncard ≤
      2 ^ (n * n * b) *
        (((M.q + 1) * (2 * T + 1) ^ (M.k + 1)) ^ (memBoundaries U (numSlots r T)).card *
          (M.g + 1) ^ (r * (3 * M.k * (memBoundaries U (numSlots r T)).card +
            ∑ t : Fin M.k,
              (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card))) :=
  Impl.cut_bound_trace hr (Impl.classCorrect_of_transposes hcorr hF) hF U

/-- **The Cut Lemma on a trace class, bits form:** if `|F| ≥ 2^{L - D}`, then
`b |S_J| - D ≤ μ (⌈log₂(q+1)⌉ + (k+1)⌈log₂(2T+1)⌉) + r ⌈log₂(g+1)⌉ (3kμ + χ)`. -/
theorem cut_bound_trace_bits {M : TM} {n b r T : ℕ} (hr : 1 ≤ r) (hcorr : Transposes M n b)
    {F : Set (List Bool)} {w₀ : List Bool} (hF : TraceClass M n b r T F w₀) {D : ℕ}
    (hD : 2 ^ (n * n * b) ≤ 2 ^ D * F.ncard) (U : Set ℕ) :
    b * (cutPairs M w₀ n b (slotSteps r U T)).card ≤ D +
      (memBoundaries U (numSlots r T)).card *
          (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1)) +
        r * Nat.clog 2 (M.g + 1) * (3 * M.k * (memBoundaries U (numSlots r T)).card +
          ∑ t : Fin M.k,
            (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card) :=
  Impl.cut_bound_trace_bits hr (Impl.classCorrect_of_transposes hcorr hF) hF hD U

/-- **Discrete Isoperimetry on a trace class (labelled partitions of the slots).** Let the slots
be labelled by `lab`, with at most `m` slots per label, `M_b` label changes and `χ_cross` chords
(of the representative's residency) between different labels. If `|F| ≥ 2^{L - D}`, then

  `(n - M_b)(n - 2m) b ≤ (M_b + 1) D + M_b (⌈log₂(q+1)⌉ + (k+1)⌈log₂(2T+1)⌉)
      + r ⌈log₂(g+1)⌉ (3k M_b + χ_cross)`.

For an oblivious machine (`D = 0`) this is `isoperimetry` in bits, up to the position term. -/
theorem isoperimetry_trace {M : TM} {n b r T : ℕ} (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    (hcorr : Transposes M n b) {F : Set (List Bool)} {w₀ : List Bool}
    (hF : TraceClass M n b r T F w₀) {D : ℕ} (hD : 2 ^ (n * n * b) ≤ 2 ^ D * F.ncard)
    (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    (n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b ≤
      (labelChanges lab (numSlots r T) + 1) * D +
        labelChanges lab (numSlots r T) *
          (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1)) +
        r * Nat.clog 2 (M.g + 1) * (3 * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k,
            (crossChords (pairRes r (fun τ => workTraj M w₀ τ t) T) lab (numSlots r T)).card) :=
  Impl.isoperimetry_trace hr hrnb (Impl.classCorrect_of_transposes hcorr hF) hF hD lab m hm

/-- **Oblivious machines form one trace class** with `D = 0`: all matrix inputs share the
trace, and there are `2^{n²b}` of them. -/
theorem traceClass_of_oblivious {M : TM} {n b r T : ℕ}
    (hobl : ObliviousOn M (matrixInputs n b) T) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) :
    TraceClass M n b r T (matrixInputs n b) w₀ ∧ (matrixInputs n b).ncard = 2 ^ (n * n * b) :=
  Impl.traceClass_of_oblivious hobl hw₀

/-- **An oblivious set is a trace class:** if `M` is oblivious on a set `W` of matrix inputs (time
`T`), then `W` is a trace class, with any member as representative. So the class results (with
`D` the co-entropy of `W`) cover machines oblivious, and correct, only on `W`. -/
theorem traceClass_of_obliviousOn {M : TM} {n b r T : ℕ} {W : Set (List Bool)}
    (hW : W ⊆ matrixInputs n b) (hobl : ObliviousOn M W T) {w₀ : List Bool} (hw₀ : w₀ ∈ W) :
    TraceClass M n b r T W w₀ :=
  Impl.traceClass_of_obliviousOn hW hobl hw₀

/-- **Any member of a trace class is a representative.** -/
theorem traceClass_of_mem {M : TM} {n b r T : ℕ} {F : Set (List Bool)} {w₀ w : List Bool}
    (hF : TraceClass M n b r T F w₀) (hw : w ∈ F) : TraceClass M n b r T F w :=
  Impl.traceClass_of_mem hF hw

/-- **Representative independence:** members of one trace class (slot length `slotLen M n`) have
rescaled work-head trajectories within `4/n` of each other, everywhere. -/
theorem rescaledTrajOf_close {M : TM} {n T : ℕ} (hn : 1 ≤ n) {F : Set (List Bool)}
    {w₀ w : List Bool} (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀) (hw : w ∈ F)
    (t : Fin M.k) (u : ℝ) :
    |rescaledTrajOf M n w t u - rescaledTrajOf M n w₀ t u| ≤ 4 / n :=
  Impl.rescaledTrajOf_close hn hF hw t u

/-- **The limits are class invariants:** along trace classes `F_i`, if the representatives'
rescaled trajectories converge uniformly on a set to `P`, so do those of any members `w'_i ∈ F_i`.
So every conclusion about the limits of the representatives (`theoremMStar_level_class`,
`theoremMStar_level_adaptive`, `theoremMStar_level_robust`) holds for the limits of any members. -/
theorem tendstoUniformlyOn_of_mem {M : TM} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws ws' : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i))
    (hmem : ∀ᶠ i in atTop, ws' i ∈ Fs i) {t : Fin M.k} {P : ℝ → ℝ} {s : Set ℝ}
    (hconv : TendstoUniformlyOn (fun i => rescaledTrajOf M (ns i) (ws i) t) P atTop s) :
    TendstoUniformlyOn (fun i => rescaledTrajOf M (ns i) (ws' i) t) P atTop s :=
  Impl.tendstoUniformlyOn_of_mem hns hF hmem hconv

/-- **The popular trace.** Suppose every matrix input halts
within `T_max` steps, and `1 ≤ r ≤ n b`. Then some trace class `F` (with halting time `T ≤ T_max`)
satisfies `2^{n²b} ≤ traceCount k n ⌈T_max/r⌉ T_max · |F|`. -/
theorem exists_popular_traceClass {M : TM} {n b r Tmax : ℕ} (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T ≤ Tmax, HaltsAt M w T) :
    ∃ T ≤ Tmax, ∃ (F : Set (List Bool)) (w₀ : List Bool), TraceClass M n b r T F w₀ ∧
      2 ^ (n * n * b) ≤ traceCount M.k n (numSlots r Tmax) Tmax * F.ncard :=
  Impl.exists_popular_traceClass hr hrnb hrun

/-- **Theorem M\*, level form, for trace classes.** Along `n_i → ∞`, let `F_i` be trace classes
(slot length `slotLen M n_i`, halting time `T_i ≤ c L_i`, representative `w_i`) with
`2^{L_i} ≤ 2^{D_i} |F_i|` and `D_i / L_i → 0`. If the rescaled trajectories of the representatives
converge uniformly on `[0, c₀]` to `P_t`, the conclusion of `theoremMStar_level` holds for the
limits. -/
theorem theoremMStar_level_class {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts Ds : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i))
    (hD : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard)
    (hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {P : Fin M.k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns i) (ws i) t) (P t) atTop
      (Set.Icc 0 (horizon M c)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (horizon M c))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
      2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) :=
  Impl.theoremMStar_level_class hns hF hD hDL
    ((hF.and hcorr).mono fun _ h => Impl.classCorrect_of_transposes h.2 h.1) htime hconv hS hβ hclass

/-- **Theorem M\* for adaptive machines (popular trace).**
Let `M` transpose `n_i × n_i` matrices, `n_i → ∞`, halting within `c L_i` steps on every input.
Then there are trace classes `F_i` (representatives `w_i`, halting times `T_i ≤ c L_i`) with
`2^{L_i} ≤ 2^{D_i} |F_i|`, `D_i ≤ C n_i b_i` (`C = traceConst M c`) and `D_i / L_i → 0`; some subsequence of the representatives' rescaled
trajectories converges uniformly on `[0, c₀]`; and **every** such subsequential limit is 1-Lipschitz
and satisfies (★) for every `θ`, `S` and `β`. -/
theorem theoremMStar_level_adaptive {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, ∀ w ∈ matrixInputs (ns i) (entryBits (ns i)),
      ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧ HaltsAt M w T) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i) ∧
          (Ts i : ℝ) ≤ c * inputLength (ns i) ∧ 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ traceConst M c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (horizon M c))) ∧
        ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (horizon M c) →
          (∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
          1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
            2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) :=
  Impl.theoremMStar_level_adaptive hns hcorr htime

/-- **The popular trace costs `O(n b)` bits** (`D = O(n log n)`).
For `T_max ≤ c L` and slot length `slotLen M n`, `⌈log₂ traceCount⌉ ≤ C n b` with the explicit
constant `C = traceConst M c`; so the popular class loses `O(1)` blocks per label class. -/
theorem traceBits_le {M : TM} {c : ℝ} {n Tmax : ℕ} (hn : 1 ≤ n)
    (hT : (Tmax : ℝ) ≤ c * inputLength n) :
    Nat.clog 2 (traceCount M.k n (numSlots (slotLen M n) Tmax) Tmax) ≤
      traceConst M c * n * entryBits n :=
  Impl.traceBits_le hn hT

/-- **The frozen (T) supplies the hypotheses of `theoremMStar_level_adaptive`** (with `2c`): a
machine satisfying `TransposesWithin M (fun L => c (L + 1))` transposes at every size and halts within
`2c L` steps on every input, along any `n_i → ∞`. -/
theorem adaptive_hyps_of_linearTime {M : TM} {c : ℕ} (h : TransposesWithin M (fun L => c * (L + 1)))
    {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    (∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i))) ∧
    (∀ᶠ i in atTop, ∀ w ∈ matrixInputs (ns i) (entryBits (ns i)),
      ∃ T : ℕ, (T : ℝ) ≤ ((2 * c : ℕ) : ℝ) * inputLength (ns i) ∧ HaltsAt M w T) :=
  Impl.adaptive_hyps_of_linearTime h hns

/-- **Under (T), the popular-trace limits satisfy (★).** If `LinearTimeTransposable` holds, then some
machine `M` and constant `c` have, along every `n_i → ∞`, popular trace classes with `D = o(L)`; a
subsequence of their representatives' rescaled trajectories converges uniformly; and every
subsequential limit is 1-Lipschitz and satisfies (★) (horizon `horizon M (2c)`). So exhibiting, for
every machine, a sequence along which some popular-trace limit violates (★) would refute (T). -/
theorem linearTimeTransposable_popular_limits (hT : LinearTimeTransposable) :
    ∃ (M : TM) (c : ℕ), ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
        (∀ᶠ i in atTop,
          TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i) ∧
            2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
        Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
          TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
            (Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ)))) ∧
        ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
          (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
            (Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ)))) →
          (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ)))) ∧
          ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
            PiecewiseConstOn β S (horizon M ((2 * c : ℕ) : ℝ)) →
            (∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ)) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
            1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M ((2 * c : ℕ) : ℝ)) p) + 2 * θ +
              2 * M.k * volume (S ∩ Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ))) :=
  Impl.linearTimeTransposable_popular_limits hT

/-- **The offsets-only Block Locality Lemma is false.** There is a correct transposer and two
inputs with the same halting time and block-level trace (`n = b = 1`, `r = 4`, `T = 9`) that agree,
at the memory boundary `z = 2` of `U = {2}`, on everything that a version of the Block Locality
Lemma recording only the work-head offsets requires:
* the state, the input-head position and the work-head offsets;
* the contents of the resident blocks;
* there are no entering chords, and no input row is touched during `J`.

Yet their work heads are in different blocks and their transitions at step 8 differ. -/
theorem block_locality_offsets_counterexample : ∃ (M : TM) (w w' : List Bool),
    Transposes M 1 1 ∧ w ∈ matrixInputs 1 1 ∧ w' ∈ matrixInputs 1 1 ∧
    HaltsAt M w 9 ∧ HaltsAt M w' 9 ∧ SameTrace M 1 1 4 9 w w' ∧
    2 ∈ memBoundaries {2} (numSlots 4 9) ∧
    (run M w 8).state = (run M w' 8).state ∧ (run M w 8).inPos = (run M w' 8).inPos ∧
    (∀ t, (run M w 8).workPos t % 4 = (run M w' 8).workPos t % 4) ∧
    (∀ (t : Fin M.k) (c : ℤ), blockOf 4 c ∈ pairRes 4 (fun τ => workTraj M w τ t) 9 2 →
      (run M w 8).work t c = (run M w' 8).work t c) ∧
    (∀ (t : Fin M.k) (β : ℤ) (x : ℕ), ¬ IsChord (pairRes 4 (fun τ => workTraj M w τ t) 9) β x 2) ∧
    srcRows M w 1 1 (slotSteps 4 {2} 9) = ∅ ∧
    (∃ t, blockOf 4 ((run M w 8).workPos t) ≠ blockOf 4 ((run M w' 8).workPos t)) ∧
    transAt M w 8 ≠ transAt M w' 8 :=
  Impl.block_locality_offsets_counterexample

/-! # Robust forms (M\*): correctness on the class, or on a large set -/

/-- **The Cut Lemma on a trace class, robust form**: `cut_bound_trace` with `M` correct only on
the class `F` (it outputs the transposed encoding at time `T` on every input of `F`), not on all
inputs. -/
theorem cut_bound_trace_on {M : TM} {n b r T : ℕ} (hr : 1 ≤ r)
    {F : Set (List Bool)} {w₀ : List Bool} (hF : TraceClass M n b r T F w₀)
    (hcorr : ∀ w ∈ F, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A)) (U : Set ℕ) :
    2 ^ (b * (cutPairs M w₀ n b (slotSteps r U T)).card) * F.ncard ≤
      2 ^ (n * n * b) *
        (((M.q + 1) * (2 * T + 1) ^ (M.k + 1)) ^ (memBoundaries U (numSlots r T)).card *
          (M.g + 1) ^ (r * (3 * M.k * (memBoundaries U (numSlots r T)).card +
            ∑ t : Fin M.k,
              (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card))) :=
  Impl.cut_bound_trace hr hcorr hF U

/-- **The Cut Lemma on a trace class, bits form, robust**: `cut_bound_trace_bits` with `M`
correct only on the class `F`. -/
theorem cut_bound_trace_bits_on {M : TM} {n b r T : ℕ} (hr : 1 ≤ r)
    {F : Set (List Bool)} {w₀ : List Bool} (hF : TraceClass M n b r T F w₀)
    (hcorr : ∀ w ∈ F, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A)) {D : ℕ}
    (hD : 2 ^ (n * n * b) ≤ 2 ^ D * F.ncard) (U : Set ℕ) :
    b * (cutPairs M w₀ n b (slotSteps r U T)).card ≤ D +
      (memBoundaries U (numSlots r T)).card *
          (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1)) +
        r * Nat.clog 2 (M.g + 1) * (3 * M.k * (memBoundaries U (numSlots r T)).card +
          ∑ t : Fin M.k,
            (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card) :=
  Impl.cut_bound_trace_bits hr hcorr hF hD U

/-- **Discrete Isoperimetry on a trace class, robust form**: `isoperimetry_trace` with `M`
correct only on the class `F`. -/
theorem isoperimetry_trace_on {M : TM} {n b r T : ℕ} (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    {F : Set (List Bool)} {w₀ : List Bool} (hF : TraceClass M n b r T F w₀)
    (hcorr : ∀ w ∈ F, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {D : ℕ} (hD : 2 ^ (n * n * b) ≤ 2 ^ D * F.ncard)
    (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    (n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b ≤
      (labelChanges lab (numSlots r T) + 1) * D +
        labelChanges lab (numSlots r T) *
          (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1)) +
        r * Nat.clog 2 (M.g + 1) * (3 * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k,
            (crossChords (pairRes r (fun τ => workTraj M w₀ τ t) T) lab (numSlots r T)).card) :=
  Impl.isoperimetry_trace hr hrnb hcorr hF hD lab m hm

open Classical in
/-- **The discrete M\* inequality at one size `n`** (finite-`n` form, on a trace class; the inequality
behind `theoremMStar_level_class`, checkable at concrete `n`). Let `F` be a trace class (halting time
`T ≤ c L`, representative `w₀`), with `2^L ≤ 2^D |F|`, on which `M` is correct (it outputs the
transposed encoding at time `T` on every input of `F`). Let `S` be a finite union
of the closed intervals `I`, let `β` be constant on the subintervals of `[0, c₀]` (`c₀ = horizon M c`)
that avoid `S` and the finite set `Z`, and let every label class have measure `≤ θ`. Write
`b = entryBits n`, `N = numSlots (slotLen M n) T`, `G = cellBits M`,
`M_cut = 2 |Impl.mstarBreaks Z I c₀ θ|` (the breakpoints `Z`, the interval endpoints `Impl.endpts I`
and the points `jθ` for `j ≤ ⌈c₀/θ⌉`, one of which may exceed `c₀`) and
`m = ⌊θ n⌋ + 2 |Z ∪ endpts I| + 1`. Then

  `(n - M_cut)(n - 2m) b ≤ (M_cut + 1) D + M_cut (k+1)⌈log₂(2T+1)⌉ + M_cut ⌈log₂(q+1)⌉
      + (n b + G)(3k M_cut + Σ_t χ'_t)`,

where `χ'_t = M_cut (⌈η n⌉ + 1) + 2 #{y < N : y/n ∈ S} + |𝒳_t|` and `𝒳_t = longCross` counts the long
chords (gap `≥ η n`) of tape `t` with both ends off `S` and different labels `β(y/n)`. (The proof
applies the cut inequality of Discrete Isoperimetry to the slot labelling `2 β(y/n)` off `S`, fresh
odd labels `2⌊(y/n)/θ⌋ + 1` on `S`; this labelling does not appear in the statement.) -/
theorem mstar_discrete_class_on {M : TM} {n T : ℕ} {c θ η : ℝ} (hθ : 0 < θ)
    {F : Set (List Bool)} {w₀ : List Bool}
    (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀) {D : ℕ}
    (hD : 2 ^ (n * n * entryBits n) ≤ 2 ^ D * F.ncard)
    (hcorr : ∀ w ∈ F, ∃ A : Matrix, w = encode n (entryBits n) A ∧
      (run M w T).outRev.reverse = encode n (entryBits n) (transpose A))
    (htime : (T : ℝ) ≤ c * inputLength n)
    {S : Set ℝ} {I : Finset (ℝ × ℝ)} (hSI : S = ⋃ x ∈ I, Set.Icc x.1 x.2) {β : ℝ → ℕ}
    {Z : Finset ℝ}
    (hβZ : ∀ u v, 0 ≤ u → u ≤ v → v ≤ horizon M c →
      (∀ x ∈ Set.Icc u v, x ∉ S ∧ x ∉ (Z : Set ℝ)) → β u = β v)
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤
      ENNReal.ofReal θ) :
    (n - 2 * (Impl.mstarBreaks Z I (horizon M c) θ).card) *
        (n - 2 * (⌊θ * n⌋₊ + 2 * (Z ∪ Impl.endpts I).card + 1)) * entryBits n ≤
      (2 * (Impl.mstarBreaks Z I (horizon M c) θ).card + 1) * D +
      2 * (Impl.mstarBreaks Z I (horizon M c) θ).card * ((M.k + 1) * Nat.clog 2 (2 * T + 1)) +
      2 * (Impl.mstarBreaks Z I (horizon M c) θ).card * Nat.clog 2 (M.q + 1) +
        (n * entryBits n + cellBits M) *
          (3 * M.k * (2 * (Impl.mstarBreaks Z I (horizon M c) θ).card) +
          ∑ t : Fin M.k, (2 * (Impl.mstarBreaks Z I (horizon M c) θ).card * (⌈η * n⌉₊ + 1) +
            2 * ((Finset.range (numSlots (slotLen M n) T)).filter
              (fun y : ℕ => (y : ℝ) / n ∈ S)).card +
            (longCross (pairRes (slotLen M n) (fun τ => workTraj M (w₀) τ t) T) S β n η
              (numSlots (slotLen M n) T)).card)) :=
  Impl.mstar_discrete_class hθ hF hD hcorr htime hSI hβZ hclass

/-- **Theorem M\*, level form, for trace classes, robust form**: `theoremMStar_level_class` with
`M` correct only on the classes `F_i` (it outputs the transposed encoding at time `T_i` on every input
of `F_i`), eventually. -/
theorem theoremMStar_level_class_on {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts Ds : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i))
    (hD : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard)
    (hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ∀ w ∈ Fs i, ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
      (run M w (Ts i)).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {P : Fin M.k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns i) (ws i) t) (P t) atTop
      (Set.Icc 0 (horizon M c)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (horizon M c))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
      2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) :=
  Impl.theoremMStar_level_class hns hF hD hDL hcorr htime hconv hS hβ hclass

/-- **Theorem M\* for non-uniform machines on trace classes** (the non-uniform generalization of
`theoremMStar_level_class_on`, with subsequences). At sizes `n_i → ∞`, let `M_i` be machines with
`k` work tapes and `G` bits per cell (`cellBits M_i = G`), any transition tables and state bits
`⌈log₂(q_i+1)⌉ = o(L_i)`, and let `F_i` be trace classes of `M_i` (halting time `T_i ≤ c L_i`,
representative `w_i`) with `2^{L_i} ≤ 2^{D_i} |F_i|` and `D_i / L_i → 0`, on which `M_i` is
correct, eventually. Then the representatives' rescaled trajectories have a uniformly convergent
subsequence on `[0, c₀]`, `c₀ = c G + 1`, and every subsequential limit is 1-Lipschitz and
satisfies (★). The tapes of `M_i` are indexed by `Fin k` through `M_i.k = k`. This is the one
route from machines to codes (`diagram_of_class`); `theoremMStar_level_class_on` is its case of
one machine and `φ = id`. -/
theorem theoremMStar_class_nonuniform {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ts Ds : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i))
    (hD : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard)
    (hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ∀ w ∈ Fs i, ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
      (run (Ms i) w (Ts i)).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
        (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
        (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
      ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (c * G + 1) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
          2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) :=
  Impl.theoremMStar_class_nonuniform hns hk hG hq hF hD hDL hcorr htime

/-- **No stationary limits for trace classes.** Along trace classes with `D = o(L)` (for example the
popular ones) on which `M` is correct, eventually, the representatives' rescaled work-head
trajectories cannot all converge uniformly to `0`. -/
theorem no_stationary_limits_class_on {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts Ds : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i))
    (hD : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard)
    (hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ∀ w ∈ Fs i, ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
      (run M w (Ts i)).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) :
    ¬ ∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns i) (ws i) t) (fun _ => 0) atTop
      (Set.Icc 0 (horizon M c)) :=
  Impl.no_stationary_limits_class hns hF hD hDL hcorr htime

/-- **Theorem M\* for machines fast and correct on a set of co-entropy `o(L)`** (robust adaptive
M\*). Let `M`, at sizes `n_i → ∞`, halt within `c L_i` steps with the transposed output on every input
of a set `W_i` (necessarily of matrix inputs) with `2^{L_i} ≤ 2^{m_i} |W_i|` and `m_i / L_i → 0`,
eventually; on the other inputs it may err or run long. Then there are trace classes `F_i ⊆ W_i` (representatives `w_i`, halting
times `T_i ≤ c L_i`) with `2^{L_i} ≤ 2^{D_i} |F_i|`, `D_i ≤ m_i + C n_i b_i` (`C = traceConst M c`) and
`D_i / L_i → 0`; some subsequence of the representatives' rescaled trajectories converges uniformly
on `[0, c₀]`; and **every** such subsequential limit is 1-Lipschitz and satisfies (★) for every `θ`,
`S` and `β`. With `W_i` all matrix inputs and `m_i = 0` this is `theoremMStar_level_adaptive`. -/
theorem theoremMStar_level_robust {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt M w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run M w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ ms i + traceConst M c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (horizon M c))) ∧
        ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (horizon M c) →
          (∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
          1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
            2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) :=
  Impl.theoremMStar_level_robust hns hm hmL hfast

/-- **Theorem M\* for non-uniform machines fast and correct on a set of co-entropy `o(L)`.** At sizes
`n_i → ∞`, let `M_i` be machines with `k` work tapes and `G` bits per cell (`cellBits M_i = G`), with any
transition tables and any state counts with `⌈log₂(q_i+1)⌉ = o(L_i)`, and let `M_i` halt within
`c L_i` steps with the transposed output on every input of a set `W_i` with `2^{L_i} ≤ 2^{m_i} |W_i|`
and `m_i / L_i → 0`, eventually. Then there are trace classes `F_i ⊆ W_i` (representatives `w_i`,
halting times `T_i ≤ c L_i`) with `2^{L_i} ≤ 2^{D_i} |F_i|`, `D_i ≤ m_i + C n_i b_i`
(`C = traceConst M_0 c`: all `traceConst M_i c` are equal, as they depend on `k`, `G` and `c` only)
and `D_i / L_i → 0`; some
subsequence of the representatives' rescaled trajectories converges uniformly on `[0, c₀]`,
`c₀ = c G + 1`; and every such subsequential limit is 1-Lipschitz and satisfies (★). The tapes of
`M_i` are indexed by `Fin k` through `M_i.k = k`. `theoremMStar_level_robust` is the case of one
machine; the proof applies Theorem M\* for code-carrying diagrams
(`Transpose/Tape/Statements/Coding.lean`) to the popular class codes. -/
theorem theoremMStar_level_nonuniform {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt (Ms i) w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ ms i + traceConst (Ms 0) c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
        ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (c * G + 1) →
          (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
          1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
            2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) :=
  Impl.theoremMStar_level_nonuniform hns hk hG hq hm hmL hfast

/-- **Labelling-free non-uniform M\*.** Under the hypotheses of `theoremMStar_level_nonuniform`,
every subsequential limit `P` of the popular representatives' rescaled trajectories has total excess
level multiplicity `Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1` and total range `1 + Σ_t |P_t([0, c₀])| ≤ k c₀`
(`c₀ = c G + 1`), and its paths are not all monotone. `theoremMStar_excess_robust` is its case of
one machine. -/
theorem theoremMStar_excess_nonuniform {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt (Ms i) w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ ms i + traceConst (Ms 0) c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) →
        1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (c * G + 1) p ∧
          1 + ∑ t, volume (P t '' Set.Icc 0 (c * G + 1)) ≤ k * ENNReal.ofReal (c * G + 1) ∧
          ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (c * G + 1)) ∨
            AntitoneOn (P t) (Set.Icc 0 (c * G + 1)) :=
  Impl.theoremMStar_excess_nonuniform hns hk hG hq hm hmL hfast

/-- **Labelling-free robust M\*.** Under the hypotheses of `theoremMStar_level_robust`, every
subsequential limit `P` of the popular representatives' rescaled trajectories has total excess level
multiplicity `Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1` and total range `1 + Σ_t |P_t([0, c₀])| ≤ k c₀`
(`c₀ = horizon M c`), and its paths are not all monotone (see `one_le_excess_of_star`,
`range_add_one_le_of_star` and `not_all_monotone_of_star`); the case of one machine of
`theoremMStar_excess_nonuniform`. -/
theorem theoremMStar_excess_robust {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt M w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run M w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) →
        1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (horizon M c) p ∧
          1 + ∑ t, volume (P t '' Set.Icc 0 (horizon M c)) ≤ M.k * ENNReal.ofReal (horizon M c) ∧
          ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (horizon M c)) ∨
            AntitoneOn (P t) (Set.Icc 0 (horizon M c)) :=
  Impl.theoremMStar_excess_robust hns hm hmL hfast

/-! # Robust forms (P′): correctness on a large set -/

/-- **The comb is determined by the codes and the commonly read bits, robust form**:
`forest_comb_agree` with `M` correct only on `w` and `w'` (each is the encoding of a matrix, and the
output at the end `T`, `T'` of its pass partition is the transposed encoding). No halting is
assumed, and the segment `[o₁, o₂)` is arbitrary. -/
theorem forest_comb_agree_on {M : TM} {n b T T' r : ℕ} {w w' : List Bool} {p p' : ℕ → ℕ}
    (hcw : ∃ A : Matrix, w = encode n b A ∧ (run M w T).outRev.reverse = encode n b (transpose A))
    (hcw' : ∃ A : Matrix, w' = encode n b A ∧
      (run M w' T').outRev.reverse = encode n b (transpose A))
    (hp : PassPartition M w T r p) (hp' : PassPartition M w' T' r p') {o₁ o₂ : ℕ}
    (hcode : ∀ α ∈ addresses M.k r,
      nodeCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          nodeCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2) ∧
        sideCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          sideCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2))
    (hinput : ∀ d ∈ readSet (inTraj M w) (n * n * b) (forest M w p r o₁ o₂),
      d ∈ readSet (inTraj M w') (n * n * b) (forest M w' p' r o₁ o₂) → nth w d = nth w' d) :
    ∀ d ∈ combSet n b o₁ o₂, nth w d = nth w' d :=
  Impl.forest_comb_agree_on hcw hcw' hp hp' hcode hinput

/-- **The Kraft count on a set of inputs** (robust form of `kraft_group`). For every input `v` of a
set `V` fix a time `T_v ≤ T` and a pass partition `p_v` of `[0, T_v)` into `r` passes, and let `M` be
correct on `v` at that time (its output at time `T_v` is the transposed encoding; no halting is
assumed). Fix an output segment
`[o₁, o₂)` (any `o₁, o₂`), and let `U(v)` be the set of input positions read by `v`'s forest of the
segment. Then `Σ_{v ∈ V} 2^{|comb ∖ U(v)|} ≤ 2^L · ((2T+1)^{k+4} (q+1)(g+1)^k)^𝓗`, `L = n²b`. -/
theorem kraft_group_on {M : TM} {n b T r : ℕ} (V : Finset (Fin (n * n * b) → Bool))
    (Tv : (Fin (n * n * b) → Bool) → ℕ) (pv : (Fin (n * n * b) → Bool) → ℕ → ℕ)
    (hTv : ∀ v ∈ V, Tv v ≤ T)
    (hpv : ∀ v ∈ V, PassPartition M (List.ofFn v) (Tv v) r (pv v))
    (hcv : ∀ v ∈ V, ∃ A : Matrix, List.ofFn v = encode n b A ∧
      (run M (List.ofFn v) (Tv v)).outRev.reverse = encode n b (transpose A))
    {o₁ o₂ : ℕ} :
    ∑ v ∈ V, 2 ^ (combSet n b o₁ o₂ \ readSet (inTraj M (List.ofFn v)) (n * n * b)
        (forest M (List.ofFn v) (pv v) r o₁ o₂)).card ≤
      2 ^ (n * n * b) * (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ addrCount M.k r :=
  Impl.kraft_group_on V Tv pv hTv hpv hcv

/-- **Theorem P′_γ on a set of co-entropy `≤ m` (robust P′), log-free.** Let `M` (data-dependent
heads) have, on every input of a set `W` with `2^{n²b} ≤ 2^m |W|`, the transposed output at some time
`T' ≤ T` and a partition of `[0, T')` into `r` passes (correctness forces `W ⊆ matrixInputs n b`; `M`
need not halt at `T'`); on other inputs it may err, run long or use more passes. Then for every
`γ ≥ 1`

  `2^{n²b} ≤ 2^{⌈n/γ⌉ m} · 2^{𝓗 (γ+1) n b} · ((2T+1)^{k+4} (q+1)(g+1)^k)^{⌈n/γ⌉ 𝓗}`:

every group of `γ` columns pays `m` bits. -/
theorem theoremPprime_grouped_on {M : TM} {n b T r γ : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    (hγ : 1 ≤ γ) {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (n * n * b) ≤
      2 ^ (numGroups n γ * m) * (2 ^ (addrCount M.k r * ((γ + 1) * n * b)) *
        (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ (numGroups n γ * addrCount M.k r)) :=
  Impl.theoremPprime_grouped_on hrun hγ hco

/-- **Theorem P′_γ on a set, bits form**:
`n² b ≤ ⌈n/γ⌉ m + 𝓗 ((γ+1) n b + ⌈n/γ⌉ (σ + (k+4)⌈log₂(2T+1)⌉))`. -/
theorem theoremPprime_grouped_on_bits {M : TM} {n b T r γ : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    (hγ : 1 ≤ γ) {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ numGroups n γ * m + addrCount M.k r * ((γ + 1) * n * b + numGroups n γ *
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  Impl.theoremPprime_grouped_on_bits hrun hγ hco

/-- **Theorem P′ on a set of co-entropy `≤ m`, log-free** (`γ = 1`). -/
theorem theoremPprime_on {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (n * n * b) ≤
      2 ^ (n * m) * (2 ^ (addrCount M.k r * (2 * n * b)) *
        (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ (n * addrCount M.k r)) :=
  Impl.theoremPprime_on hrun hco

/-- **Theorem P′ on a set, bits form**: `n² b ≤ n m + 𝓗 n (2b + σ + (k+4)⌈log₂(2T+1)⌉)`. -/
theorem theoremPprime_on_bits {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ n * m + addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1)))) :=
  Impl.theoremPprime_on_bits hrun hco

/-- **Theorem P′ on a set of co-entropy `≤ C n`, per-`n` form**:
`n b ≤ C n + 𝓗 (2b + σ + (k+4)⌈log₂(2T+1)⌉)`. So if `(k+4)⌈log₂(2T+1)⌉ ≤ c' b`, co-entropy `O(n)`
still forces `𝓗 ≥ n (b − C) / ((2 + c') b + σ)`. -/
theorem theoremPprime_on_div {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {C : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * n) * W.ncard) :
    n * b ≤ C * n + addrCount M.k r * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  Impl.theoremPprime_on_div hrun hco

/-- **Theorem P′ on a set of co-entropy `≤ C n`, power form**:
`k n b ≤ k C n + ((k+1)^r − 1)(2b + σ + (k+4)⌈log₂(2T+1)⌉)`. -/
theorem theoremPprime_on_pow {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {C : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * n) * W.ncard) :
    M.k * (n * b) ≤ M.k * (C * n) + ((M.k + 1) ^ r - 1) * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  Impl.theoremPprime_on_pow hrun hco

/-- **Theorem P′ at the robust co-entropy level `C n b`** (grouping `γ = 2C`): if `M` is correct, fast
and `r`-pass on a set `W` with `2^{n²b} ≤ 2^{C n b} |W|`, then
`C n b ≤ 2C² b + 𝓗 (2C(2C+1) b + 2σ′)` with `σ′ = σ + (k+4)⌈log₂(2T+1)⌉`. If
`(k+4)⌈log₂(2T+1)⌉ ≤ c' b` (e.g. `T ≤ poly(L)` and `b = ⌈log₂ n⌉`, or any `b = Ω(log n)`), this gives
`𝓗 ≥ (C n − 2C²) b / (2C(2C+1) b + 2σ′)`: still `log_{k+1} n − O(log(C + c'))` passes, as for
Theorem P (`theoremP_on_robust`; here the structure term is `Θ(b)` for `b = ⌈log₂ n⌉`, since
`T ≥ L`). -/
theorem theoremPprime_on_robust {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {C : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * (n * b)) * W.ncard) :
    C * (n * b) ≤ 2 * C * C * b + addrCount M.k r * (2 * C * (2 * C + 1) * b +
      2 * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) +
        (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  Impl.theoremPprime_on_robust hrun hco

/-- **Theorem P′ at the robust co-entropy level `C n b`, any grouping `γ ≥ 1`:**
`(γ − C) n² b ≤ γ C n b + 𝓗 (γ(γ+1) n b + (n + γ) σ′)`, `σ′ = σ + (k+4)⌈log₂(2T+1)⌉`. Optimizing
`γ` improves the constant of `theoremPprime_on_robust` (`γ = 2C`). -/
theorem theoremPprime_on_robust_gamma {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {C γ : ℕ} (hγ : 1 ≤ γ) (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * (n * b)) * W.ncard) :
    (γ - C) * (n * n * b) ≤ γ * C * (n * b) + addrCount M.k r * (γ * (γ + 1) * (n * b) +
      (n + γ) * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) +
        (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  Impl.theoremPprime_on_robust_gamma hrun hγ hco

/-- **Theorem P′ on a set, with greedy pass counts.** -/
theorem theoremPprime_on_greedy {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, greedyPasses M w T' ≤ r ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ n * m + addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1)))) :=
  Impl.theoremPprime_on_greedy hrun hco

end Transpose.Tape
