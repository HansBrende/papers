import Transpose.Tape.CEMain
import Transpose.Tape.CEEquiv
import Transpose.Tape.CEProfile
import Transpose.Tape.CESweep
import Transpose.Tape.CEForms
import Transpose.Tape.CEHint
import Transpose.Tape.CoarseTrace
import Transpose.Tape.CERungs
import Transpose.Tape.MStarCoding

/-!
# Statements: the Tape Coding Conjecture

Definitions: `DefsCE.lean`. Everything here is kernel-checked.

## The conjecture as a formal target

Block networks of `k`-tape time–space diagrams of length `O(L)` carry complete bipartite exchange.
* **CE_TM**: with independent uniform sources, their network-coding rate is at most `γ(n)` times
  their multicommodity-flow rate, for some `γ(n) = o(log n)`.
* **Robust CE_TM**: the same, for sources uniform on any set of inputs of co-entropy `O(n log n)`.

The **Tape Coding Conjecture** is the robust target. Its no-code form is `RobustNoCode_TM`: for all
constants and all large `n`, no causal code solves complete exchange at the profile capacities on a
set of inputs of co-entropy `≤ C n w`. Its flow form is `RobustCE_TM` and its distance (volume) form
is `RobustCE_TM_dist`. The plain forms, for independent uniform sources (all inputs), are
`NoCode_TM`, `CE_TM` and `CE_TM_dist`.

**Remarks on the formal statement.** Each of the following makes the formal conjecture weaker or
equal at every `k`, so a proof of the informal conjecture proves the formal one:
* Sinks are per bit: output bit `o` is decoded at the slot that appends it.
* Sources are multi-homed and see whole rows: a node sees every row its input walk touches.
* Codes are one-shot and zero-error.
* Several chords between the same two slots form one edge, of capacity one block per tape.
* The memory profile is per node (the resident blocks, at most `3k`), with no extra bits.

## The one-way reduction

**No code refutes (T)**: `not_linearTimeTransposable_of_robustNoCode`, and hence
`not_linearTimeTransposable_of_robustCE_TM` and `not_linearTimeTransposable_of_robustCE_TM_dist`.
A proof of any of the forms plugs into the final answer as
`theorem answer : ¬ LinearTimeTransposable := not_linearTimeTransposable_of_robustCE_TM h`.
**A refutation does not decide (T)**: it gives codes for infinitely many `n` with fixed constants,
but no machine, and no converse is proved. Positively, **(T) gives codes**:
`codes_coentLinear_of_linearTimeTransposable` gives explicit constants and, for every large `n`, a
code at co-entropy `O(n)` on the buffered machine's diagram, which appends its output in its last
`L` steps (`codes_of_linearTimeTransposable`: the form of `RobustNoCode_TM`).

The reduction (`codes_of_fastOn`):
* The popular trace within the inputs the machine handles fast gives a trace class of co-entropy
  `O(n w)` (`exists_popular_traceClass_on`, `traceBits_le`).
* `traceClass_code` (the Block Locality Lemma in functional form) turns the class into a causal code
  on the block network of its representative's run (`runDiagram`). A memory edge `y → y+1` carries
  what slot `y` can compute:
  - the state and the head positions at time `(y+1) r`;
  - the contents at that time of the blocks resident at slot `y` (`R_y`).

  A block of `R_{y+1} ∖ R_y` arrives by the chord from its previous visit, or was never visited and
  is blank. A chord edge carries one block per tape having that chord.
* This is the only step from a class to a code (`codes_of_fastOn_bits`): the code lives on the run's
  own diagram at the per-node blocks plus `s` bits per memory edge, `s` = state bits + `O(log n)`
  bits of head positions. Every other profile follows by TM-free conversions: a stationary tape
  changes nothing in the block network and its resident block carries the extra bits
  (`solves_profileCap_addTapes`, giving `codes_of_fastOn` on `k + 1` tapes at the per-node profile),
  and `robustNoCode_bits_iff`.

**Why the memory edges carry the state and head positions.** This concerns the reduction, not the
target. On a trace class (adaptive machines) the head positions vary with the input, so the
simulation of a run (the code built from it) needs `O(log n)` bits per memory edge beyond the
resident blocks; whether some other code fits `3k` blocks plus `O(1)` bits there is unproven. For
oblivious machines the positions are fixed, and "`3k` blocks plus `O(1)` bits of state" suffices.

## Equivalent forms

**The forms are equivalent** (collected in `robust_tfae` and `plain_tfae`):
`robustCE_TM_iff_robustNoCode` (flow form), `robustCE_TM_dist_iff_robustNoCode` (distance form),
and the same for the plain forms (`ce_TM_iff_noCode`, `ce_TM_dist_iff_noCode`). The γ-form is
equivalent too (`robustCE_TM_gamma_iff`, `robustCE_TM_gamma_per_iff`). The reason is a property of
the networks alone, `volume_gap`. In a block network almost every input bit is `Ω(log n)` hops from
its sink, while the capacities sum to `O(L)`. So the volume bound caps the flow rate at
`O(1/log n)`, while a code solving complete exchange has rate `1` (`code_gap`). "Coding beats flow
by `o(log n)`" therefore says exactly that **no code exists for large `n`**. Even the gain bound
`log₂ n / E(k, G, c)`, with an explicit `E` and needed only at the profile capacities, suffices
(`robustNoCode_of_gainBound`).

**The memory profile is immaterial.** `RobustNoCode_TM` is stated at the per-node profile
capacities (`profileCap`): a memory edge carries the blocks resident at its source slot, a chord
edge one block per tape. Since `Solves` is monotone in the capacities, this is the same as ruling
out codes within every `cap` in the profile (`robustNoCode_iff_forall_cap`; `noCode_iff_forall_cap`
for the plain form). It is equivalent to:
- "no code" with any uniform profile of `m` blocks per memory edge, for any `m` with
  `3k ≤ m(k + a)` for some `a` (`robustNoCode_with_iff`), e.g. `m(k) ≥ 3k` or one block per tape
  (`robustNoCode_with_k_iff`). This includes `m(k) = 3k` (no extra bits) and `m(k) = 3k + 1`; the
  informal profile of `3k` blocks plus `O(1)` (or `O(log n)`) bits lies between these two for
  large `n`;
- "no code" with `s(k, n) ≤ C(k) n w` (for `n ≥ 1`) extra bits per memory edge
  (`robustNoCode_bits_iff`), e.g. the `O(log n)` bits `(3k + 4)⌈log₂ n⌉`
  (`robustNoCode_logBits_iff`).

Adding stationary tapes trades extra blocks or bits for tapes. Moreover one may assume that the
input walk attaches every row (`robustNoCode_iff_attached`; append an input sweep). On such diagrams
the flow form (`RobustCE_TM_att`) needs no convention for rows without a source node, and it is
again equivalent (`robustCE_TM_att_iff`).

## Consequences for non-uniform and average-case machines

* `linearTime_fails_of_robustNoCode`: every machine fails at **every** large `n`.
* `no_fast_transposer_of_robustNoCode`: for all large `n`, no machine with `k` tapes and alphabet
  `g + 1` transposes correctly within `c L` steps, even if its transition table depends on `n` and
  it has up to `2^{C₁ n w}` states (any constant `C₁`), and even if it only has to handle a set of
  `2^{L - C₀ n w}` inputs.
* With `s` extra bits per memory edge, directly: the target at `s` rules out every machine family
  whose state bits plus head-position bits fit in `s` (`no_fast_transposer_of_robustNoCode_bits`).
  Already `s(k, n) = (3k + 4)⌈log₂ n⌉` bits refute every fixed machine
  (`linearTime_fails_of_robustNoCode_logBits`).
* One non-uniform theorem for every co-entropy level (`no_fast_transposer_of_coent`), and what each
  rung of the ladder rules out (`traceClass_coent_lt`).

`F₀ ⊆ matrixInputs` is not a hypothesis of the `no_fast_transposer_*` theorems, nor of
`codes_of_fastOn` and `codes_of_fastOn_bits` (correctness implies it).

## The co-entropy ladder

`NoCode_TM_coent m` runs from the plain target (`m = 0`, `noCode_iff_coent_zero`) to the robust one
(`m = C n w`, `robustNoCode_iff_coent`). **Co-entropy `O(n)` suffices**
(`not_linearTimeTransposable_of_coentLinear`): ruling out codes on sets of co-entropy `C n`, rather
than `C n w`, for every `C` already refutes (T), and every machine then fails at every large `n`
(`linearTime_fails_of_coentLinear`). The machine is first made to output only at the end
(`bufTM_run`); its coarse trace, plus the halting time, then costs `O(1)` bits per slot and
determines the block-level trace. This hypothesis is implied by `RobustNoCode_TM` and implies
`NoCode_TM`. The consequences of `RobustNoCode_TM` above are proved as corollaries of these
co-entropy-`O(n)` forms. Moreover:
* any single superlinear level suffices (`not_linearTimeTransposable_of_coent`), e.g. `n w`
  (`not_linearTimeTransposable_of_coent_nw`);
* the target may assume the output comes in the last `L` steps
  (`not_linearTimeTransposable_of_coentLinear_end`; `NoCode_TM_coent_end`);
* the flow form at co-entropy `C n` is the linear rung (`robustCE_TM_lin_iff`), so it refutes (T)
  (`not_linearTimeTransposable_of_robustCE_TM_lin`).

## Robust versus plain

The robust target is exactly the plain target with an uncharged (oracle) `O(n w)`-bit hint
(`robustNoCode_iff_hint`; per diagram `code_of_hint`, `hint_of_code`), while a side channel of that
size whose contents the code computes itself is free (`noCode_bits_iff`). An `O(n)`-bit oracle hint
already suffices to refute (T) (`not_linearTimeTransposable_of_noCode_hintLinear`,
`hintLinear_iff_coentLinear`). (T) gives hint codes on all inputs
(`hintCodes_of_linearTimeTransposable`; with an `O(n)`-bit hint,
`hintCodes_linear_of_linearTimeTransposable`). Whether plain implies robust stays open; partial
results towards it are in `Transpose/Tape/Statements/PlainRobust.lean` and
`Transpose/Tape/PlainRobust/`.

## Infinitely many sizes suffice

Since (T) gives codes at every large `n`, no code for infinitely many `n` already refutes (T)
(`not_linearTimeTransposable_of_robustNoCode_io`; flow form `…_robustCE_TM_io`). The three robust
infinitely-often forms are equivalent (`robust_io_tfae`). Moreover:
* one superlinear co-entropy level for **infinitely many** `n` suffices
  (`not_linearTimeTransposable_of_coent_io`; `NoCode_TM_coent_io`); by a diagonal argument this
  single level is equivalent to the linear io family of
  `not_linearTimeTransposable_of_coentLinear_io` (`coentLinear_io_iff_exists_coent_io`);
* output at the end and infinitely many `n` suffice together
  (`not_linearTimeTransposable_of_coentLinear_end_io`; `NoCode_TM_coent_end_io`), which gives the
  output-at-end form and the linear io form as corollaries.

## Oblivious machines

`NoCode_TM` (equivalently `CE_TM`) refutes oblivious (T)
(`not_obliviousLinearTimeTransposable_of_noCode`, `not_obliviousLinearTimeTransposable_of_ce_TM`),
already for infinitely many `n` (`not_obliviousLinearTimeTransposable_of_noCode_io`).

## The cut-set bound and the code gap

Lower-bound tools for any code-carrying diagram (TM-free): the cut-set bound at the bit level
(`cutset_bound_bitwise`; its cut at all nodes is `card_le_of_solves`) and its entry form
`cutset_bound`, Discrete Isoperimetry `isoperimetry_code`, the code gap `code_gap` (a solving code
beats the volume bound by a factor `Ω(log n)`) and the rate bound `flow_rate_lt` (every routing has
rate `< E/w`). They constrain every counterexample to `RobustNoCode_TM`; with `traceClass_code`
(`code_bits_of_class`) they give the machine forms of Discrete Isoperimetry used by Theorem M\*
(`cutIneq_of_solves`).

## Theorem M* for code-carrying diagrams

Proofs in `MStarWalk.lean`, `MStarDiagram.lean` and `MStarCoding.lean`. Every family of valid
diagrams carrying codes at the profile capacities plus `o(L)` bits per memory edge, on sets of
co-entropy `o(L)`, has rescaled work walks with convergent subsequences, and every limit satisfies
(★) (`theoremMStar_diagram`). In particular **every family of counterexamples to the Tape Coding
Conjecture satisfies (★)**, and its limits are not monotone on every tape
(`mstar_of_robustNoCode_counterexamples`); if the conjecture fails, such families exist
(`mstar_of_not_robustNoCode`). The core is TM-free: Theorem M\* for any walks satisfying the cut
inequality of Discrete Isoperimetry, with unit steps only before `T` and no condition on `G`
(`theoremMStar_walk`, the most general form; `theoremMStar_level_walk` is its level form). The
machine versions (oblivious, trace class, adaptive, robust, non-uniform) are corollaries.
-/

namespace Transpose.Tape

open Transpose TSDiagram

/-! ## Robust CE_TM implies ¬(T) -/

/-- **No code refutes (T).** If, for all large `n`, no causal code solves complete exchange within the
block profile on sets of inputs of co-entropy `O(n w)`, then no machine transposes in linear time.
This is the cleanest target: a proof shows that no code exists. A refutation gives codes for
infinitely many `n`, but no machine, so it does not decide (T). -/
theorem not_linearTimeTransposable_of_robustNoCode (h : RobustNoCode_TM) :
    ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_coentLinear (Impl.coentLinear_of_robustNoCode h)

/-- **Robust CE_TM implies ¬(T)** (the flow form). A proof of the conjecture plugs into
the final answer as
`theorem answer : ¬ LinearTimeTransposable := not_linearTimeTransposable_of_robustCE_TM h`. -/
theorem not_linearTimeTransposable_of_robustCE_TM (h : RobustCE_TM) : ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_robustNoCode
    (Impl.robustNoCode_of_robustCE_TM_dist (Impl.robustCE_TM_dist_of_robustCE_TM h))

/-- **Robust CE_TM, distance form, implies ¬(T).** -/
theorem not_linearTimeTransposable_of_robustCE_TM_dist (h : RobustCE_TM_dist) :
    ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_robustNoCode (Impl.robustNoCode_of_robustCE_TM_dist h)

/-- **Every machine fails at every large size.** Under `RobustNoCode_TM`, for every machine `M` and
constant `c`, for all large `n` some `n × n` matrix is not transposed within `c (L + 1)` steps. ¬(T)
only says that this happens for some `n`. -/
theorem linearTime_fails_of_robustNoCode (h : RobustNoCode_TM) (M : TM) (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ¬ ∀ A : Matrix,
      ComputesWithin M (encode n (entryBits n) A) (encode n (entryBits n) (transpose A))
        (c * (inputLength n + 1)) :=
  Impl.linearTime_fails_of_coentLinear (Impl.coentLinear_of_robustNoCode h) M c

/-- **No fast transposer, even non-uniform and on average.** Under `RobustNoCode_TM`, for all `k`, `g`,
`c`, `C₀`, `C₁` and all large `n`: no machine with `k` work tapes, alphabet `g + 1` and at most
`2^{C₁ n w}` states (any transition table, which may depend on `n`) outputs the transposed encoding
within `c L` steps on every input of a set of at least `2^{L - C₀ n w}` matrix inputs. So the target
rules out finite controls holding any constant number of matrix rows. -/
theorem no_fast_transposer_of_robustNoCode (h : RobustNoCode_TM) (k g c C₀ C₁ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) ≤ C₁ * (n * entryBits n) →
      ∀ F₀ : Set (List Bool),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n * entryBits n) * F₀.ncard →
        ¬ ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
          ∃ A : Matrix, w = encode n (entryBits n) A ∧
            (run M w T).outRev.reverse = encode n (entryBits n) (transpose A) :=
  Impl.no_fast_transposer_of_robustNoCode h k g c C₀ C₁

/-- **(T) gives codes.** A linear-time transposer yields constants `k, G ≥ 1, c, C` such that for
every large `n` there are a valid `k`-tape diagram of length `≤ c L`, capacities within the block
profile, a set `F` of inputs of co-entropy `≤ C n w` and a causal code solving complete exchange on
`F`. (A corollary of `codes_coentLinear_of_linearTimeTransposable`, whose constants it inherits; the
single machine reduction `codes_of_fastOn` gives such codes on `M.k + 1` tapes with
`C = traceConst M (2c₀)` directly.) -/
theorem codes_of_linearTimeTransposable (h : LinearTimeTransposable) :
    ∃ (k G c C : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (cap : ℕ × ℕ → ℕ) (F : Set (Fin (n * n * entryBits n) → Bool))
        (code : NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧ D.CapProfile n G cap ∧
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard ∧
        D.Solves n G cap F code :=
  Impl.codes_of_linearTimeTransposable h

/-- **(T) refutes Robust CE_TM**, in every form. -/
theorem not_robustCE_TM_of_linearTimeTransposable (h : LinearTimeTransposable) : ¬ RobustCE_TM :=
  fun hc => not_linearTimeTransposable_of_robustCE_TM hc h

/-- **The target with `s` extra bits rules out every machine family whose state bits plus
head-position bits fit in `s`.** Under `RobustNoCode_TM_bits s`, for all `k`, `g`, `c`, `C₀` and all
large `n`: no machine with `k` work tapes and alphabet `g + 1` (any transition table, which may depend
on `n`) with `⌈log₂(q+1)⌉ + (k+1)⌈log₂(2cL+1)⌉ ≤ s k n` outputs the transposed encoding within `c L`
steps on every input of a set of at least `2^{L - C₀ n w}` matrix inputs. -/
theorem no_fast_transposer_of_robustNoCode_bits {s : ℕ → ℕ → ℕ} (h : RobustNoCode_TM_bits s)
    (k g c C₀ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) + (k + 1) * Nat.clog 2 (2 * (c * (n * n * entryBits n)) + 1) ≤ s k n →
      ∀ F₀ : Set (List Bool),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n * entryBits n) * F₀.ncard →
        ¬ ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
          ∃ A : Matrix, w = encode n (entryBits n) A ∧
            (run M w T).outRev.reverse = encode n (entryBits n) (transpose A) :=
  Impl.no_fast_transposer_of_robustNoCode_bits h k g c C₀

/-- **`O(log n)` extra bits suffice for every fixed machine.** Under the target with
`(3k + 4) ⌈log₂ n⌉` extra bits per memory edge, every machine fails to transpose within `c (L + 1)`
steps at every large `n`. -/
theorem linearTime_fails_of_robustNoCode_logBits
    (h : RobustNoCode_TM_bits (fun k n => (3 * k + 4) * entryBits n)) (M : TM) (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ¬ ∀ A : Matrix,
      ComputesWithin M (encode n (entryBits n) A) (encode n (entryBits n) (transpose A))
        (c * (inputLength n + 1)) :=
  Impl.linearTime_fails_of_coentLinear
    (Impl.coentLinear_of_robustNoCode (Impl.robustNoCode_logBits_iff.1 h)) M c

/-- **The `O(log n)`-bit target refutes (T).** -/
theorem not_linearTimeTransposable_of_robustNoCode_logBits
    (h : RobustNoCode_TM_bits (fun k n => (3 * k + 4) * entryBits n)) :
    ¬ LinearTimeTransposable := by
  rintro ⟨M, c, hM⟩
  obtain ⟨n₀, hn₀⟩ := linearTime_fails_of_robustNoCode_logBits h M c
  exact hn₀ (max n₀ 1) (le_max_left _ _) (hM (max n₀ 1) (le_max_right _ _))

/-! ## Co-entropy `O(n)` suffices

The targets above allow co-entropy `C n w` because the reduction's block-level trace of an adaptive
machine records absolute block indices, rows and output lengths (`O(log n)` bits per slot).
Recording moves and patterns instead takes `O(1)` bits per slot (`coarseTrace`), once the output
schedule is fixed by the halting time; a machine can be made to do so in linear time by buffering its
output on an extra tape and copying it out at the end (`bufTM_run`). So co-entropy `C n` suffices, and
so does any single superlinear level, such as `n w` (the robust target with `C = 1` alone). -/

/-- **Robust no-code at co-entropy `O(n)` refutes (T).** If for every `C`, for all constants and all
large `n`, no causal code solves complete exchange at the profile capacities on a set of inputs of
co-entropy `≤ C n`, then no machine transposes in linear time. The hypothesis is implied by
`RobustNoCode_TM` (`coentLinear_of_robustNoCode`), so this strengthens
`not_linearTimeTransposable_of_robustNoCode`. -/
theorem not_linearTimeTransposable_of_coentLinear
    (h : ∀ C : ℕ, NoCode_TM_coent (fun n => C * n)) : ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_coentLinear h

/-- **Every machine fails at every large size, at co-entropy `O(n)`.** Under the target at
co-entropy `C n` for every `C`: for every machine `M` and constant `c`, for all large `n` some
`n × n` matrix is not transposed within `c (L + 1)` steps. -/
theorem linearTime_fails_of_coentLinear (h : ∀ C : ℕ, NoCode_TM_coent (fun n => C * n))
    (M : TM) (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ¬ ∀ A : Matrix,
      ComputesWithin M (encode n (entryBits n) A) (encode n (entryBits n) (transpose A))
        (c * (inputLength n + 1)) :=
  Impl.linearTime_fails_of_coentLinear h M c

/-- **No fast transposer, even non-uniform and on average, at co-entropy `O(n)`.** Under the target
at co-entropy `C n` for every `C`: for all `k`, `g`, `c`, `C₀`, `C₁` and all large `n`, no machine with
`k` work tapes, alphabet `g + 1` and at most `2^{C₁ n w}` states (any transition table, which may
depend on `n`) outputs the transposed encoding within `c L` steps on every input of a set of at least
`2^{L - C₀ n}` matrix inputs. (The analogue of `no_fast_transposer_of_robustNoCode`, whose sets have
co-entropy `C₀ n w` under the stronger hypothesis.) -/
theorem no_fast_transposer_of_coentLinear (h : ∀ C : ℕ, NoCode_TM_coent (fun n => C * n))
    (k g c C₀ C₁ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) ≤ C₁ * (n * entryBits n) →
      ∀ F₀ : Set (List Bool),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n) * F₀.ncard →
        ¬ ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
          ∃ A : Matrix, w = encode n (entryBits n) A ∧
            (run M w T).outRev.reverse = encode n (entryBits n) (transpose A) :=
  Impl.no_fast_transposer_of_coentLinear h k g c C₀ C₁

/-- **Infinitely many sizes suffice at co-entropy `O(n)`.** -/
theorem not_linearTimeTransposable_of_coentLinear_io
    (h : ∀ (k G c C : ℕ), 1 ≤ G → ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n) * F.ncard →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code) :
    ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_coentLinear_io h

/-- **(T) gives codes at co-entropy `O(n)`, with the output at the end.** A linear-time transposer
yields constants `k, G ≥ 1, c, C` such that for every large `n` a valid `k`-tape diagram of length
`≤ c L`, appending its `L` output bits in its last `L` steps, carries a code at its profile capacities
solving complete exchange on a set of inputs of co-entropy `≤ C n`. (Explicitly, for `M` transposing
within `c₀ (L + 1)` steps: `k = M.k + 5`, `G = cellBits (bufTM M)`, `c = 2 c₀ + 4` and
`C = coarseConst (M.k + 1) c G`, from `n ≥ coarseSize M c₀`.) -/
theorem codes_coentLinear_of_linearTimeTransposable (h : LinearTimeTransposable) :
    ∃ (k G c C : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (F : Set (Fin (n * n * entryBits n) → Bool)) (code : NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n) * F.ncard ∧
        D.Solves n G (D.profileCap n G) F code ∧
        ∀ τ ≤ D.T, D.out τ = n * n * entryBits n - (D.T - τ) :=
  Impl.codes_coentLinear_of_linearTimeTransposable h

/-- **The co-entropy-`O(n)` target lies between robust and plain**: `RobustNoCode_TM` (co-entropy
`C n w`) implies it. -/
theorem coentLinear_of_robustNoCode (h : RobustNoCode_TM) :
    ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) :=
  Impl.coentLinear_of_robustNoCode h

/-- **The co-entropy-`C n` target implies the plain target** (for any one `C`). -/
theorem noCode_of_coentLinear {C : ℕ} (h : NoCode_TM_coent (fun n => C * n)) : NoCode_TM :=
  Impl.noCode_of_coentLinear h

/-- **No code at any superlinear co-entropy level refutes (T).** If `f n` eventually exceeds `C n`
for every `C` (for instance `n` times any function tending to infinity), no code at co-entropy `f` already
refutes (T). -/
theorem not_linearTimeTransposable_of_coent {f : ℕ → ℕ}
    (hf : ∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) (h : NoCode_TM_coent f) :
    ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_coent hf h

/-- **The single level `n w` suffices.** `RobustNoCode_TM` asks for no code at co-entropy `C n w` for
every `C`; no code at the one level `n w` (`C = 1`) already refutes (T), since `C n ≤ n w` from
`n ≥ 2^C` on. -/
theorem not_linearTimeTransposable_of_coent_nw
    (h : NoCode_TM_coent (fun n => n * entryBits n)) : ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_coent_nw h

/-- **Output buffering** (the machine-level step). If `M` halts at time `T` on `w` with an output of
length `L`, the buffered machine `bufTM M` (one extra work tape, two extra states, alphabet `g + 3`)
halts at time `T + 2L + 2` with the same output, and at every time `t` up to then its output has
`L - (T + 2L + 2 - t)` bits: it appends exactly in its last `L` steps. -/
theorem bufTM_run {M : TM} {w : List Bool} {T : ℕ} (hT : HaltsAt M w T) :
    HaltsAt (Impl.bufTM M) w (T + 2 * (run M w T).outRev.length + 2) ∧
    (run (Impl.bufTM M) w (T + 2 * (run M w T).outRev.length + 2)).outRev.reverse =
      (run M w T).outRev.reverse ∧
    ∀ t ≤ T + 2 * (run M w T).outRev.length + 2,
      (run (Impl.bufTM M) w t).outRev.length =
        (run M w T).outRev.length - (T + 2 * (run M w T).outRev.length + 2 - t) :=
  Impl.bufTM_run hT

/-! ## Infinitely many sizes suffice -/

/-- **No code for infinitely many `n` refutes (T).** A linear-time transposer gives codes at every
large `n` (`codes_of_linearTimeTransposable`), so the target only has to hold for infinitely many `n`
(for instance only for powers of two). `RobustNoCode_TM_io` is formally weaker than `RobustNoCode_TM`
(`robustNoCode_io_of_robustNoCode`). -/
theorem not_linearTimeTransposable_of_robustNoCode_io (h : RobustNoCode_TM_io) :
    ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_coentLinear_io fun k G c C hG n₀ =>
    Impl.coentLinear_io_of_robustNoCode_io h C k G c hG n₀

/-- **Robust CE_TM for infinitely many `n` refutes (T)** (flow form). -/
theorem not_linearTimeTransposable_of_robustCE_TM_io (h : RobustCE_TM_io) :
    ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_robustNoCode_io
    (Impl.robustNoCode_io_of_robustCE_TM_dist_io (Impl.robustCE_TM_dist_io_of_robustCE_TM_io h))

/-- The infinitely-often target is weaker. -/
theorem robustNoCode_io_of_robustNoCode (h : RobustNoCode_TM) : RobustNoCode_TM_io :=
  Impl.robustNoCode_io_of_robustNoCode h

/-- **The infinitely-often forms are equivalent**: flow, distance and no-code. The gap works one
size at a time. -/
theorem robust_io_tfae : List.TFAE [RobustCE_TM_io, RobustCE_TM_dist_io, RobustNoCode_TM_io] :=
  Impl.robust_io_tfae

/-! ## Robust versus plain

The robust target is exactly the plain target with an `O(n w)`-bit hint supplied by an oracle that
sees the whole input (a coordinator: no edge carries the hint and no node computes it), while a side
channel of that size whose contents the code computes itself is free. So the gap between the plain
and the robust conjecture is whether the network can compute such a hint itself. Timing alone is not
the issue: after a prepended input sweep every row is read before the original diagram starts.
Partial results towards "plain ⟹ robust" are in `Transpose/Tape/Statements/PlainRobust.lean` and
`Transpose/Tape/PlainRobust/`. -/

/-- **Robust ⟺ plain with an oracle hint.** `RobustNoCode_TM` holds iff, for every `C`, no family
of codes indexed by a hint `< 2^{C n w}` that may be any function of the whole input solves complete
exchange on every input (equivalently: the inputs cannot be covered by `2^{C n w}` sets each carrying
a code). -/
theorem robustNoCode_iff_hint : RobustNoCode_TM ↔ NoCode_TM_hint :=
  Impl.robustNoCode_iff_hint

/-- **The hint form refutes (T).** -/
theorem not_linearTimeTransposable_of_noCode_hint (h : NoCode_TM_hint) :
    ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_robustNoCode (Impl.robustNoCode_iff_hint.2 h)

/-- **(T) gives hint codes on all inputs**: a linear-time transposer yields constants such that, for
every large `n`, a single valid diagram carries codes, indexed by a hint `< 2^{C n w}` that is a
function of the whole input, solving complete exchange on *every* input at the profile capacities.
(The popular-trace code, shifted. Unlike Farhadi et al.'s coordinator, which receives the inputs
over edges, this oracle coordinator is uncharged and sends one global index to every node.) -/
theorem hintCodes_of_linearTimeTransposable (h : LinearTimeTransposable) :
    ∃ (k G c C : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (hint : (Fin (n * n * entryBits n) → Bool) → ℕ) (codes : ℕ → NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
        (∀ x, hint x < 2 ^ (C * n * entryBits n)) ∧
        ∀ x, D.Solves n G (D.profileCap n G) {x} (codes (hint x)) :=
  Impl.hintCodes_of_linearTimeTransposable h

/-- **A side channel computed by the code is free**: for `s k n ≤ C(k) n w` (for `n ≥ 1`), "no code"
for independent sources with `s k n` extra bits on every memory edge (contents computed by the code,
like every edge value) is equivalent to `NoCode_TM`. -/
theorem noCode_bits_iff {s : ℕ → ℕ → ℕ}
    (hs : ∃ C : ℕ → ℕ, ∀ k n, 1 ≤ n → s k n ≤ C k * (n * entryBits n)) :
    NoCode_TM_bits s ↔ NoCode_TM :=
  Impl.noCode_bits_iff hs

/-- **The co-entropy ladder, top**: the robust target is "no code at co-entropy `C n w`" for every
`C`. -/
theorem robustNoCode_iff_coent :
    RobustNoCode_TM ↔ ∀ C : ℕ, NoCode_TM_coent (fun n => C * n * entryBits n) :=
  Impl.robustNoCode_iff_coent

/-- **The co-entropy ladder, bottom**: the plain target is "no code at co-entropy `0`". -/
theorem noCode_iff_coent_zero : NoCode_TM ↔ NoCode_TM_coent (fun _ => 0) :=
  Impl.noCode_iff_coent_zero

/-- A smaller co-entropy budget is a weaker target. -/
theorem coent_mono {m m' : ℕ → ℕ} (hm : ∃ N, ∀ n, N ≤ n → m n ≤ m' n)
    (h : NoCode_TM_coent m') : NoCode_TM_coent m :=
  Impl.coent_mono hm h

/-- **Co-entropy `s` ⟹ no hint code with `s` hint bits** (pigeonhole). -/
theorem hintBits_of_coent {s : ℕ → ℕ} (h : NoCode_TM_coent s) : NoCode_TM_hintBits s :=
  Impl.hintBits_of_coent h

/-- **No hint code with `m + 3w + 1` hint bits ⟹ co-entropy `m`** (shifts of a code cover all
inputs). -/
theorem coent_of_hintBits {m s : ℕ → ℕ}
    (hs : ∃ N, ∀ n, N ≤ n → m n + 3 * entryBits n + 1 ≤ s n)
    (h : NoCode_TM_hintBits s) : NoCode_TM_coent m :=
  Impl.coent_of_hintBits hs h

/-- With a constant hint (`C = 0`) the hint target gives the plain target. -/
theorem noCode_of_noCode_hint (h : NoCode_TM_hint) : NoCode_TM :=
  Impl.noCode_of_noCode_hint h

/-- **A code for `F` is a code for every shift of `F`** (TM-free), within the same capacities: each
node shifts its visible rows by `z` and each output bit is shifted back. -/
theorem solves_shiftCode {k : ℕ} (D : TSDiagram k) {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {C : NetCode} (hsol : D.Solves n G cap F C)
    (z : Fin (n * n * entryBits n) → Bool) :
    D.Solves n G cap {x | Impl.xorVec x z ∈ F}
      (Impl.shiftCode D n (entryBits n) (blockSize G n) C z) :=
  Impl.solves_shiftCode D hsol z

/-- **Shifts of a large set cover everything**: if `2^L ≤ 2^m |F|`, some `2^m (L + 1)` shifts of `F`
cover every vector of length `L`. -/
theorem exists_shift_cover {L m : ℕ} (F : Set (Fin L → Bool)) (hF : 2 ^ L ≤ 2 ^ m * F.ncard) :
    ∃ z : Fin (2 ^ m * (L + 1)) → (Fin L → Bool), ∀ x, ∃ i, Impl.xorVec x (z i) ∈ F :=
  Impl.exists_shift_cover F hF

/-- **Per diagram: a code on a large set gives a hint code**, within the same capacities. -/
theorem hint_of_code {k : ℕ} (D : TSDiagram k) {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {C : NetCode} {m : ℕ}
    (hsol : D.Solves n G cap F C) (hF : 2 ^ (n * n * entryBits n) ≤ 2 ^ m * F.ncard) :
    ∃ (hint : (Fin (n * n * entryBits n) → Bool) → ℕ) (codes : ℕ → NetCode),
      (∀ x, hint x < 2 ^ m * (n * n * entryBits n + 1)) ∧
      ∀ x, D.Solves n G cap {x} (codes (hint x)) :=
  Impl.hint_of_code D hsol hF

/-- **Per diagram: a hint code gives a code on a large set**, within the same capacities. -/
theorem code_of_hint {k : ℕ} (D : TSDiagram k) {n G : ℕ} {cap : ℕ × ℕ → ℕ} {s : ℕ}
    (hint : (Fin (n * n * entryBits n) → Bool) → ℕ) (codes : ℕ → NetCode)
    (hh : ∀ x, hint x < 2 ^ s) (hsol : ∀ x, D.Solves n G cap {x} (codes (hint x))) :
    ∃ (F : Set (Fin (n * n * entryBits n) → Bool)) (C : NetCode),
      2 ^ (n * n * entryBits n) ≤ 2 ^ s * F.ncard ∧ D.Solves n G cap F C :=
  Impl.code_of_hint D hint codes hh hsol

/-! ## The forms are equivalent -/

/-- **The robust forms are equivalent**: the flow form `RobustCE_TM`, the distance form, "no code",
"no code" and the flow form on diagrams with every row attached, "no code" with the uniform profile
of `3k` blocks per memory edge, and "no code" with `(3k + 4)⌈log₂ n⌉` extra bits per memory edge. -/
theorem robust_tfae : List.TFAE [RobustCE_TM, RobustCE_TM_dist, RobustNoCode_TM,
    RobustNoCode_TM_att, RobustCE_TM_att, RobustNoCode_TM_with (fun k => 3 * k),
    RobustNoCode_TM_bits (fun k n => (3 * k + 4) * entryBits n)] :=
  Impl.robust_tfae

/-- **The plain forms are equivalent**: `CE_TM`, `CE_TM_dist` and `NoCode_TM`. -/
theorem plain_tfae : List.TFAE [CE_TM, CE_TM_dist, NoCode_TM] :=
  Impl.plain_tfae

/-- **Every routing has rate `O(1/log n)`** (network-only: weak duality plus `volume_gap`). For all
constants there is `n₀` such that, for `n ≥ n₀`, on a valid `k`-tape diagram of length `≤ c L` with at
most `C` rows without a source node, every routing of the transposition demand within capacities in
the block profile has rate `< E / w`, where `E = 4 ⌈log₂(2k+3)⌉ (4k+1) G (c+1)`. A solving code has
rate `1`. -/
theorem flow_rate_lt (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap →
      ((Finset.range n).filter (fun i => ∀ a < D.nodes (blockSize G n),
        i ∉ D.rowsAt n (entryBits n) (blockSize G n) a)).card ≤ C →
      ∀ (ρ : Routing) (rate : ℝ), D.RoutesAt n G cap ρ rate →
        rate < ((4 * Nat.clog 2 (2 * k + 3) * ((4 * k + 1) * G * (c + 1)) : ℕ) : ℝ) / entryBits n :=
  ⟨Impl.ceSize k G c C, fun _ hn _ hD hT _ hcap hu _ _ hρ => Impl.rate_lt hG hn hD hT hcap hu hρ⟩

/-- **The volume bound caps the flow rate at `E/w`** (a property of the networks alone). For all
constants there is `n₀` such that, for `n ≥ n₀`, every valid `k`-tape diagram of length `≤ c L` with at
most `C` rows without a source node, with capacities within the block profile, has
`w Σ_e cap e < E Σ_d rowDist d`, where `E = 4 ⌈log₂(2k+3)⌉ (4k+1) G (c+1)`. -/
theorem volume_gap (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap →
      ((Finset.range n).filter (fun i => ∀ a < D.nodes (blockSize G n),
        i ∉ D.rowsAt n (entryBits n) (blockSize G n) a)).card ≤ C →
        entryBits n * ∑ e ∈ D.edges (blockSize G n), cap e <
          4 * Nat.clog 2 (2 * k + 3) * ((4 * k + 1) * G * (c + 1)) *
            ∑ d ∈ Finset.range (n * n * entryBits n), D.rowDist n (entryBits n) (blockSize G n) d :=
  ⟨Impl.ceSize k G c C, fun _ hn _ hD hT _ hcap hu => Impl.volume_gap hG hn hD hT hcap hu⟩

/-- **A code beats the volume bound by a factor `Ω(log n)`.** For all constants there is `n₀` such
that, for `n ≥ n₀`, if a causal code solves complete exchange within the block profile on a set of
inputs of co-entropy `≤ C n w`, then `w Σ_e cap e < E Σ_d rowDist d` with
`E = 4 ⌈log₂(2k+3)⌉ (4k+1) G (c+1)`. So the volume bound caps the flow rate at `E/w`, while the code
has rate `1`. -/
theorem code_gap (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ code : NetCode, D.Solves n G cap F code →
        entryBits n * ∑ e ∈ D.edges (blockSize G n), cap e <
          4 * Nat.clog 2 (2 * k + 3) * ((4 * k + 1) * G * (c + 1)) *
            ∑ d ∈ Finset.range (n * n * entryBits n), D.rowDist n (entryBits n) (blockSize G n) d :=
  ⟨Impl.ceSize k G c C, fun _ hn _ hD hT _ hcap _ hF _ hsol => Impl.dist_gap hG hn hD hT hcap hF hsol⟩

/-- **An explicit gain threshold suffices.** Suppose that for all constants and all large `n`, every
causal code solving complete exchange at the profile capacities (`profileCap`) satisfies
`E Σ_d rowDist d ≤ w Σ_e profileCap e` with `E = 4 ⌈log₂(2k+3)⌉ (4k+1) G (c+1)`. That is, the volume
bound allows routing at rate `E/w`, so the coding gain is at most `w / E ≈ log₂ n / E`. Then no such
code exists, so (T) fails. The conjecture's `o(log n)` is not needed, and the bound is needed only
at `profileCap`, not for every `cap` within the block profile. -/
theorem robustNoCode_of_gainBound
    (h : ∀ (k G c C : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ code : NetCode, D.Solves n G (D.profileCap n G) F code →
        4 * Nat.clog 2 (2 * k + 3) * ((4 * k + 1) * G * (c + 1)) *
            ∑ d ∈ Finset.range (n * n * entryBits n), D.rowDist n (entryBits n) (blockSize G n) d ≤
          entryBits n * ∑ e ∈ D.edges (blockSize G n), D.profileCap n G e) :
    RobustNoCode_TM :=
  Impl.robustNoCode_of_gainBound h

/-- **Robust CE_TM is equivalent to "no code".** -/
theorem robustCE_TM_iff_robustNoCode : RobustCE_TM ↔ RobustNoCode_TM :=
  robust_tfae.out 1 3

/-- **The distance form is equivalent to "no code".** -/
theorem robustCE_TM_dist_iff_robustNoCode : RobustCE_TM_dist ↔ RobustNoCode_TM :=
  robust_tfae.out 2 3

/-- **CE_TM is equivalent to "no code"** (independent uniform sources). -/
theorem ce_TM_iff_noCode : CE_TM ↔ NoCode_TM :=
  plain_tfae.out 1 3

/-- **CE_TM, distance form, is equivalent to "no code".** -/
theorem ce_TM_dist_iff_noCode : CE_TM_dist ↔ NoCode_TM :=
  plain_tfae.out 2 3

/-- The robust form implies the plain one (all inputs have co-entropy `0`). -/
theorem noCode_of_robustNoCode (h : RobustNoCode_TM) : NoCode_TM :=
  Impl.noCode_of_robustNoCode h

/-- Robust CE_TM implies CE_TM. -/
theorem ce_TM_of_robustCE_TM (h : RobustCE_TM) : CE_TM :=
  ce_TM_iff_noCode.2 (noCode_of_robustNoCode (robustCE_TM_iff_robustNoCode.1 h))

/-- The robust distance form implies the plain distance form. -/
theorem ce_TM_dist_of_robustCE_TM_dist (h : RobustCE_TM_dist) : CE_TM_dist :=
  ce_TM_dist_iff_noCode.2 (noCode_of_robustNoCode (robustCE_TM_dist_iff_robustNoCode.1 h))

/-- **The memory profile is immaterial.** For every `m` such that every `k` has some `a` with
`3k ≤ m (k + a)` (e.g. `m k ≥ 3k`, or one block per tape `m k = k`), "no code" with the uniform
profile of `m` blocks per memory edge is equivalent to `RobustNoCode_TM` (per-node profile). This
includes `m k = 3k` (with no state bits at all) and `m k = 3k + 1`; the informal profile of `3k`
blocks plus `O(1)` (or `O(log n)`) bits lies between these two for large `n`. One direction adds
`m k` stationary tapes, which change nothing in the block network and add `m k` resident blocks per
slot; the other adds `a` stationary tapes and uses that at most `3k` blocks are resident per
slot. -/
theorem robustNoCode_with_iff {m : ℕ → ℕ} (hm : ∀ k, ∃ a, 3 * k ≤ m (k + a)) :
    RobustNoCode_TM_with m ↔ RobustNoCode_TM :=
  Impl.robustNoCode_with_iff hm

/-- **One block per tape** on memory edges (`m k = k`) is already equivalent to the per-node
profile (add `2k` stationary tapes). -/
theorem robustNoCode_with_k_iff : RobustNoCode_TM_with (fun k => k) ↔ RobustNoCode_TM :=
  Impl.robustNoCode_with_k_iff

/-- The hypothesis of `robustNoCode_with_iff` says exactly that `m` is unbounded: for every unbounded
memory profile, "no code" is equivalent to `RobustNoCode_TM`. -/
theorem exists_shift_iff_unbounded (m : ℕ → ℕ) :
    (∀ k, ∃ a, 3 * k ≤ m (k + a)) ↔ ∀ B, ∃ j, B ≤ m j :=
  Impl.exists_shift_iff_unbounded m

/-- "No code" with the per-node profile implies "no code" with every uniform profile. -/
theorem robustNoCode_with_of_robustNoCode (m : ℕ → ℕ) (h : RobustNoCode_TM) :
    RobustNoCode_TM_with m :=
  Impl.robustNoCode_with_of_robustNoCode m h

/-- **Extra bits are immaterial**: for `s k n ≤ C(k) n w` (for `n ≥ 1`), "no code" with `s k n` extra
bits per memory edge is equivalent to `RobustNoCode_TM` (add `C(k)` stationary tapes). This includes
every `s` independent of `k` with `s n ≤ K n w`, e.g. `s = 0`. -/
theorem robustNoCode_bits_iff {s : ℕ → ℕ → ℕ}
    (hs : ∃ C : ℕ → ℕ, ∀ k n, 1 ≤ n → s k n ≤ C k * (n * entryBits n)) :
    RobustNoCode_TM_bits s ↔ RobustNoCode_TM :=
  Impl.robustNoCode_bits_iff hs

/-- **The `O(log n)`-bit target is equivalent** to `RobustNoCode_TM`: the target of
`linearTime_fails_of_robustNoCode_logBits` (`s k n = (3k + 4)⌈log₂ n⌉`) therefore also rules out
machine families with up to `2^{C₁ n w}` states, for any `C₁` (`no_fast_transposer_of_robustNoCode`). -/
theorem robustNoCode_logBits_iff :
    RobustNoCode_TM_bits (fun k n => (3 * k + 4) * entryBits n) ↔ RobustNoCode_TM :=
  Impl.robustNoCode_logBits_iff

/-- **The target with every capacity in the profile.** `RobustNoCode_TM`, stated at the profile
capacities, is equivalent to ruling out codes within every `cap` satisfying `CapProfile`. -/
theorem robustNoCode_iff_forall_cap : RobustNoCode_TM ↔
    ∀ (k G c C : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ code : NetCode, ¬ D.Solves n G cap F code :=
  Impl.robustNoCode_iff_forall_cap

/-- **The plain target with every capacity in the profile**: `NoCode_TM` is equivalent to ruling out
codes within every `cap` satisfying `CapProfile`. -/
theorem noCode_iff_forall_cap : NoCode_TM ↔
    ∀ (k G c : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap →
      ∀ code : NetCode, ¬ D.Solves n G cap Set.univ code :=
  Impl.noCode_iff_forall_cap

/-- `Solves` is monotone in the capacities. -/
theorem solves_mono {k : ℕ} (D : TSDiagram k) {n G : ℕ} {cap cap' : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode}
    (hle : ∀ e ∈ D.edges (blockSize G n), cap e ≤ cap' e) (h : D.Solves n G cap F code) :
    D.Solves n G cap' F code :=
  Impl.solves_mono D hle h

/-- **Every row attached, without loss of generality.** "No code" on diagrams whose input walk attaches
every row is equivalent to `RobustNoCode_TM`: a diagram is extended by a final input sweep, which keeps
every original node, edge and sink and the residency of every complete slot (an incomplete last slot
can only gain residents, chords and source rows), and the code masks each node's input back to its
original rows (`c` becomes `2c + 3`). -/
theorem robustNoCode_iff_attached : RobustNoCode_TM ↔ RobustNoCode_TM_att :=
  Impl.robustNoCode_iff_attached

/-- **The flow form on diagrams with every row attached** is equivalent to "no code", hence to
`RobustCE_TM`. Here every commodity has a source node, so the conventions for rows without one never
arise. -/
theorem robustCE_TM_att_iff : RobustCE_TM_att ↔ RobustNoCode_TM :=
  Impl.robustCE_TM_att_iff

/-- The flow forms with and without the attachment restriction are equivalent. -/
theorem robustCE_TM_att_iff_robustCE_TM : RobustCE_TM_att ↔ RobustCE_TM :=
  robustCE_TM_att_iff.trans robustCE_TM_iff_robustNoCode.symm

/-! ## Oblivious machines -/

/-- **An oblivious linear-time transposer gives codes for independent sources.** -/
theorem codes_of_obliviousLinearTimeTransposable (h : ObliviousLinearTimeTransposable) :
    ∃ (k G c : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (cap : ℕ × ℕ → ℕ) (code : NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧ D.CapProfile n G cap ∧
        D.Solves n G cap Set.univ code :=
  Impl.codes_of_obliviousLinearTimeTransposable h

/-- **No code (independent sources) refutes oblivious (T).** -/
theorem not_obliviousLinearTimeTransposable_of_noCode (h : NoCode_TM) :
    ¬ ObliviousLinearTimeTransposable :=
  Impl.not_obliviousLinearTimeTransposable_of_noCode h

/-- **CE_TM implies no oblivious linear-time transposer.** -/
theorem not_obliviousLinearTimeTransposable_of_ce_TM (h : CE_TM) :
    ¬ ObliviousLinearTimeTransposable :=
  not_obliviousLinearTimeTransposable_of_noCode (ce_TM_iff_noCode.1 h)

/-- **CE_TM, distance form, implies no oblivious linear-time transposer.** -/
theorem not_obliviousLinearTimeTransposable_of_ce_TM_dist (h : CE_TM_dist) :
    ¬ ObliviousLinearTimeTransposable :=
  not_obliviousLinearTimeTransposable_of_noCode (ce_TM_dist_iff_noCode.1 h)

/-- **`NoCode_TM` for infinitely many `n` refutes oblivious (T).** -/
theorem not_obliviousLinearTimeTransposable_of_noCode_io (h : NoCode_TM_io) :
    ¬ ObliviousLinearTimeTransposable :=
  Impl.not_obliviousLinearTimeTransposable_of_noCode_io h

/-- Robust ⟹ plain, infinitely often. -/
theorem noCode_io_of_robustNoCode_io (h : RobustNoCode_TM_io) : NoCode_TM_io :=
  Impl.noCode_io_of_robustNoCode_io h

/-! ## The ingredients -/

/-- **The cut-set bound, bit level** (TM-free). If a causal code solves complete exchange on `F` within
`cap`, then for every set `U` of nodes, with `B_U` the input bits whose row is attached at no node of
`U` and whose transposed position is decoded at a node of `U`,
`2^{|B_U|} |F| ≤ 2^L · 2^{Σ_{e entering U} cap e}`. -/
theorem cutset_bound_bitwise {k : ℕ} (D : TSDiagram k) {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (hsol : D.Solves n G cap F code)
    (U : Set ℕ) [DecidablePred (· ∈ U)] :
    2 ^ ((Finset.range (n * n * entryBits n)).filter (fun d =>
        d / (n * entryBits n) ∉ D.rowsIn n (entryBits n) (blockSize G n) U ∧
        D.outNode (blockSize G n) (tpos n (entryBits n) d) ∈ U)).card * F.ncard ≤
      2 ^ (n * n * entryBits n) * 2 ^ (∑ e ∈ D.edgesInto (blockSize G n) U, cap e) :=
  Impl.cutset_bound_bitwise D hsol U

/-- **The cut-set bound, bit level, bits form**: if `2^L ≤ 2^{D_c} |F|`, then
`|B_U| ≤ D_c + Σ_{e entering U} cap e`. -/
theorem cutset_bits_bitwise {k : ℕ} (D : TSDiagram k) {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (hsol : D.Solves n G cap F code)
    {Dc : ℕ} (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ Dc * F.ncard) (U : Set ℕ)
    [DecidablePred (· ∈ U)] :
    ((Finset.range (n * n * entryBits n)).filter (fun d =>
        d / (n * entryBits n) ∉ D.rowsIn n (entryBits n) (blockSize G n) U ∧
        D.outNode (blockSize G n) (tpos n (entryBits n) d) ∈ U)).card ≤
      Dc + ∑ e ∈ D.edgesInto (blockSize G n) U, cap e :=
  Impl.cutset_bits_bitwise D hsol hco U

/-- **The cut-set bound for network codes** (TM-free; entry form). If a causal code solves complete
exchange on `F` within `cap`, then for every set `U` of nodes, with `S_U` the entries whose row is
attached at no node of `U` (`rowsIn`) and whose column is produced entirely at nodes of `U`
(`colsIn`), `2^{w |S_U|} |F| ≤ 2^L · 2^{Σ_{e entering U} cap e}`. A corollary of
`cutset_bound_bitwise`, since each such entry gives `w` cut bits. -/
theorem cutset_bound {k : ℕ} (D : TSDiagram k) {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (hsol : D.Solves n G cap F code)
    (U : Set ℕ) [DecidablePred (· ∈ U)] :
    2 ^ (entryBits n * ((Finset.range n \ D.rowsIn n (entryBits n) (blockSize G n) U) ×ˢ
        D.colsIn n (entryBits n) (blockSize G n) U).card) * F.ncard ≤
      2 ^ (n * n * entryBits n) * 2 ^ (∑ e ∈ D.edgesInto (blockSize G n) U, cap e) :=
  Impl.cutset_bound D hsol U

/-- **Discrete Isoperimetry for every code-carrying diagram** (TM-free). Let a causal code solve
complete exchange on `F`, with `2^L ≤ 2^{D_c} |F|`, in the block network of a valid diagram (block
size `r ≥ 1`; then `r ≤ n w`). For a labelling of the slots with at most `m` slots per label and
`M_b` label changes,
`(n - M_b)(n - 2m) w ≤ (M_b + 1) D_c + Σ_{e between different labels} cap e`. -/
theorem isoperimetry_code {k : ℕ} (D : TSDiagram k) {n G : ℕ} (hD : D.Valid (n * n * entryBits n))
    (hr : 1 ≤ blockSize G n) {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (hsol : D.Solves n G cap F code)
    {Dc : ℕ} (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ Dc * F.ncard) (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (D.nodes (blockSize G n))).filter (fun y => lab y = ℓ)).card ≤ m) :
    (n - labelChanges lab (D.nodes (blockSize G n))) * (n - 2 * m) * entryBits n ≤
      (labelChanges lab (D.nodes (blockSize G n)) + 1) * Dc +
        ∑ e ∈ (D.edges (blockSize G n)).filter (fun e => lab e.1 ≠ lab e.2), cap e :=
  Impl.isoperimetry_code D hD hr hsol hco lab m hm

/-- **Weak duality.** A routing at rate `λ` within the capacities bounds the total distance of the
commodities: `λ Σ_d rowDist d ≤ Σ_e cap e`. -/
theorem weak_duality {k : ℕ} {D : TSDiagram k} {n G : ℕ} {cap : ℕ × ℕ → ℕ} {ρ : Routing}
    {rate : ℝ} (hρ : D.RoutesAt n G cap ρ rate) :
    rate * ((∑ d ∈ Finset.range (n * n * entryBits n),
        D.rowDist n (entryBits n) (blockSize G n) d : ℕ) : ℝ) ≤
      ∑ e ∈ D.edges (blockSize G n), (cap e : ℝ) :=
  Impl.weak_duality hρ

/-- **Rows without a source node cost co-entropy.** If a code solves complete exchange on `F` in the
block network of a diagram, and `u` input rows have no source node, then `2^{u n w} |F| ≤ 2^L`. -/
theorem card_le_of_solves {k : ℕ} {D : TSDiagram k} {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (hsol : D.Solves n G cap F code) :
    2 ^ (((Finset.range n).filter (fun i => ∀ a < D.nodes (blockSize G n),
        i ∉ D.rowsAt n (entryBits n) (blockSize G n) a)).card * (n * entryBits n)) * F.ncard ≤
      2 ^ (n * n * entryBits n) :=
  Impl.card_le_of_solves hsol

/-- **Most input bits are far from their sinks** (TM-free; summed form). Consider the block network of
a valid `k`-tape diagram, with block size `1 ≤ r ≤ n w`, `N` nodes and `u` rows without a source node.
For every `j`, `j L ≤ Σ_d rowDist d + j (4 N (2k+3)^{j-1} w + u n w)`: in effect, all but
`4 N (2k+3)^{j-1} w + u n w` of the `L = n² w` input bits are at distance `≥ j` from the sink of
their transposed position. The network has degree `≤ 2k + 2`, at most `2` rows per node, and at most
`2w` bits of a row per sink. -/
theorem rowDist_sum_ge {k : ℕ} {D : TSDiagram k} {n w r : ℕ} (hD : D.Valid (n * n * w))
    (hr : 1 ≤ r) (hrnw : r ≤ n * w) (j : ℕ) :
    j * (n * n * w) ≤ ∑ d ∈ Finset.range (n * n * w), D.rowDist n w r d +
      j * (4 * D.nodes r * (2 * k + 3) ^ (j - 1) * w +
        ((Finset.range n).filter (fun i => ∀ a < D.nodes r, i ∉ D.rowsAt n w r a)).card *
          (n * w)) :=
  Impl.rowDist_sum_ge hD hr hrnw j

/-- The block network of a valid diagram has at most `k N` chord edges (each node is the target of at
most one chord per tape). -/
theorem card_chordEdges_le {k : ℕ} {D : TSDiagram k} {L r : ℕ} (hD : D.Valid L) (hr : 1 ≤ r) :
    (D.chordEdges r).card ≤ k * D.nodes r :=
  Impl.card_chordEdges_le hD hr

/-- **Capacities within the block profile sum to `O(L)`**: at most `4k N r G`, where `N r ≤ T + r`
(at most `3k` resident blocks per memory edge, and `k N` tape chords in all). -/
theorem sum_cap_le {k : ℕ} {D : TSDiagram k} {L n G : ℕ} (hD : D.Valid L)
    {cap : ℕ × ℕ → ℕ} (hcap : D.CapProfile n G cap) :
    ∑ e ∈ D.edges (blockSize G n), cap e ≤
      4 * k * D.nodes (blockSize G n) * (blockSize G n * G) :=
  Impl.sum_cap_le hD hcap

/-- **The popular trace within a set of inputs.** If every input of a nonempty set `F₀` of matrix
inputs halts within `T_max` steps (slot length `1 ≤ r ≤ n b`), some trace class `F ⊆ F₀` with halting
time `T ≤ T_max` has `|F₀| ≤ traceCount · |F|`. -/
theorem exists_popular_traceClass_on {M : TM} {n b r Tmax : ℕ} (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    {F₀ : Set (List Bool)} (hF₀ : F₀ ⊆ matrixInputs n b) (hne : F₀.Nonempty)
    (hrun : ∀ w ∈ F₀, ∃ T ≤ Tmax, HaltsAt M w T) :
    ∃ T ≤ Tmax, ∃ (F : Set (List Bool)) (w₀ : List Bool), TraceClass M n b r T F w₀ ∧ F ⊆ F₀ ∧
      F₀.ncard ≤ traceCount M.k n (numSlots r Tmax) Tmax * F.ncard :=
  Impl.exists_popular_traceClass_on hr hrnb hF₀ hne hrun

/-- **A trace class is a network code** (the Block Locality Lemma in functional form). Let `M`
output the transposed encoding on every input of a trace class `F` (slot length `r = slotLen M n`,
halting time `T`, representative `w₀`); `Transposes M n (entryBits n)` implies this. Then the
time–space diagram `runDiagram M w₀ T` of the representative's run is valid, and its block network
carries a causal code solving complete exchange on the class.
* A memory edge `y → y+1` carries what slot `y` can compute: the state and the `k + 1` head positions
  at time `(y+1) r`, and the contents at that time of the blocks resident at slot `y`. That is
  `⌈log₂(q+1)⌉ + (k+1)⌈log₂(2T+1)⌉ + r ⌈log₂(g+1)⌉ · |R_y|` bits, `|R_y|` summed over the tapes.
* A chord edge carries one block per tape having that chord: `r ⌈log₂(g+1)⌉` bits per tape. -/
theorem traceClass_code {M : TM} {n T : ℕ} (hn : 1 ≤ n) {F : Set (List Bool)} {w₀ : List Bool}
    (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀)
    (hcorr : ∀ w ∈ F, ∃ A : Matrix, w = encode n (entryBits n) A ∧
      (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) :
    ∃ (cap : ℕ × ℕ → ℕ) (code : NetCode),
      (runDiagram M w₀ T).Valid (n * n * entryBits n) ∧
      (runDiagram M w₀ T).Solves n (cellBits M) cap {v | List.ofFn v ∈ F} code ∧
      (∀ e ∈ (runDiagram M w₀ T).memEdges (slotLen M n), cap e ≤ Nat.clog 2 (M.q + 1) +
        (M.k + 1) * Nat.clog 2 (2 * T + 1) +
        (∑ t, (pairRes (slotLen M n) ((runDiagram M w₀ T).work t) (runDiagram M w₀ T).T e.1).card) *
          slotLen M n * Nat.clog 2 (M.g + 1)) ∧
      (∀ e ∈ (runDiagram M w₀ T).chordEdges (slotLen M n),
        cap e ≤ (runDiagram M w₀ T).chordTapes (slotLen M n) e * slotLen M n *
          Nat.clog 2 (M.g + 1)) ∧
      (∀ e, e ∉ (runDiagram M w₀ T).edges (slotLen M n) → cap e = 0) :=
  Impl.traceClass_code hn hF hcorr

/-- **A fast transposer gives a code** (the per-size reduction). Let `M` output the transposed
encoding within `c L` steps on every input of a set `F₀` of co-entropy `≤ C₀ n w`, at a size
`n ≥ slotSize M.k c` where its state takes at most half a block. Then there are a valid
`(M.k + 1)`-tape diagram of length `≤ c L`, capacities within the block profile (`G = cellBits M`), a
set of inputs of co-entropy `≤ (C₀ + traceConst M c) n w` and a causal code solving complete exchange
on it. -/
theorem codes_of_fastOn {M : TM} {c C₀ n : ℕ} (hn : Impl.slotSize M.k c ≤ n)
    (hq : 2 * Nat.clog 2 (M.q + 1) ≤ n * entryBits n) {F₀ : Set (List Bool)}
    (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n * entryBits n) * F₀.ncard)
    (hfast : ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
      ∃ A : Matrix, w = encode n (entryBits n) A ∧
        (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) :
    ∃ (D : TSDiagram (M.k + 1)) (cap : ℕ × ℕ → ℕ) (F : Set (Fin (n * n * entryBits n) → Bool))
      (code : NetCode),
      D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
      D.CapProfile n (cellBits M) cap ∧
      2 ^ (n * n * entryBits n) ≤
        2 ^ ((C₀ + traceConst M (c : ℝ)) * n * entryBits n) * F.ncard ∧
      D.Solves n (cellBits M) cap F code :=
  Impl.codes_of_fastOn hn hq hco hfast

/-- **The single machine reduction** (per size). If `M` outputs the transposed encoding within `c L`
steps on every input of a set `F₀` of co-entropy `≤ C₀ n w`, and its state bits plus head-position
bits fit in `s`, then its popular trace class is a code on its own `M.k`-tape diagram, at the per-node
blocks plus `s` bits per memory edge. Every other profile follows by TM-free conversions
(`solves_profileCap_addTapes`, `robustNoCode_bits_iff`). -/
theorem codes_of_fastOn_bits {M : TM} {c C₀ n s : ℕ} (hn1 : 1 ≤ n)
    (hs : Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * (c * (n * n * entryBits n)) + 1) ≤ s)
    {F₀ : Set (List Bool)}
    (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n * entryBits n) * F₀.ncard)
    (hfast : ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
      ∃ A : Matrix, w = encode n (entryBits n) A ∧
        (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) :
    ∃ (D : TSDiagram M.k) (F : Set (Fin (n * n * entryBits n) → Bool)) (code : NetCode),
      D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
      2 ^ (n * n * entryBits n) ≤
        2 ^ ((C₀ + traceConst M (c : ℝ)) * n * entryBits n) * F.ncard ∧
      D.Solves n (cellBits M) (D.blockCap n (cellBits M)
        (fun y => ∑ t, (pairRes (blockSize (cellBits M) n) (D.work t) D.T y).card) s) F code :=
  Impl.codes_of_fastOn_bits hn1 hs hco hfast

/-- **Extra bits become stationary tapes** (TM-free). A code at the per-node blocks plus
`s ≤ a r G` bits per memory edge is a code at the per-node profile capacities of the diagram with `a`
stationary tapes added. -/
theorem solves_profileCap_addTapes {k : ℕ} {D : TSDiagram k} {n G a s : ℕ}
    (hr : 1 ≤ blockSize G n) (hs : s ≤ a * (blockSize G n * G))
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode}
    (h : D.Solves n G (D.blockCap n G
      (fun y => ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) s) F code) :
    (Impl.addTapes D a).Solves n G ((Impl.addTapes D a).profileCap n G) F code :=
  Impl.solves_profileCap_addTapes hr hs h

/-! ## Weaker sufficient conditions for ¬(T)

Proofs in `CERungs.lean` and `CoarseTrace.lean`. -/

/-- **(T) gives hint codes with an `O(n)`-bit hint** (not `O(n w)`): for all large `n`, a valid
diagram with causal codes indexed by an oracle hint `hint x < 2^{C n}`. -/
theorem hintCodes_linear_of_linearTimeTransposable (h : LinearTimeTransposable) :
    ∃ (k G c C : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (hint : (Fin (n * n * entryBits n) → Bool) → ℕ) (codes : ℕ → NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
        (∀ x, hint x < 2 ^ (C * n)) ∧
        ∀ x, D.Solves n G (D.profileCap n G) {x} (codes (hint x)) :=
  Impl.hintCodes_linear_of_linearTimeTransposable h

/-- **The linear hint rung is the linear co-entropy rung**: no code with a `C n`-bit oracle hint, for
every `C`, iff no code at co-entropy `C n`, for every `C`. -/
theorem hintLinear_iff_coentLinear :
    (∀ C : ℕ, NoCode_TM_hintBits (fun n => C * n)) ↔ ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) :=
  Impl.hintLinear_iff_coentLinear

/-- **An `O(n)`-bit oracle hint suffices to refute (T)**: if for every `C` no family of codes indexed
by a `C n`-bit hint exists, then ¬(T). This sharpens `not_linearTimeTransposable_of_noCode_hint`
(an `O(n w)`-bit hint). -/
theorem not_linearTimeTransposable_of_noCode_hintLinear
    (h : ∀ C : ℕ, NoCode_TM_hintBits (fun n => C * n)) : ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_noCode_hintLinear h

/-- **One superlinear level, infinitely many `n`, refutes (T).** If `f n` eventually exceeds `C n` for
every `C` (for instance `f n = n w`, or `n` times any function tending to infinity), then no code at
co-entropy `f` for infinitely many `n` (`NoCode_TM_coent_io f`) already refutes (T). By a diagonal
argument, "some such `f`" is equivalent to the linear io family "for every `C`, co-entropy `C n` for
infinitely many `n`" (`coentLinear_io_iff_exists_coent_io`), the hypothesis of
`not_linearTimeTransposable_of_coentLinear_io`; it is formally incomparable with the output-at-end
form (`not_linearTimeTransposable_of_coentLinear_end`). The all-large-`n` targets give it
(`coent_io_of_coent`), and so does `RobustNoCode_TM_io` at the level `n w`
(`coent_io_nw_of_robustNoCode_io`). -/
theorem not_linearTimeTransposable_of_coent_io {f : ℕ → ℕ}
    (hf : ∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) (h : NoCode_TM_coent_io f) :
    ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_coent_io hf h

/-- No code at all large `n` gives no code for infinitely many `n`. -/
theorem coent_io_of_coent {f : ℕ → ℕ} (h : NoCode_TM_coent f) : NoCode_TM_coent_io f :=
  Impl.coent_io_of_coent h

/-- The robust io target gives the io target at co-entropy `C n`, for every `C` (the hypothesis of
`not_linearTimeTransposable_of_coentLinear_io`). -/
theorem coentLinear_io_of_robustNoCode_io (h : RobustNoCode_TM_io) (C : ℕ) :
    NoCode_TM_coent_io (fun n => C * n) :=
  Impl.coentLinear_io_of_robustNoCode_io h C

/-- **The single superlinear io level is equivalent to the linear io family** (a diagonal
argument). -/
theorem coentLinear_io_iff_exists_coent_io :
    (∀ C : ℕ, NoCode_TM_coent_io (fun n => C * n)) ↔
      ∃ f : ℕ → ℕ, (∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) ∧ NoCode_TM_coent_io f :=
  Impl.coentLinear_io_iff_exists_coent_io

/-- The robust io target gives the io target at the superlinear level `n w`. -/
theorem coent_io_nw_of_robustNoCode_io (h : RobustNoCode_TM_io) :
    NoCode_TM_coent_io (fun n => n * entryBits n) :=
  Impl.coent_io_nw_of_robustNoCode_io h

/-- **No fast transposer at any single co-entropy level** (non-uniform, average-case). Under
`NoCode_TM_coent m`, for all `k, g, c, C₁` and all large `n`: no machine with `k` work tapes, alphabet
`g + 1` and at most `2^{C₁ n w}` states (any transition table, which may depend on `n`) outputs the
transposed encoding within `c L` steps on every input of a set `F₀` with `2^L ≤ 2^{m₀} |F₀|`, whenever
`m₀ + K n ≤ m n`, `K = Impl.coarseConst (k+1) (c+4) (max 1 ⌈log₂(g+3)⌉)`. This unifies
`no_fast_transposer_of_coentLinear` and `no_fast_transposer_of_robustNoCode`. -/
theorem no_fast_transposer_of_coent {m : ℕ → ℕ} (h : NoCode_TM_coent m) (k g c C₁ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) ≤ C₁ * (n * entryBits n) →
      ∀ (F₀ : Set (List Bool)) (m₀ : ℕ),
        m₀ + Impl.coarseConst (k + 1) (c + 4) (max 1 (Nat.clog 2 (g + 2 + 1))) * n ≤ m n →
        2 ^ (n * n * entryBits n) ≤ 2 ^ m₀ * F₀.ncard →
        ¬ ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
          ∃ A : Matrix, w = encode n (entryBits n) A ∧
            (run M w T).outRev.reverse = encode n (entryBits n) (transpose A) :=
  Impl.no_fast_transposer_of_coent h k g c C₁

/-- **What each rung of the ladder rules out.** Under `NoCode_TM_coent m`, for all large `n`, every
trace class on which a machine (`k` work tapes, alphabet `g + 1`, at most `2^{C₁ n w}` states,
halting time `T ≤ c L`) outputs the transposed encoding has `2^{m n} |F| < 2^L`. So the plain target
(`m = 0`) rules out machines oblivious at a single large size (non-uniformly), and the rung `m` rules
out machines oblivious and correct on a set of co-entropy `m` (`traceClass_of_obliviousOn`). -/
theorem traceClass_coent_lt {m : ℕ → ℕ} (h : NoCode_TM_coent m) (k g c C₁ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) ≤ C₁ * (n * entryBits n) →
      ∀ (T : ℕ), T ≤ c * (n * n * entryBits n) → ∀ (F : Set (List Bool)) (w₀ : List Bool),
        TraceClass M n (entryBits n) (slotLen M n) T F w₀ →
        (∀ w ∈ F, ∃ A : Matrix, w = encode n (entryBits n) A ∧
          (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) →
        2 ^ m n * F.ncard < 2 ^ (n * n * entryBits n) :=
  Impl.traceClass_coent_lt h k g c C₁

/-- **The γ-form of robust CE_TM is `RobustNoCode_TM`**: "for some `γ(n) = o(log n)` (measured by
`w`), coding beats flow by at most `γ(n)`" (`RobustCE_TM_gamma`). -/
theorem robustCE_TM_gamma_iff : RobustCE_TM_gamma ↔ RobustNoCode_TM :=
  Impl.robustCE_TM_gamma_iff

/-- **The per-constant γ-form** (`γ` may depend on `k, G, c, C`) is equivalent to `RobustNoCode_TM` too. -/
theorem robustCE_TM_gamma_per_iff : RobustCE_TM_gamma_per ↔ RobustNoCode_TM :=
  Impl.robustCE_TM_gamma_per_iff

/-- **The target may assume the output comes at the end**: if for every `C` no code at co-entropy
`C n` exists on the diagrams that append their `L` output bits in their last `L` steps
(`NoCode_TM_coent_end`), then ¬(T). -/
theorem not_linearTimeTransposable_of_coentLinear_end
    (h : ∀ C : ℕ, NoCode_TM_coent_end (fun n => C * n)) : ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_coentLinear_end h

/-- **Output at the end and infinitely many sizes suffice together**: if for every `C` and all
constants, arbitrarily large `n` exist at which no code at co-entropy `C n` exists on the diagrams that
append their `L` output bits in their last `L` steps (`NoCode_TM_coent_end_io`), then ¬(T). The
hypothesis is implied both by that of `not_linearTimeTransposable_of_coentLinear_end` and by that of
`not_linearTimeTransposable_of_coentLinear_io`, which are proved as its corollaries: (T) gives codes
with the output at the end at *every* large `n` (`codes_coentLinear_of_linearTimeTransposable`). -/
theorem not_linearTimeTransposable_of_coentLinear_end_io
    (h : ∀ C : ℕ, NoCode_TM_coent_end_io (fun n => C * n)) : ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_coentLinear_end_io h

/-- **The flow form at co-entropy `C n`** (`RobustCE_TM_lin`, the flow form of the linear rung)
implies no code at co-entropy `C n` for every `C`. -/
theorem coentLinear_of_robustCE_TM_lin (h : RobustCE_TM_lin) :
    ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) :=
  Impl.coentLinear_of_robustCE_TM_lin h

/-- **The flow form at co-entropy `C n` is the linear rung**: `RobustCE_TM_lin` is equivalent to
"no code at co-entropy `C n`, for every `C`" (the converse holds vacuously, since a code within any
capacities in the profile is a code at the profile capacities). -/
theorem robustCE_TM_lin_iff : RobustCE_TM_lin ↔ ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) :=
  Impl.robustCE_TM_lin_iff

/-- **The flow form at co-entropy `C n` refutes (T).** -/
theorem not_linearTimeTransposable_of_robustCE_TM_lin (h : RobustCE_TM_lin) :
    ¬ LinearTimeTransposable :=
  Impl.not_linearTimeTransposable_of_robustCE_TM_lin h

/-! ## Theorem M* for code-carrying diagrams

Theorem M\* (level form (★) for interval labellings) holds for code-carrying time–space diagrams,
with no machine in sight. The machine-free core is `theoremMStar_walk`, the most general form of
Theorem M\*: for any `k` walks of length `T ≤ c L` with unit steps before `T` that satisfy the cut
inequality of Discrete Isoperimetry (`CutIneq`) with `(D + s)/L → 0`, convergent subsequences exist
(if the walks start at `0`) and every subsequential limit is 1-Lipschitz, satisfies (★) and has the
labelling-free properties; `theoremMStar_level_walk` is its level form. A code-carrying diagram
satisfies the cut inequality (`cutIneq_of_solves`, from `isoperimetry_code` and the capacity between
labels, `sum_cross_blockCap_le`). Theorem M\* for machines (oblivious, trace class, adaptive, robust
and non-uniform; `Transpose/Tape/Statements/Core.lean`, `Transpose/Tape/Statements/Adaptive.lean`)
is the instance `runDiagram`, with the state and head positions as `o(L)` extra bits per memory
edge. The generic walk lemmas behind the core (`pairRes_congr`, `frozen_V2`, `numSlots_le_of`,
`blockTraj_limit_lipschitz`, `exists_subseq_blockTraj`) are published too; their machine instances
are in `Transpose/Tape/Statements/Core.lean` (`pairRes_V2`, `numSlots_le_horizon`,
`rescaledTraj_limit_lipschitz`, `exists_subseq_tendstoUniformlyOn`). -/

open MeasureTheory Filter Topology

open scoped ENNReal

/-- **The capacity between labels.** At the block capacities with the per-node profile and `s` extra
bits per memory edge, the edges between different labels of a slot labelling carry at most
`M_b s + r G (3k M_b + Σ_t χ_t)` bits (`M_b` label changes, `χ_t` chords of tape `t` between
different labels). -/
theorem sum_cross_blockCap_le {k : ℕ} (D : TSDiagram k) {L n G s : ℕ} (hD : D.Valid L)
    (hr : 1 ≤ blockSize G n) (lab : ℕ → ℕ) :
    ∑ e ∈ (D.edges (blockSize G n)).filter (fun e => lab e.1 ≠ lab e.2),
        D.blockCap n G (fun y => ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) s e ≤
      labelChanges lab (D.nodes (blockSize G n)) * s +
        blockSize G n * G * (3 * k * labelChanges lab (D.nodes (blockSize G n)) +
          ∑ t, (crossChords (pairRes (blockSize G n) (D.work t) D.T) lab
            (D.nodes (blockSize G n))).card) :=
  Impl.sum_cross_blockCap_le D hD hr lab

/-- **A code-carrying diagram satisfies the cut inequality** of Discrete Isoperimetry (`CutIneq`),
at the block capacities with the per-node profile and `s` extra bits per memory edge, on a set of
co-entropy `≤ D_c`. -/
theorem cutIneq_of_solves {k : ℕ} (D : TSDiagram k) {n G s : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hD : D.Valid (n * n * entryBits n)) {F : Set (Fin (n * n * entryBits n) → Bool)}
    {code : NetCode}
    (hsol : D.Solves n G (D.blockCap n G
      (fun y => ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) s) F code)
    {Dc : ℕ} (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ Dc * F.ncard) :
    CutIneq n G (blockSize G n) D.T Dc s D.work :=
  Impl.cutIneq_of_solves D hG hn hD hsol hco

/-- **The pair residency reads the walk only before `T`**: walks that agree before `T` have the same
pair residency `R_y` at every slot. -/
theorem pairRes_congr {r T : ℕ} {h h' : ℕ → ℤ} (he : ∀ σ < T, h σ = h' σ) (y : ℕ) :
    pairRes r h T y = pairRes r h' T y :=
  Impl.pairRes_eq_of_agree he y

/-- **(V2′) for a frozen walk**: if the block of a unit-step walk frozen at `T`, at the first steps
of slots `y₁ ≤ y₂` (block size `r ≥ 1`), passes strictly over a block `σ`, then `σ` is resident
(pair residency before `T`) at some slot in `[y₁, y₂]`. -/
theorem frozen_V2 {h : ℕ → ℤ} (hh : UnitSteps h) {r T : ℕ} (hr : 1 ≤ r) {y₁ y₂ : ℕ}
    (hy : y₁ ≤ y₂) {σ : ℤ}
    (hσ : curBlock r (fun τ => h (min τ T)) (y₁ * r) < σ ∧
          σ < curBlock r (fun τ => h (min τ T)) (y₂ * r) ∨
        curBlock r (fun τ => h (min τ T)) (y₂ * r) < σ ∧
          σ < curBlock r (fun τ => h (min τ T)) (y₁ * r)) :
    ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ σ ∈ pairRes r h T y :=
  Impl.frozen_V2 hh hr hy hσ

/-- **The number of slots**: `⌈T/r⌉ ≤ (c G + 1) n` when `T ≤ c n² b` and a block holds a row
(`n b ≤ r G`), for `n ≥ 1`. -/
theorem numSlots_le_of {n T r G : ℕ} {c : ℝ} (hn : 1 ≤ n) (hrG : n * entryBits n ≤ r * G)
    (hT : (T : ℝ) ≤ c * inputLength n) :
    (numSlots r T : ℝ) ≤ (c * G + 1) * n :=
  Impl.numSlots_le_of hn hrG hT

/-- **Uniform limits of rescaled block walks are 1-Lipschitz**: if, eventually, the walks have unit
steps and the block sizes are positive, every uniform limit on `[0, c₀]` of the rescaled block
trajectories `blockTraj` is 1-Lipschitz there. -/
theorem blockTraj_limit_lipschitz {c₀ : ℝ} {ns rs : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {hs : ℕ → ℕ → ℤ} (hgood : ∀ᶠ i in atTop, UnitSteps (hs i) ∧ 1 ≤ rs i) {P : ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun i => blockTraj (rs i) (ns i) (hs i)) P atTop
      (Set.Icc 0 c₀)) :
    LipschitzOnWith 1 P (Set.Icc 0 c₀) :=
  Impl.blockTraj_limit_lipschitz hns hgood hconv

/-- **Arzelà–Ascoli for block walks**: if, eventually, the block sizes are positive and the `k`
walks have unit steps and start at `0`, a subsequence of the rescaled block trajectories converges
uniformly on `[0, c₀]`. -/
theorem exists_subseq_blockTraj {k : ℕ} (c₀ : ℝ) {ns rs : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {hs : ℕ → Fin k → ℕ → ℤ}
    (hgood : ∀ᶠ i in atTop, 1 ≤ rs i ∧ ∀ t, UnitSteps (hs i t) ∧ hs i t 0 = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => blockTraj (rs (φ i)) (ns (φ i)) (hs (φ i) t)) (P t) atTop
        (Set.Icc 0 c₀) :=
  Impl.exists_subseq_blockTraj c₀ hns hgood

/-- **Theorem M\* for walks** (the machine-free core, and the most general form of Theorem M\*). At
sizes `n_i → ∞`, let `k` walks `h_i t` have unit steps before `T_i` and length `T_i ≤ c L_i`, and
satisfy the cut inequality (blocks of `r_i = blockSize G n_i` cells of `G` bits) with co-entropy
`D_i` and `s_i` bits per label change, where `(D_i + s_i)/L_i → 0`. Then:
* if the walks start at `0`, their rescaled block walks frozen at `T_i` have a uniformly convergent
  subsequence on `[0, c₀]`, `c₀ = c G + 1`;
* every subsequential limit `P` is 1-Lipschitz, satisfies (★) for every `θ`, `S` and `β`, has total
  excess level multiplicity `Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1` and total range
  `1 + Σ_t |P_t([0, c₀])| ≤ k c₀`, and is not monotone on every tape.

No `G ≥ 1` is assumed (at `G = 0` the hypotheses are contradictory for large `i`), and the walks
after `T_i` are unconstrained: the cut inequality reads them only before `T_i` (`pairRes_congr`),
and the convergence concerns the frozen walks. Every other asymptotic form of Theorem M\* is an
instance. -/
theorem theoremMStar_walk {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ts Ds ss : ℕ → ℕ} {hs : ℕ → Fin k → ℕ → ℤ}
    (hunit : ∀ᶠ i in atTop, ∀ t, ∀ τ < Ts i, |hs i t (τ + 1) - hs i t τ| ≤ 1)
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    (hcut : ∀ᶠ i in atTop, CutIneq (ns i) G (blockSize G (ns i)) (Ts i) (Ds i) (ss i) (hs i))
    (hDL : Tendsto (fun i => ((Ds i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0)) :
    ((∀ᶠ i in atTop, ∀ t, hs i t 0 = 0) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns (φ i))) (ns (φ i))
        (fun τ => hs (φ i) t (min τ (Ts (φ i))))) (P t) atTop (Set.Icc 0 (c * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns (φ i))) (ns (φ i))
        (fun τ => hs (φ i) t (min τ (Ts (φ i))))) (P t) atTop (Set.Icc 0 (c * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
      (∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (c * G + 1) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
          2 * k * volume (S ∩ Set.Icc 0 (c * G + 1))) ∧
      1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (c * G + 1) p ∧
      1 + ∑ t, volume (P t '' Set.Icc 0 (c * G + 1)) ≤ k * ENNReal.ofReal (c * G + 1) ∧
      ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (c * G + 1)) ∨
        AntitoneOn (P t) (Set.Icc 0 (c * G + 1)) :=
  Impl.theoremMStar_walk hns hunit htime hcut hDL

/-- **Theorem M\* for walks, level form** (the case `φ = id` of `theoremMStar_walk`). At sizes
`n_i → ∞`, let `k` walks `h_i t` have unit steps before `T_i` and length `T_i ≤ c L_i`, and satisfy
the cut inequality (blocks of `r_i = blockSize G n_i` cells of `G` bits) with co-entropy `D_i` and
`s_i` bits per label change, where `(D_i + s_i)/L_i → 0`. If their rescaled block walks, frozen at
`T_i`, converge uniformly to `P` on `[0, c₀]`, `c₀ = c G + 1`, then
`1 ≤ Σ_t ∫⁻ κ_t + 2θ + 2k |S ∩ [0, c₀]|`. The cut inequality and the unit steps concern the walks
before `T_i` (`CutIneq` reads them only there, `pairRes_congr`), the convergence their frozen
versions. -/
theorem theoremMStar_level_walk {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ts Ds ss : ℕ → ℕ} {hs : ℕ → Fin k → ℕ → ℤ}
    (hunit : ∀ᶠ i in atTop, ∀ t, ∀ τ < Ts i, |hs i t (τ + 1) - hs i t τ| ≤ 1)
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    (hcut : ∀ᶠ i in atTop, CutIneq (ns i) G (blockSize G (ns i)) (Ts i) (Ds i) (ss i) (hs i))
    (hDL : Tendsto (fun i => ((Ds i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0))
    {P : Fin k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns i)) (ns i)
      (fun τ => hs i t (min τ (Ts i)))) (P t) atTop (Set.Icc 0 (c * G + 1)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (c * G + 1))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
      2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) :=
  Impl.theoremMStar_level_walk hns hunit htime hcut hDL hconv hS hβ hclass

/-- **Theorem M\* for code-carrying diagrams** (level form, any `θ`). Let valid `k`-walk diagrams
`D_i` of length `≤ c L_i` (sizes `n_i → ∞`) carry causal codes solving complete exchange on sets of
co-entropy `m_i` at the block capacities (per-node profile, `G ≥ 1` bits per cell) plus `s_i` bits per
memory edge, with `(m_i + s_i)/L_i → 0`. If their rescaled work walks (`TSDiagram.rescaled`) converge
uniformly to `P` on `[0, c₀]`, `c₀ = c G + 1`, then `1 ≤ Σ_t ∫⁻ κ_t + 2θ + 2k |S ∩ [0, c₀]|`. -/
theorem theoremMStar_level_diagram {k G : ℕ} (hG : 1 ≤ G) {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ds : ℕ → TSDiagram k}
    {Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)} {codes : ℕ → NetCode}
    {ms ss : ℕ → ℕ}
    (hvalid : ∀ᶠ i in atTop, (Ds i).Valid (ns i * ns i * entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, ((Ds i).T : ℝ) ≤ c * inputLength (ns i))
    (hco : ∀ᶠ i in atTop, 2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ ms i * (Fs i).ncard)
    (hsol : ∀ᶠ i in atTop, (Ds i).Solves (ns i) G ((Ds i).blockCap (ns i) G
      (fun y => ∑ t, (pairRes (blockSize G (ns i)) ((Ds i).work t) (Ds i).T y).card) (ss i))
      (Fs i) (codes i))
    (hsmall : Tendsto (fun i => ((ms i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0))
    {P : Fin k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => (Ds i).rescaled (ns i) G t) (P t) atTop
      (Set.Icc 0 (c * G + 1)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (c * G + 1))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
      2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) :=
  Impl.theoremMStar_level_diagram hG hns hvalid htime hco hsol hsmall hconv hS hβ hclass

/-- **Theorem M\* for code-carrying diagrams.** Under the hypotheses of `theoremMStar_level_diagram`,
the rescaled work walks have a uniformly convergent subsequence on `[0, c₀]`, and every
subsequential limit is 1-Lipschitz and satisfies (★) for every `θ`, every finite union `S` of closed
intervals and every labelling `β` of `[0, c₀] ∖ S` constant on finitely many intervals with label
classes of measure `≤ θ`. -/
theorem theoremMStar_diagram {k G : ℕ} (hG : 1 ≤ G) {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ds : ℕ → TSDiagram k}
    {Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)} {codes : ℕ → NetCode}
    {ms ss : ℕ → ℕ}
    (hvalid : ∀ᶠ i in atTop, (Ds i).Valid (ns i * ns i * entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, ((Ds i).T : ℝ) ≤ c * inputLength (ns i))
    (hco : ∀ᶠ i in atTop, 2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ ms i * (Fs i).ncard)
    (hsol : ∀ᶠ i in atTop, (Ds i).Solves (ns i) G ((Ds i).blockCap (ns i) G
      (fun y => ∑ t, (pairRes (blockSize G (ns i)) ((Ds i).work t) (Ds i).T y).card) (ss i))
      (Fs i) (codes i))
    (hsmall : Tendsto (fun i => ((ms i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 (c * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 (c * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
      ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (c * G + 1) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
          2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) :=
  Impl.theoremMStar_diagram hG hns hvalid htime hco hsol hsmall

/-- **Theorem M\* for code-carrying diagrams at the profile capacities**, with the labelling-free
consequences: for codes at `profileCap` on sets of co-entropy `m_i = o(L_i)`, every subsequential
limit `P` of the rescaled work walks is 1-Lipschitz, satisfies (★), has total excess level
multiplicity `Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1` and total range `1 + Σ_t |P_t([0, c₀])| ≤ k c₀`, and is
not monotone on every tape; and a convergent subsequence exists. -/
theorem theoremMStar_diagram_profile {k G : ℕ} (hG : 1 ≤ G) {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ds : ℕ → TSDiagram k}
    {Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)} {codes : ℕ → NetCode}
    {ms : ℕ → ℕ}
    (hvalid : ∀ᶠ i in atTop, (Ds i).Valid (ns i * ns i * entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, ((Ds i).T : ℝ) ≤ c * inputLength (ns i))
    (hco : ∀ᶠ i in atTop, 2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ ms i * (Fs i).ncard)
    (hsol : ∀ᶠ i in atTop, (Ds i).Solves (ns i) G ((Ds i).profileCap (ns i) G) (Fs i) (codes i))
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 (c * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 (c * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
      (∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (c * G + 1) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
          2 * k * volume (S ∩ Set.Icc 0 (c * G + 1))) ∧
      1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (c * G + 1) p ∧
      1 + ∑ t, volume (P t '' Set.Icc 0 (c * G + 1)) ≤ k * ENNReal.ofReal (c * G + 1) ∧
      ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (c * G + 1)) ∨ AntitoneOn (P t) (Set.Icc 0 (c * G + 1)) :=
  Impl.theoremMStar_diagram_profile hG hns hvalid htime hco hsol hmL

/-- **Every family of counterexamples to the Tape Coding Conjecture satisfies (★).** Fix `k`,
`G ≥ 1`, `c`, `C` and sizes `n_i → ∞`, and at every large `n_i` a counterexample to
`RobustNoCode_TM` at these constants: a valid `k`-walk diagram of length `≤ c L_i` whose block
network carries a causal code solving complete exchange at the profile capacities on a set of
co-entropy `≤ C n_i w_i`. Then the rescaled walks have a uniformly convergent subsequence on
`[0, c₀]`, `c₀ = c G + 1`, and every subsequential limit is 1-Lipschitz, satisfies (★), has total
excess level multiplicity `≥ 1` and total range `≤ k c₀ − 1`, and is not monotone on every tape. So
a refutation of the Tape Coding Conjecture must produce head motions whose limits satisfy (★). -/
theorem mstar_of_robustNoCode_counterexamples {k G c C : ℕ} (hG : 1 ≤ G) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ds : ℕ → TSDiagram k}
    {Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)} {codes : ℕ → NetCode}
    (hcex : ∀ᶠ i in atTop, (Ds i).Valid (ns i * ns i * entryBits (ns i)) ∧
      (Ds i).T ≤ c * (ns i * ns i * entryBits (ns i)) ∧
      2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ (C * ns i * entryBits (ns i)) * (Fs i).ncard ∧
      (Ds i).Solves (ns i) G ((Ds i).profileCap (ns i) G) (Fs i) (codes i)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 ((c : ℝ) * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 ((c : ℝ) * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 ((c : ℝ) * G + 1))) ∧
      (∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
        PiecewiseConstOn β S ((c : ℝ) * G + 1) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 ((c : ℝ) * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β ((c : ℝ) * G + 1) p) + 2 * θ +
          2 * k * volume (S ∩ Set.Icc 0 ((c : ℝ) * G + 1))) ∧
      1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) ((c : ℝ) * G + 1) p ∧
      1 + ∑ t, volume (P t '' Set.Icc 0 ((c : ℝ) * G + 1)) ≤
        k * ENNReal.ofReal ((c : ℝ) * G + 1) ∧
      ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 ((c : ℝ) * G + 1)) ∨
        AntitoneOn (P t) (Set.Icc 0 ((c : ℝ) * G + 1)) :=
  Impl.mstar_of_robustNoCode_counterexamples hG hns hcex

/-- **Counterexamples to the Tape Coding Conjecture, and their limits.** If `RobustNoCode_TM`
fails, there are `k`, `G ≥ 1`, `c`, `C` and, at sizes `n_i ≥ i`, counterexamples at these
constants: valid `k`-walk diagrams of length `≤ c L_i` whose block networks carry causal codes
solving complete exchange at the profile capacities on sets of co-entropy `≤ C n_i w_i`. Their
rescaled walks have a uniformly convergent subsequence on `[0, c₀]`, `c₀ = c G + 1`, and every
subsequential limit is 1-Lipschitz, satisfies (★), has total excess level multiplicity `≥ 1` and
total range `≤ k c₀ − 1`, and is not monotone on every tape. (Every family of counterexamples has
such limits: `mstar_of_robustNoCode_counterexamples`.) -/
theorem mstar_of_not_robustNoCode (h : ¬ RobustNoCode_TM) :
    ∃ (k G c C : ℕ) (ns : ℕ → ℕ) (Ds : ℕ → TSDiagram k)
      (Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)) (codes : ℕ → NetCode),
      1 ≤ G ∧ (∀ i, i ≤ ns i) ∧
      (∀ i, (Ds i).Valid (ns i * ns i * entryBits (ns i)) ∧
        (Ds i).T ≤ c * (ns i * ns i * entryBits (ns i)) ∧
        2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ (C * ns i * entryBits (ns i)) * (Fs i).ncard ∧
        (Ds i).Solves (ns i) G ((Ds i).profileCap (ns i) G) (Fs i) (codes i)) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
          (Set.Icc 0 ((c : ℝ) * G + 1))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
          (Set.Icc 0 ((c : ℝ) * G + 1))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 ((c : ℝ) * G + 1))) ∧
        (∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
          PiecewiseConstOn β S ((c : ℝ) * G + 1) →
          (∀ ℓ, volume {u | u ∈ Set.Icc 0 ((c : ℝ) * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
          1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β ((c : ℝ) * G + 1) p) + 2 * θ +
            2 * k * volume (S ∩ Set.Icc 0 ((c : ℝ) * G + 1))) ∧
        1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) ((c : ℝ) * G + 1) p ∧
        1 + ∑ t, volume (P t '' Set.Icc 0 ((c : ℝ) * G + 1)) ≤
          k * ENNReal.ofReal ((c : ℝ) * G + 1) ∧
        ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 ((c : ℝ) * G + 1)) ∨
          AntitoneOn (P t) (Set.Icc 0 ((c : ℝ) * G + 1)) :=
  Impl.mstar_of_not_robustNoCode h

end Transpose.Tape
