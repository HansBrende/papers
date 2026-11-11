# Independent English–Lean review

Historical scope: the independent review below covers the nine-module checkpoint
before the subsequent `SlabGeometry` addition. The authoring addendum at the end
records that later work and does not claim an independent review of it.

Status: PASS for the stated formalization scope, after the two precision fixes
below. This is a working-draft review, not a finding that the native headline
theorems or every feasible subsidiary step have been formalized.

The reviewer read `../CONTRIBUTING.md`, all nine paper Lean modules, the five
shared modules listed below, and every formal or partial formal-status statement
and its outline. The review also inspected the frozen native transition and the
three imported slab/stripe declarations used in the manuscript. It was
independent of the authorship of those Lean proofs. The reviewer made the
finite-window wording clarification and the formalization-backlog clarification;
the exact scanned-write lemma was added separately in response to this review.

This review concerns statement fidelity and proof scope. The separate
`proof-review.md` records the complete written-proof and citation review. Final
package builds, axiom execution and PDF checks are separate integration checks;
no independent broad build or external-priority search is claimed here.

## Resolved findings

1. The original `step_work_update` identified the old address as the only
   possible changed cell, but expressed the new scanned value using the resulting
   configuration itself. It did not alone state that this value is the transition
   instruction's prescribed write. The new, cited `step_scanned_write` explicitly
   takes the actual instruction witness and proves that equality by unfolding
   `Transpose.step`. The old-position lemma now matches all three English claims.
2. The persistent-cell declarations use `nonblankWithin`, a finite-window
   support. The English formal lemma now says this explicitly. Its application
   to a whole finite execution uses a window containing its live cells, as the
   outline already explained. No persistence, independence or future-use claim
   was strengthened.
3. The README and formalization appendix now distinguish ordinary unfinished
   counting and selection steps from the substantial native execution
   constructions. Neither a small kernel nor a successful library build is
   described as proving its native headline theorem.

## Complete formal-status inventory

The current inventory has nine formal lemmas and two partial theorems. Their
status lines cite 25 distinct paper declarations; three additional imported
geometry declarations are named and included in the generated audit.

| Result | Actual checked statement and boundary |
|---|---|
| Old-position writes (`model.tex`) | `step_work_update`, `step_scanned_write` and `step_preserves_unscanned` concern actual successful frozen-model steps. `instruction_eq_of_old_tuple` fixes the complete instruction from old state, raw symbol and scanned tuple; neither output history nor unobserved cells is an argument to the table. |
| Incoming first reads (`replay.tex`) | `outside_first_read_is_long_return` proves `p < a < t`, the imported consecutive-visit `IsHop`, and the strict excursion witness at `a`. Its premises are the actual first-visit and last-visit conditions. It does not assume a decoder or a common trace, and loses no unit in the threshold. |
| Joint sparse records (`replay.tex`) | `SizedImports` and `SparseImports` are explicit finite record types. The exact counts are `choose n j * A^j` and their sum through `J`; the terms above `n` vanish. `replay_message_bound` visibly requires an injective encoder. It does not construct the native encoder or assume its injectivity without disclosure. |
| Finite adaptive replay (`replay.tex`, partial) | `ExecutionPrefix.filtered_native_read` checks the current-version ingredient. The stated gap names the variable-message decoder, joint reconstruction induction and input injection. The complete native replay/counting statement remains written. |
| Fragment starts (`fragments.tex`) | `StateClosedExcept` and `LocallyStateClosedExcept` express precisely the predecessor closure in the text. Run starts lie among zero/cut successors, or selected-set starts/cut successors, giving the displayed global and localized counts. |
| Current versions suffice (`fragments.tex`) | `filtered_read_correct` retains the actual last writer when one exists. The native adapter proves the work dictionary identity from initialization and actual successful steps. Written values are actual execution values; reconstructing those values from a message is outside this lemma. No whole-memory equality after skipped writes is asserted. |
| Finite adaptive input-cut bound (`fragments.tex`, partial) | Only the cited fragment-count kernel is certified here. The gap explicitly retains the adaptive encoder, sparse geometry menu and injection. The equation for the native bad-input count is not a Lean theorem. |
| Persistent unchanged cells (`storage.tex`) | Both support inequalities and `untouched_cell_constant` apply to actual successful steps. `persistent_cells` removes at most the interval's duration many touched addresses from terminal support in an arbitrary finite window and preserves the survivors at every intermediate configuration time. |
| Protected cores and paid fringes (`clusters.tex`) | The actual floor/ceiling sets, selected-position coverage, outside avoidance, disjointness and total cardinality bounds are proved. The adapter supports separate nonnegative integer allowances for different heads; the uniform ceiling allowance in the text is its specialization. |
| Finite order-conflict chart (`clusters.tex`) | `finite_order_chart` uses the literal finite maximum defining the conflict and supplies a chart on all real arguments, monotone and 1-Lipschitz in each coordinate, with exact normalized sum and both error bounds at the original vector sums. `order_conflict_le_two_error` proves the converse. |
| One subset for every context (`persistence.tex`) | The aliases expose actual nonnegative finite weights, total mass one, one common retained subset and the attained-context lower-density bounds. The half-mass theorem quantifies over every observed event on that same subset. Conditional bounds require positive denominator, matching the text's attained positive-probability convention; zero-weight atoms are allowed. |

The imported `exists_offset_slabTransitions_le`,
`exists_slab_chunk_dichotomy` and
`outIn_card_le_two_indep_add_six_runs` have the interfaces the text uses:
unit-walk offset averaging, a finite short/long chunk dichotomy, and an
arbitrary-positive-width stripe inequality. They do not require an oblivious
trace. The draft correctly leaves its particular slab-margin assembly written.

## Independent check of the new finite geometry

`LeanMachine.ProtectedIntervals` defines a closed real interval's integer set
as `Icc (ceil a) (floor b)` and the strict core as
`Ioo (floor (a + j)) (ceil (b - j))`. The membership lemmas prove exactly the
real inequalities in the paper. Core boundaries belong to the closed fringes.
Coverage and disjointness also cover an empty core or overlapping fringes.
The cardinality proof first bounds a closed interval by its length plus one;
the two fringe intervals contribute at most `4*j + 2`. In the paper adapter,
monotonicity supplies the endpoint order for nonnegative slab width, and the
normalized coordinate sum supplies the total core bill `W + card I`.
The outside lemma includes the upper slab boundary. A native old-position
write therefore cannot touch a protected core during an outside step. No
encoding of a real-valued chart is hidden in these definitions: four rounded
endpoints determine each head's two sets.

`MonotoneNormalization` proves that ordering the sums of a coordinatewise
monotone curve orders every coordinate. This both removes the ambiguity of
choosing a preimage on a flat segment and bounds every coordinate increment
by the total increment. The resulting functions are normalized and
1-Lipschitz, and preserve every original curve point.

`MonotoneChainEnvelope` supplies the needed continuous monotone curve through
an arbitrary nonempty finite coordinatewise chain. Its max-envelope hits
every knot; the selected coordinate's right tail and the common left tail
make the coordinate sum surjective. The intermediate value theorem, followed
by normalization, gives exact normalized knots. No distinct-knot-sum or strict
chain assumption is present.

`OrderConflictChart` forms prefix maxima over all vectors whose sums are at
most the current sum. Thus tied sums are handled without choosing an arbitrary
tie order. The prefix vectors form a chain and lie between each original
coordinate and that coordinate plus its conflict allowance. Importantly, the
final error is evaluated at the original sum, not the larger prefix-vector
sum: monotonicity gives its upper bound, and zero total error gives its lower
bound. The literal `orderConflict` includes zero for unordered pairs; this
does not change the stated maximum, since every diagonal ordered pair
contributes zero. The time family and coordinate type are both finite and
nonempty, exactly matching the corrected English hypotheses. The separate
`coordinate_conflict_chart` alias proves the stronger per-coordinate version
claimed in the README. The converse needs only monotonicity and two errors;
normalization and Lipschitz continuity are unnecessary extra hypotheses.

## Remaining formalization scope

The missing adaptive decoder, dynamic-carrier transition table, catalogue
handoffs, prefix-assisted execution, last-visit eraser, redundant-archive
wrapper, and guarded simulator/source correspondences are real native
construction obligations. Existing batch-simulator correctness does not
implement these protocols. Leaving them written is not the same as assuming
an abstract structural inequality and formalizing only its consequences.

Ordinary mathematical work also remains in those theorem chains:

- The exact slab-margin arithmetic and its finite parameter bounds.
- The sparse sampled-position, weak-composition and monotone-counter menus,
  and the metadata products. These can be formalized for abstract finite
  records before constructing the adaptive encoder.
- Binary linear-hash separation of sparse words and one common hash that
  succeeds on a sufficiently large source subset. These are finite counting
  lemmas; their use by an actual native table is a separate construction.
- Top-set atom bounds, tape-word graph-ball cardinality, common pair/time-grid
  selection, and the resulting catalogue-size bills. The context-pruning
  theorem already formalizes one important step, not this whole selection.
- Sparse-binomial estimates, attained-small-fibre counting, logarithmic
  overhead bounds and the uniform asymptotic choices of constants and dimension
  thresholds.

These are not independently weeks-scale compiler projects. Shared
`LeanMachine.GraphBall` and `LeanMachine.FinitePartition` already provide
relevant general ball and attained-fibre bounds, although their required
adapters and the exact inequalities used here remain to be checked. The draft
does not therefore receive a blanket clearance that every feasible subsidiary
formalization is finished. The README and appendix now state this distinction.

No source inspected in the nine paper modules or five shared modules below
contains an admitted proof, an extra axiom, `native_decide` or unsafe code.
The generated index and axiom source name the formal-status declarations,
including the newly added `step_scanned_write`. This source inspection does
not itself substitute for running the final axiom audit.

## Separate integration results inspected

After the scanned-write addition, the separate final integration run completed
the Lean package build successfully, with 9,258 jobs and no warnings. The
reviewer inspected its build log and complete axiom output rather than
repeating that build. All 28 generated audit requests occurred exactly once
in the output, and their dependencies were subsets of `propext`,
`Classical.choice` and `Quot.sound`. The nine-module root imports the new
protected-core and order-chart adapters. All 14 reviewed Lean hashes below
still matched the files at the end of this review. These checks certify the
listed Lean statements; they do not certify the written-only native results
or replace PDF verification.

## Reviewed Lean source pins

Paths are relative to this paper. Each listed file was read completely.

| File | SHA-256 |
|---|---|
| `lean/AdaptiveTransfer/NativeWrites.lean` | `c49dc2d94f16256a281b473404bbe8beea1c7362d7215c8707df69ac48b203b2` |
| `lean/AdaptiveTransfer/CurrentVersion.lean` | `f0f256c4855a6610fff6bcb6a0179daab1ad531382fdf9c120a36212fe43c9f1` |
| `lean/AdaptiveTransfer/Fragments.lean` | `408d12961655959a2a82210e78791ecd121708d06461fecde37ab8866a9863b1` |
| `lean/AdaptiveTransfer/IncomingReturns.lean` | `791745a6d7758808a96ab37d2f29d15cb1b3ee9402c5141fa9125df7e3e0ee26` |
| `lean/AdaptiveTransfer/RecordCounts.lean` | `033c0b0777c5f3fb5292597e66ffa017f0ea7ff85e7aaf9e797206871aec6e02` |
| `lean/AdaptiveTransfer/Storage.lean` | `efff6110f89c83c8ca717715b8b7addaccad85ae3977d972e4bf4cbdeae4a289` |
| `lean/AdaptiveTransfer/ContextPruning.lean` | `257059decaed50518f00ff212b43e888576945d546618e01511b74c495a256ab` |
| `lean/AdaptiveTransfer/ProtectedCores.lean` | `38e3c33a3ceff0ece88d69533f76bd34ee870defcd86c0a970cd2805212e0480` |
| `lean/AdaptiveTransfer/OrderChart.lean` | `572ef637cb2f158631569ec96ea8e9a1cfb23eca7f4d96b884b425378c83da3b` |
| `../lean-machine/LeanMachine/ContextPruning.lean` | `660e31f9db2ce7643f7fc36f67b786f0d4881b186669759f6b704f3380e92507` |
| `../lean-machine/LeanMachine/ProtectedIntervals.lean` | `b9cf785435b26ab8f59962c85f03a96892e9d855addf61eea5483eca57774625` |
| `../lean-machine/LeanMachine/MonotoneNormalization.lean` | `241220f1669439477ccf0277b2f10da608442e71cbaf01fa25577316539487c5` |
| `../lean-machine/LeanMachine/MonotoneChainEnvelope.lean` | `5c02bec3ae93c5e3cea8ea7a1767cd92b0cc2447e6b939b402a433bb3a161dc8` |
| `../lean-machine/LeanMachine/OrderConflictChart.lean` | `ab6ccdce8ea30b9dacbbc9d36e2838d4710183c59c88d5bb694cc0fc836b4a14` |

## Subsequent slab-geometry authoring addendum

After completing the independent review above, this reviewer was asked to
formalize the remaining numbered finite slab-geometry lemma and authored
`lean/AdaptiveTransfer/SlabGeometry.lean` and its revised formal-proof outline.
This addendum discloses that authorship; it is not independent verification of
the new code. The original inventory, build count and source pins above remain
a historical record of the pre-authoring checkpoint.

The new `exists_slab_geometry` constructs a literal half-open slab chunk from
the imported offset-averaging, short/long dichotomy and stripe inequalities.
It proves the exact width `ceil(P/(80*a*c))`, run cap
`floor(160*a*c^2) + 1`, half-length bound and snapshot-adjusted margin
`P/(4*N) - 3*N*d*b - a`. The zero-start short case pays no snapshot; the long
case pays at most the slab width. The omitted-coordinate set is the actual
transpose image of selected output ordinals minus the selected raw-read set.
No hypothesis assumes the desired chunk or its margin.

The new `native_slab_geometry` obtains the required runtime, actual unit head
walks and strictly increasing append times from `TransposesInput` for the one
input under consideration. Its trace is that input's own trace; neither
all-input correctness nor a common trace is assumed. It supports arbitrary
positive entry width and every `P >= 2`, with the exact constants above. This
closes the finite slab-margin assembly listed in the historical backlog; it
does not close the adaptive replay encoder or any later native headline proof.

The targeted command `lake env lean AdaptiveTransfer/SlabGeometry.lean`
completed successfully without warnings. The module and the numbered lemma's
formal status and outline were then handed to the separate integration and
independent review steps. This addition contributes one module and two cited
declarations; the earlier independent review's counts do not include them.

| Authored file | SHA-256 |
|---|---|
| `lean/AdaptiveTransfer/SlabGeometry.lean` | `4995f3d9b6d23d0b75101f6ae9fddf153f61b84a7fea8f5ed5a4eeb1208b204f` |
| `paper/sections/returns.tex` | `3fe0f11cf8c01f401a8bc03d700ad1732f7603b305c318211f5a9fa545e679ad` |
