# Closure and entropy: proof status and remaining work

15 November 2026. This is a verification index, not a new capacity theorem.
The [conditional machine-exclusion table](conditional-machine-exclusions.md)
records exactly which additional native hypotheses would let the existing
code results exclude a machine class. The native common-deficit hypothesis
is still open. The task-ready target is [`Wall.Conjecture`](../Wall.lean),
with verified implication from the original wall and verified adaptive
consumer. Strict non-equivalence between the open statements is unproved.
The [conditional bridge closure audit](#conditional-bridge-closure-audit)
separates the frozen checker's import replay from its target axiom filter.

| Item | Lean coverage | What remains |
|---|---|---|
| Known whole-row bounds (Paper 21, Proposition 2.5) | Shared [OrderAverage](../../lean-machine/LeanMachine/WholeRow/OrderAverage.lean) and [OrderCode](../../lean-machine/LeanMachine/WholeRow/OrderCode.lean) prove the rectangular order-average bound, retaining the actual incidence count, and code cardinality. The [paper adapter](../../Tape-Transposition-and-the-Matrix-Coding-Conjecture/lean/MatrixCoding/KnownBounds.lean) gives the finite power bound, the real exponent, the window-one bound and the limiting rate w/(w+1) uniformly over every finite alphabet. | The sharper window-two bound remains Paper 17's written multigraph-ranking proof; it is not formalized by this unit. |
| Induced-matching parity partitions (Paper 21, Proposition 10.1) | Shared [InducedMatchings](../../lean-machine/LeanMachine/WholeRow/InducedMatchings.lean) proves the arbitrary-cutoff large-block count, both square-root bounds, exact syndrome sizes and recovery. The [paper adapter](../../Tape-Transposition-and-the-Matrix-Coding-Conjecture/lean/MatrixCoding/InducedMatchings.lean) uses the whole-row predicate and proves the alphabet-uniform finite threshold d ≥ nw + 25w³n² for rate at most 1/2 + 1/n. The balanced bound gives half rate for w = o(d^(1/3)), including mixed block sizes. | None for these finite statements. The asymptotic sentence is their elementary consequence. Overlapping mutual checks and arbitrary codes are not covered. |
| Whole-row bounds to robust block TCC and adaptive exclusion | [BlockIntervalWalk](../BlockIntervalWalk.lean) and [BlockCut](../BlockCut.lean) embed the actual block graph in unit-speed walk dependencies and project Paper 14’s cut. [BlockCodeLocal](../BlockCodeLocal.lean), [BlockCutPrice](../BlockCutPrice.lean), [BlockRowGrouping](../BlockRowGrouping.lean) and [BlockCodeTransfer](../BlockCodeTransfer.lean) give local determination, pricing, grouping and fibres. [BlockCodeInvoice](../BlockCodeInvoice.lean) retains arbitrary coentropy and sharp price (4kG+1)r per cut slot. [WholeRowTCC](../WholeRowTCC.lean) proves robust/plain TCC and adaptive exclusion from a common deficit. [BlockEndRows](../BlockEndRows.lean) removes exceptional columns for final output; [WeakWholeRowTCC](../WeakWholeRowTCC.lean) proves adaptive exclusion under the [finite cofinal criterion](block-tcc-from-whole-row.md#8-the-weakened-adaptive-only-hypothesis), also normalized two-sided, permitting dimension-dependent windows and deficits and only one explicit coentropy allowance. [FiniteWholeRowPayments](../FiniteWholeRowPayments.lean) retains integer cut size and exact cross overlap; [Wall](../Wall.lean) states the final open target and proves both comparison arrows and its adaptive consumer. | No missing step in these implications. The capacity hypotheses and converse remain open. The weaker criterion claims adaptive exclusion, not full robust TCC. The slow-decay asymptotic corollary, o(L)-coentropy extension and smaller directed-cone window remain written. The original one-window oblivious invoice remains in [RowSpreadCrux](../RowSpreadCrux.lean). |
| Sparse-recovery rank and affine-code bounds | Original triangle-free endpoints already in Paper 4; Paper 10 S* also covers nonlinear recovery under the stronger no-transitive-triangle premise. [SparseRankBounds.lean](../../lean-machine/LeanMachine/SparseRankBounds.lean) proves N ≤ k rank for nonzero diagonal, outgoing width k ≥ 2 and the weaker four-arc exclusion. [ThreeHelperRank.lean](../../lean-machine/LeanMachine/ThreeHelperRank.lean) proves half at width three with the one-way-head premise, including the sharper rooted charge N + 2 ≤ 2 rank + outdeg(root) for rank ≥ 2. Both reuse one hereditary closed-cut induction. [SparseAffineCodes.lean](../../lean-machine/LeanMachine/SparseAffineCodes.lean) proves the cardinality consequences for finite alphabets embedded coordinatewise in any field, allowing arbitrary subsets of an affine fibre. The local last-row lemma retains semiring/no-zero-divisor generality. | None for these statements. Arbitrary nonlinear recovery under the weaker pattern and native extraction are not proved. No new verification of the original scalar endpoint is claimed. |
| Triangle-free subcubic nonlinear and soft bounds | [SubcubicReuse.lean](../SubcubicReuse.lean) composes existing `HalfRate.n3_decomp`, `rateBound_n3` and `SoftRecovery.soft_half`; asymmetric helper subsets use diminishing returns. Exact weighted half and recovery-error coefficient one hold for arbitrary polymatroids. | None for these statements. The original Target B was already proved in Paper 7; no new Petersen/twelve-vertex LP is needed. Coordinate-graph support is an extra native premise, not whole-row window three. |
| Matching plus one helper | [MatchingSeed.lean](../../lean-machine/LeanMachine/MatchingSeed.lean) proves Hall selection meeting all extra-helper traps, retaining any one prescribed endpoint of a perfect matching. [InvolutionCompletion.lean](../../lean-machine/LeanMachine/InvolutionCompletion.lean) preserves existing pairs when completing an even-size matching. [MatchingRecovery.lean](../../lean-machine/LeanMachine/MatchingRecovery.lean) proves an exact ⌊N/2⌋ determining set for partial matchings and arbitrary nonlinear recovery, plus the all-alphabet code bound and the attained-range price for a varying boundary record. | None for these statements. The matching and loopless extra-helper sets are fixed across the code; neither native extraction nor value-dependent helper choices are asserted. |
| Pairing and parity-template extensions | [CosetRecords.lean](../../lean-machine/LeanMachine/CosetRecords.lean) proves exact attained-record counting. [DisjointSumsExtension.lean](../../lean-machine/LeanMachine/DisjointSumsExtension.lean) proves local extension. [DisjointSumsRecords.lean](../../lean-machine/LeanMachine/DisjointSumsRecords.lean) proves ordinary-sum separation under a chosen-view cover criterion. [DisjointSumsCompatibility.lean](../../lean-machine/LeanMachine/DisjointSumsCompatibility.lean) derives compatibility from recovery and kernel invariance and gives separation/counting with only fully-viewed/all-incident record enclosures. [DisjointSumsWeighted.lean](../../lean-machine/LeanMachine/DisjointSumsWeighted.lean) transports compatibility, separation and exact counting to coordinatewise additive-automorphism weights. Local extraction needs a nonempty code and nontrivial alphabet but no finite block index; global wrappers need finitely many blocks and allow empty codes and trivial alphabets. Coordinate types and additive alphabets may be infinite in the general identities; explicit finite kernel/fibre and record-power bounds are also proved. [InvolutionSums.lean](../../lean-machine/LeanMachine/InvolutionSums.lean) constructs oriented pairs, identifies their weighted kernel with orbit-constant shifts, proves its size q^((N+f)/2), and specializes exact separation/counting to arbitrary recovery views. [DisjointSumsPinned.lean](../../lean-machine/LeanMachine/DisjointSumsPinned.lean) adjoins singleton blocks, identifies the kernel with active shifts vanishing on prescribed coordinates, and proves separation, exact attained-record counting and the finite bound with raw pinned values. [WholeRow/ParityTemplate.lean](../../lean-machine/LeanMachine/WholeRow/ParityTemplate.lean) discharges whole-row enclosures, derives internal-block containment in the helper-row/shared-column rectangle, and proves exact incidence and finite bounded-degree bounds, allowing rectangular arrays, lanes and conditional recovery given pins. [DisjointSumsDeletion.lean](../../lean-machine/LeanMachine/DisjointSumsDeletion.lean) constructs and prices block deletion. [WholeRow/ParityTrimming.lean](../../lean-machine/LeanMachine/WholeRow/ParityTrimming.lean) proves paid heavy-row trimming, the forward-width-only bound and a uniform vanishing excess above the active-template baseline, with an explicit alphabet/lane-independent dimension threshold. [InvolutionOmissions.lean](../../lean-machine/LeanMachine/InvolutionOmissions.lean) selects the original active bank, identifies its exact allowed shifts and counts its kernel. [WholeRow/ParityReserved.lean](../../lean-machine/LeanMachine/WholeRow/ParityReserved.lean) reserves original fixed cells; [WholeRow/Pairing.lean](../../lean-machine/LeanMachine/WholeRow/Pairing.lean) cancels their contribution after trimming and proves rate at most ½+b/N+1/n once d≥n(w+2w³n), uniformly in alphabet and lanes. [Rate proof and scope](pairing-coset-bound.md). | Main pairing and active-parity finite/uniform endpoints are complete. The inactive-fixed-cell variant is also Lean: for a specified inactive fixed set F it adds card(F∖Inc(ρ))/(2N) to the rate, at the same threshold. The underlying subgroup invariance remains a hypothesis. No invariance premise is extracted from native machine correctness. |
| Paid symmetric/reflexive normalization | [SymmetricHelpers.lean](../../lean-machine/LeanMachine/SymmetricHelpers.lean) proves the degree budget and exact fixed-cell union size. [NormalizedCodeTransfer.lean](../NormalizedCodeTransfer.lean) proves the finite fibre bound, sharpened to attained records. [NormalizedRateTransfer.lean](../NormalizedRateTransfer.lean) proves same-rate equivalence for common two-sided bounds, for both all finite alphabets and canonical bits, and the native crux/exclusion consumers. | No missing step in this reduction. A common capacity deficit remains an open hypothesis; no symmetry of the code or decoder is assumed. The alternative direct pair-message invoice and exact two-sided examples remain written. |
| Assigned-rule theorem | [ClosureBarriers.lean](../ClosureBarriers.lean): `assigned_rule_card_le`, `card_le_seed_add`, `transported_invoice_ge`. Arbitrary finite helper graphs, loops included, arbitrary coordinate transports and positive copy count. | The separate multiple-helper-option extension remains a written proof. |
| Same-table replay checker (routine tooling) | [SameTable.lean](../SameTable.lean): decidable `Valid` checks only finite supplied data. `replay` and `computesWithin` give the one-input execution consequence. `transposeTableaux_iff` and `obliviousLinTime_iff` give the exact per-size interfaces, including zero dimensions/widths. `uniformTableaux_iff` identifies the raw-data family with the existing `ObliviousLinearTimeTransposable`, preserving one fixed table/time constant, terminal moves and all-time obliviousness. [Readable fields and quantifiers](whole-row-ingredient-ledger.md#5-converse-formalization-source-audit-and-effort-estimate). | A semantic restatement by ordinary induction, not a new capacity result. No adaptive-family wrapper, arbitrary-network-code realization or machine construction is asserted. [Sparse-record audit](whole-row-ingredient-ledger.md#6-what-bounded-causal-views-can-reconstruct): nonuniform packet gates do not supply fixed-table control. |
| Local record-view covering invoice | [LocalRecordViews.lean](../LocalRecordViews.lean): `isIndexCode_patchEncoder` fixes exterior coordinates before restriction; `patch_card_le` reuses Paper 5's fibre bound for arbitrary finite source and record alphabets. Binary wrappers prove weighted patch deficits, fractional-cover half invoices and the equal-width endpoint sCm≥L/2−Σe. Unequal record widths, empty patches and real capacity/errors are allowed. [Statement and hypotheses](local-record-view-covers.md#2-the-exact-covering-invoice). | Conditional-entropy and attained-range displays remain written. Native record views, separation/local capacities and record-reuse bounds remain additional premises; no native exclusion is newly formalized. |
| No-empty-rectangle barrier | [RectangleBarrier.lean](../RectangleBarrier.lean): `rectangle_barrier` proves `d²+(r−1)²≤\|S\|+(m+1)d(r−1)` for explicit finite recovery witnesses and arbitrary bijective layouts. The copies may have different helper relations, each with no empty r×r rectangle. `rectangleBarrierTarget` proves the original common-relation statement; `rectangle_invoice_ge` proves its real invoice form. Equal recovery ranks and m growing with d are allowed. | The probabilistic construction of fixed-window relations with this rectangle property remains written. The finite barrier and invoice have no unproved step. |
| Soft order bound | [EntropyConsolidation.lean](../EntropyConsolidation.lean): `acyclic_conditional_le`, `soft_order`, `soft_order_of_acyclic`, `soft_order_entropy`. The polymatroid statement assumes no exact recovery or singleton caps; loops outside the acyclic set are allowed. | No missing step in these declarations. The conditional-entropy interpretation uses the same polymatroid inequality. |
| Entropy-to-exact-subcode selection | [SubcodeSelection.lean](../SubcodeSelection.lean): `exists_observed_dependency_subset` handles arbitrary finite functional dependencies; `subcodeSelectionTarget` derives the original storage-code statement. [ConditionalSubcode.lean](../ConditionalSubcode.lean): `conditional_subcode_selection` strengthens the record bound to H(X∣Z), and `conditionalSubcodeSelectionTarget` derives the original target. Both select nonempty subcodes in the positive support, allowing arbitrary correlated records. | No missing step in these statements. They concern actual finite laws, not arbitrary polymatroids; they do not promise to preserve linearity or decoder symmetry. |
| Fano paid inequalities and code bound | [FanoCertificate.lean](../FanoCertificate.lean): `paid_fano` proves `3h(V)≤2Σh({v})+Σ[h(N_v∪{v})−h(N_v)]` on the actual 28-cell residual graph. [FanoFull.lean](../FanoFull.lean): `paid_full` retains the joint incident-cell price and conditional singleton prices; `full_upper_of_cap` proves `3h(V)≤119a` under singleton caps a. `wholeRow_card_cube` proves `\|C\|³≤\|A\|¹¹⁹` for every finite nonempty alphabet and arbitrary nonlinear code on the full host. | The separate joint-column-error coefficient 41/84 remains written/exactly checked outside Lean. |
| Fano Shannon and code attainment | [FanoAttainment.lean](../FanoAttainment.lean) proves exact unit-cap polymatroid optima 56/3 and 119/3; `residual_no_decomp` rules out a literal Paper 7 half-rate decomposition. [FanoLaneCode](../../Tape-Transposition-and-the-Matrix-Coding-Conjecture/lean/MatrixCoding/FanoLaneCode.lean) constructs the three-lane code over every finite abelian group A, proves whole-row recovery and exactly \|A\|^119 words, permits arbitrary triangle sums, and proves optimality over A³. The ZMod q specialization supplies every positive integer base size. | None for Theorem E(a). This is actual code attainment; no grid or sparse-lift attainment is asserted. |
| Fano order and acyclic values | [FanoOrder.lean](../FanoOrder.lean): `exact_order_value`, `orderCost_eq_sum_lastHelperPosition` and `exact_last_helper_value` prove the exact minimum 41, including the standard last-helper-position formulation. | None for the full-host comparison: shared [AcyclicOrder.lean](../../lean-machine/LeanMachine/WholeRow/AcyclicOrder.lean) proves rectangular containment and exact cardinality; [WholeRowAcyclic.lean](../WholeRowAcyclic.lean) proves maximum acyclic size 8 and gap at least 4/3 against every acyclic invoice. |
| Sparse amplification at fixed window and growing girth (breach B3) | [MacroProjection.lean](../MacroProjection.lean) transfers any unit-cap base bound under helper containment and a positive fibre-size cap; the Fano cap endpoint includes zero and rectangular clones. [LiftOrder.lean](../../lean-machine/LeanMachine/WholeRow/LiftOrder.lean) constructs the threshold-induced base order and proves every-fine-order cost ≥ (n−r+1)²S under per-incidence r-rectangle mixing; contiguous clone groups give a separate n² upper comparison. [FanoLift.lean](../FanoLift.lean) combines the actual Fano value 41 and upper bound 119/3, proving gap ≥ 15523n²/30000 > (7n)²/100 under 99n≤100(n−r+1), 1≤r≤n. All feasible polymatroids and every induced acyclic-set invoice are covered. The explicit complete lift has containment, mixing at r=1, growing window 3n and gap at least (4/3)n². | Random-permutation mixing existence, degree-3600 existence and logarithmic girth remain written. The optional paid macro-error extension and small-separator argument also remain written. [Coverage and stopping point](finite-shannon-gap-amplification.md#7-lean-coverage-and-remaining-effort): stages 1–2 complete; stop before permutation counting. No fine-host attainment is asserted. |
| Grid paid upper bounds | [GridCertificate.lean](../GridCertificate.lean): `paid_grid`, `rateBound_grid`, `residual_le`, `loopless`, `mutual_triangle_free` on the actual 36-cell residual host. [GridFull.lean](../GridFull.lean): `paid_full`, `full_upper`, `storage_card_fifth` give the full 54-cell bound 204/5 and \|C\|⁵≤\|A\|²⁰⁴ for every finite alphabet. | The separate joint-column-error price 8/15, lower code with 21 residual symbols, 18×18 balancing and amplification remain written. The exact Shannon value and capacity remain open. |
| Grid order and acyclic values | [GridOrder.lean](../GridOrder.lean): `exact_order_value`, `exact_residual_order_value`, `exact_last_helper_value` give 41 full and 23 residual. `residual_upper_lt_order` and `full_upper_lt_order` compare the Shannon bounds with every row order. | None for the full-host comparison: [WholeRowAcyclic.lean](../WholeRowAcyclic.lean) proves maximum acyclic size 13 and gap at least 1/5 against every acyclic invoice. The rectangular generic theorem includes empty rows and empty helper sets. |

The subcode proofs reuse the existing finite entropy and Gibbs lemmas.
[DecoderSelection.lean](../DecoderSelection.lean) proves the finite product-weight
count, and [DecoderEntropy.lean](../DecoderEntropy.lean) supplies normalized
conditional response tables and their exact log-success identity. One additional
constraint selects a record fibre; no separate conditional-law proof is needed.

The proved declarations use only Lean's standard axioms. No open target is
introduced as an axiom or used to prove another result. Entropy in the Lean
library uses natural logarithms; the written base-q inequalities are the
same inequalities after division by log q, for q>1.

Both finite certificates reuse Paper 4's polymatroids and symmetry averaging,
the existing soft-recovery increment lemmas, and the common purchases/recovery
proofs in [ShannonCertificate.lean](../ShannonCertificate.lean). The Fano proof verifies the actual
point-line incidences, the finite automorphisms used, and all 33 semantic
certificate inequalities before adding their integer weights. No solver
output is trusted as a premise. The generated file permits 2,000,000
heartbeats for routine finite checking; this changes no logical axiom.
The companion files reuse contraction, entropy and image-rank lemmas. They
permit 1,000,000 heartbeats where used for finite checks. The order proof
checks the 128 point subsets and one attaining order, not all permutations.
The grid proof checks 18 semantic terms, its actual triangle-free residual relation,
and 512 point subsets for its order optimum. Its generated proof and adapters use
the same stated heartbeat budgets. The grid upper bound is not claimed sharp.

Reproduce the generated source with the standard-library checker (Python
3.10 or later), from the repository root:

```sh
python3 lean-backlog/tools/fano-shannon/generate_lean.py --check
python3 lean-backlog/tools/grid-shannon/generate_lean.py --check
```

Build from the existing pinned environment:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py \
  TwoSidedCodeTransfer NormalizedCodeTransfer NormalizedRateTransfer \
  ClosureBarriers RectangleBarrier EntropyConsolidation \
  DecoderSelection DecoderEntropy SubcodeSelection ConditionalSubcode \
  ShannonCertificate SubcubicReuse FanoCertificate FanoFull FanoOrder FanoAttainment \
  MacroProjection FanoLift GridCertificate GridFull GridOrder WholeRowAcyclic \
  SameTable LocalRecordViews \
  BlockIntervalWalk BlockCut BlockCodeLocal BlockCutPrice BlockRowGrouping \
  BlockEndRows BlockCodeTransfer BlockCodeInvoice WholeRowTCC WeakWholeRowTCC \
  FiniteWholeRowPayments Wall
```

## Conditional bridge closure audit

The audit targets the already-imported theorem
`Wall.Conjecture → ¬ Transpose.LinearTimeTransposable`. It does not create
`Transpose.answer`, assert the open hypothesis, or run the final checker on
an unconditional answer. The actual [frozen verifier](../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Verify.lean)
requires that unconditional type. Any future proof of the hypothesis and
its additional imports must be checked again.

At bridge revision `c078f49`, with Lean v4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`, the loaded closure has:

| Part | Modules |
|---|---:|
| Lean toolchain, trusted by the frozen verifier's path test | 2,357 |
| Mathlib umbrella and its Mathlib imports | 8,530 |
| Batteries, Aesop, Qq, Plausible, ProofWidgets, ImportGraph, LeanSearchClient | 378 |
| Repository sources, including the bridge | 291 |
| **Total** | **11,556** |

The repository part comprises Paper 1 (53 modules, through Paper 2's
read-only build adapter), Papers 2/4/5/8/9/11/14/15
(27/2/7/13/40/29/43/2), shared `lean-machine` (48), and the backlog (27).
Paper 15 contributes only `PaidInputs` and `Conditioning`. Package
requirements are not import dependencies: the Fano and grid certificates,
`ShannonCertificate`, `MacroProjection`, `WholeRowAcyclic`, and the finite
Clebsch/Paley modules are absent. Several older modules import the umbrella
`Mathlib`, so all 8,530 modules under that import are present. The diagnostic
prints every actual module name and resolved artifact path.

The 609,722 selected non-toolchain declarations contain no axiom
declarations. The bridge's transitive axiom list is exactly `propext`,
`Classical.choice`, `Quot.sound`. The mapped non-toolchain sources contain
no active `native_decide`, `decide +native`, or `axiom` tokens after removing
comments and strings; the 291 repository sources additionally pass the
placeholder/unsafe/kernel-bypass scan. The frozen statement and verifier
match the research project's SHA-256 values.

The verifier replays eligible declarations from **all** non-toolchain
imports, then applies its axiom whitelist only to the answer's transitive
dependencies. An unused imported axiom would not itself fail that final
filter. Lean's replay API skips unsafe and partial declarations; the audit
reports selected and eligible counts separately. Source scans and axiom
reports alone do not establish successful fresh replay.

**Replay cost/status:** the single-threaded cached-artifact attempt reached
the fresh-kernel phase (16.790 seconds after its internal inventory marker),
then hit the 600-second whole-process cap while that phase was active.
No completed replay or kernel rejection was established. This is a bounded
attempt on a shared host, not an isolated replay benchmark. No Mathlib
source rebuild was part of the diagnostic. An earlier combined attempt
also timed out; its optional exhaustive all-constants axiom scan has no
completed result and is not required by the frozen checker.

After preparing the pinned compiled dependencies and checking the backlog,
run from `High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean`:

```sh
lake env python3 ../../lean-backlog/tools/audit_wall_closure.py
lake env python3 ../../lean-backlog/tools/audit_wall_closure.py --replay --timeout 600
```

The [Lean diagnostic](../tools/audit_wall_closure.lean) mirrors the frozen
selection/replay and checks the conditional target's exact type; its
[launcher](../tools/audit_wall_closure.py) uses one Lean thread and a bounded
runtime, with live phase markers. Raw output contains local paths and
should be saved outside the public repository. This is verification
tooling, not a new mathematical result or an answer to the open problem.

## Scope corrections retained in the index

Transported closure invoices are **at least** the original acyclic bound;
they need not equal it. Together, the Lean acyclic-set identification in
[AcyclicOrder.lean](../../lean-machine/LeanMachine/WholeRow/AcyclicOrder.lean)
and `ClosureBarriers.transported_invoice_ge` justify “every order bound”
for induced acyclic invoices and the displayed-rule transported closure
invoices with unit coordinate prices and additive message bills.
The connected two-triangle-system example gives
`2N/3+1/2`, whereas the original acyclic exponent is `2N/3`. The interval
relay also need not achieve the optimal finite value. These are limits of
displayed-rule closure counting with the stated prices, not limits of full
Shannon inequalities or of additional algebraic dependencies.

For the withdrawn second-decoder proposal, transpose invariance is needed.
On an invariant linear code C with `R|C=transpose|C`, the conjugate
`transpose R transpose` is already another decoder. If `transpose R=I+E`,
then `rank E≤N−dim C` and the difference of the two decoders is the
commutator `transpose E−E transpose`, of rank at most twice that deficit.
This holds in every characteristic. Splitting C into positive and negative
transpose eigenspaces additionally requires characteristic not two; that
split is not needed to justify withdrawing the proposed extra condition.
