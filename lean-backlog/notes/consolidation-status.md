# Closure and entropy: proof status and remaining work

14 November 2026. This is a verification index, not a new capacity theorem.
The [conditional machine-exclusion table](conditional-machine-exclusions.md)
records exactly which additional native hypotheses would let the existing
code results exclude a machine class. The native common-deficit hypothesis
is still open.

| Item | Lean coverage | What remains |
|---|---|---|
| Sparse-recovery half rank and bounded-outdegree rank | None yet. [Written, independently reviewed proof](subcubic-half-rank.md): arbitrary fields, asymmetric subcubic supports, stronger two-helper and directed forms, and arbitrary finite-alphabet subsets of affine kernels. | Formalize the generic prefix-rank/support lemma, the last-row four-arc obstruction, the closed-set row order and the cardinality adapters. Mathlib row-span/finite-dimension APIs suffice; no zero-forcing or SCC library is needed. |
| Matching plus one helper | None yet. [Written nonlinear proof](subcubic-half-rank.md#4-a-nonlinear-subcase-a-matching-plus-one-helper), including partial matchings and fixed boundaries. | Finite Hall selection and functional-chain recovery; this ordinary seed certificate is separate from the general linear rank theorem. |
| Pairing and parity-template extensions | None yet. [Written, reviewed proof](pairing-coset-bound.md), including the omitted-orbit price and forward-width-only trimming. | Subgroup fibre counting and heavy-row recording. This is an invariance-class bound, not a capacity theorem for arbitrary codes. |
| Paid symmetric/reflexive normalization | [SymmetricHelpers.lean](../../lean-machine/LeanMachine/SymmetricHelpers.lean) proves the degree budget and exact fixed-cell union size. [NormalizedCodeTransfer.lean](../NormalizedCodeTransfer.lean) proves the finite fibre bound, sharpened to attained records. [NormalizedRateTransfer.lean](../NormalizedRateTransfer.lean) proves same-rate equivalence for common two-sided bounds, for both all finite alphabets and canonical bits, and the native crux/exclusion consumers. | No missing step in this reduction. A common capacity deficit remains an open hypothesis; no symmetry of the code or decoder is assumed. The alternative direct pair-message invoice and exact two-sided examples remain written. |
| Assigned-rule theorem | [ClosureBarriers.lean](../ClosureBarriers.lean): `assigned_rule_card_le`, `card_le_seed_add`, `transported_invoice_ge`. Arbitrary finite helper graphs, loops included, arbitrary coordinate transports and positive copy count. | The separate multiple-helper-option extension remains a written proof. |
| No-empty-rectangle barrier | [RectangleBarrier.lean](../RectangleBarrier.lean): `rectangle_barrier` proves `d²+(r−1)²≤\|S\|+(m+1)d(r−1)` for explicit finite recovery witnesses and arbitrary bijective layouts. The copies may have different helper relations, each with no empty r×r rectangle. `rectangleBarrierTarget` proves the original common-relation statement; `rectangle_invoice_ge` proves its real invoice form. Equal recovery ranks and m growing with d are allowed. | The probabilistic construction of fixed-window relations with this rectangle property remains written. The finite barrier and invoice have no unproved step. |
| Soft order bound | [EntropyConsolidation.lean](../EntropyConsolidation.lean): `acyclic_conditional_le`, `soft_order`, `soft_order_of_acyclic`, `soft_order_entropy`. The polymatroid statement assumes no exact recovery or singleton caps; loops outside the acyclic set are allowed. | No missing step in these declarations. The conditional-entropy interpretation uses the same polymatroid inequality. |
| Entropy-to-exact-subcode selection | [SubcodeSelection.lean](../SubcodeSelection.lean): `exists_observed_dependency_subset` handles arbitrary finite functional dependencies; `subcodeSelectionTarget` derives the original storage-code statement. [ConditionalSubcode.lean](../ConditionalSubcode.lean): `conditional_subcode_selection` strengthens the record bound to H(X∣Z), and `conditionalSubcodeSelectionTarget` derives the original target. Both select nonempty subcodes in the positive support, allowing arbitrary correlated records. | No missing step in these statements. They concern actual finite laws, not arbitrary polymatroids; they do not promise to preserve linearity or decoder symmetry. |
| Fano paid inequalities and code bound | [FanoCertificate.lean](../FanoCertificate.lean): `paid_fano` proves `3h(V)≤2Σh({v})+Σ[h(N_v∪{v})−h(N_v)]` on the actual 28-cell residual graph. [FanoFull.lean](../FanoFull.lean): `paid_full` retains the joint incident-cell price and conditional singleton prices; `full_upper_of_cap` proves `3h(V)≤119a` under singleton caps a. `wholeRow_card_cube` proves `\|C\|³≤\|A\|¹¹⁹` for every finite nonempty alphabet and arbitrary nonlinear code on the full host. | The separate joint-column-error coefficient 41/84 remains written/exactly checked outside Lean. |
| Fano Shannon attainment | [FanoAttainment.lean](../FanoAttainment.lean): `residual_shannon_exact` and `full_shannon_exact` prove the exact unit-cap polymatroid optima 56/3 and 119/3 by explicit feasible witnesses. | Realization by the three-lane code over every finite base alphabet remains a written proof. A feasible polymatroid alone does not assert an entropic realization. |
| Fano order value | [FanoOrder.lean](../FanoOrder.lean): `exact_order_value`, `orderCost_eq_sum_lastHelperPosition` and `exact_last_helper_value` prove the exact minimum 41, including the standard last-helper-position formulation. | The general whole-row theorem identifying this value with 49 minus the maximum induced acyclic-set size remains a separate written result of Paper 17. |
| Grid paid upper bounds | [GridCertificate.lean](../GridCertificate.lean): `paid_grid`, `rateBound_grid`, `residual_le`, `loopless`, `mutual_triangle_free` on the actual 36-cell residual host. [GridFull.lean](../GridFull.lean): `paid_full`, `full_upper`, `storage_card_fifth` give the full 54-cell bound 204/5 and \|C\|⁵≤\|A\|²⁰⁴ for every finite alphabet. | The separate joint-column-error price 8/15, lower code with 21 residual symbols, 18×18 balancing and amplification remain written. The exact Shannon value and capacity remain open. |
| Grid order values | [GridOrder.lean](../GridOrder.lean): `exact_order_value`, `exact_residual_order_value`, `exact_last_helper_value` give 41 full and 23 residual. `residual_upper_lt_order` and `full_upper_lt_order` compare the Shannon bounds with every row order. | The general theorem identifying the row-order optimum with ambient size minus the maximum induced acyclic-set size remains a separate written result. |

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
  ShannonCertificate FanoCertificate FanoFull FanoOrder FanoAttainment \
  GridCertificate GridFull GridOrder
```

## Scope corrections retained in the index

Transported closure invoices are **at least** the original acyclic bound;
they need not equal it. The connected two-triangle-system example gives
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
