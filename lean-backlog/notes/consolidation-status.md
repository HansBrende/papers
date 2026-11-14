# Closure and entropy: proof status and remaining work

14 November 2026. This is a verification index, not a new capacity theorem.
The [conditional machine-exclusion table](conditional-machine-exclusions.md)
records exactly which additional native hypotheses would let the existing
code results exclude a machine class. The native common-deficit hypothesis
is still open.

| Item | Lean coverage | What remains |
|---|---|---|
| Assigned-rule theorem | [ClosureBarriers.lean](../ClosureBarriers.lean): `assigned_rule_card_le`, `card_le_seed_add`, `transported_invoice_ge`. Arbitrary finite helper graphs, loops included, arbitrary coordinate transports and positive copy count. | The separate multiple-helper-option extension remains a written proof. |
| No-empty-rectangle barrier | [RectangleBarrier.lean](../RectangleBarrier.lean): `rectangle_barrier` proves `d²+(r−1)²≤|S|+(m+1)d(r−1)` for explicit finite recovery witnesses and arbitrary bijective layouts. The copies may have different helper relations, each with no empty r×r rectangle. `rectangleBarrierTarget` proves the original common-relation statement; `rectangle_invoice_ge` proves its real invoice form. Equal recovery ranks and m growing with d are allowed. | The probabilistic construction of fixed-window relations with this rectangle property remains written. The finite barrier and invoice have no unproved step. |
| Soft order bound | [EntropyConsolidation.lean](../EntropyConsolidation.lean): `acyclic_conditional_le`, `soft_order`, `soft_order_of_acyclic`, `soft_order_entropy`. The polymatroid statement assumes no exact recovery or singleton caps; loops outside the acyclic set are allowed. | No missing step in these declarations. The conditional-entropy interpretation uses the same polymatroid inequality. |
| Entropy-to-exact-subcode selection | [SubcodeSelection.lean](../SubcodeSelection.lean): `exists_observed_dependency_subset` handles arbitrary finite functional dependencies; `subcodeSelectionTarget` derives the original storage-code statement. [ConditionalSubcode.lean](../ConditionalSubcode.lean): `conditional_subcode_selection` strengthens the record bound to H(X∣Z), and `conditionalSubcodeSelectionTarget` derives the original target. Both select nonempty subcodes in the positive support, allowing arbitrary correlated records. | No missing step in these statements. They concern actual finite laws, not arbitrary polymatroids; they do not promise to preserve linearity or decoder symmetry. |
| Fano paid inequalities and code bound | [FanoCertificate.lean](../FanoCertificate.lean): `paid_fano` proves `3h(V)≤2Σh({v})+Σ[h(N_v∪{v})−h(N_v)]` on the actual 28-cell residual graph. [FanoFull.lean](../FanoFull.lean): `paid_full` retains the joint incident-cell price and conditional singleton prices; `full_upper_of_cap` proves `3h(V)≤119a` under singleton caps a. `wholeRow_card_cube` proves `|C|³≤|A|¹¹⁹` for every finite nonempty alphabet and arbitrary nonlinear code on the full host. | The separate joint-column-error coefficient 41/84 remains written/exactly checked outside Lean. |
| Fano Shannon attainment | [FanoAttainment.lean](../FanoAttainment.lean): `residual_shannon_exact` and `full_shannon_exact` prove the exact unit-cap polymatroid optima 56/3 and 119/3 by explicit feasible witnesses. | Realization by the three-lane code over every finite base alphabet remains a written proof. A feasible polymatroid alone does not assert an entropic realization. |
| Fano order value | [FanoOrder.lean](../FanoOrder.lean): `exact_order_value`, `orderCost_eq_sum_lastHelperPosition` and `exact_last_helper_value` prove the exact minimum 41, including the standard last-helper-position formulation. | The general whole-row theorem identifying this value with 49 minus the maximum induced acyclic-set size remains a separate written result of Paper 17. |

The subcode proofs reuse the existing finite entropy and Gibbs lemmas.
[DecoderSelection.lean](../DecoderSelection.lean) proves the finite product-weight
count, and [DecoderEntropy.lean](../DecoderEntropy.lean) supplies normalized
conditional response tables and their exact log-success identity. One additional
constraint selects a record fibre; no separate conditional-law proof is needed.

The proved declarations use only Lean's standard axioms. No open target is
introduced as an axiom or used to prove another result. Entropy in the Lean
library uses natural logarithms; the written base-q inequalities are the
same inequalities after division by log q, for q>1.

The Fano proof reuses Paper 4's polymatroids and symmetry averaging and
the existing soft-recovery increment lemmas. It verifies the actual
point-line incidences, the finite automorphisms used, and all 33 semantic
certificate inequalities before adding their integer weights. No solver
output is trusted as a premise. The generated file permits 2,000,000
heartbeats for routine finite checking; this changes no logical axiom.
The companion files reuse contraction, entropy and image-rank lemmas. They
permit 1,000,000 heartbeats where used for finite checks. The order proof
checks the 128 point subsets and one attaining order, not all permutations.

Reproduce the generated source with the standard-library checker (Python
3.10 or later), from the repository root:

```sh
python3 lean-backlog/tools/fano-shannon/generate_lean.py --check
```

Build from the existing pinned environment:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py \
  ClosureBarriers RectangleBarrier EntropyConsolidation \
  DecoderSelection DecoderEntropy SubcodeSelection ConditionalSubcode \
  FanoCertificate \
  FanoFull FanoOrder FanoAttainment
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
