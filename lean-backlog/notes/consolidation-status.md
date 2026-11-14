# Closure and entropy: proof status and remaining work

14 November 2026. This is a verification index, not a new capacity theorem.
The [conditional machine-exclusion table](conditional-machine-exclusions.md)
records exactly which additional native hypotheses would let the existing
code results exclude a machine class. The native common-deficit hypothesis
is still open.

| Item | Lean coverage | What remains |
|---|---|---|
| Assigned-rule theorem | [ClosureBarriers.lean](../ClosureBarriers.lean): `assigned_rule_card_le`, `card_le_seed_add`, `transported_invoice_ge`. Arbitrary finite helper graphs, loops included, arbitrary coordinate transports and positive copy count. | The separate multiple-helper-option extension remains a written proof. |
| No-empty-rectangle barrier | `RectangleBarrierTarget` in the same file is an exact, typechecked **proposition target**. It includes arbitrary bijective layouts and the square correction term. | Its proof is written only. The proposition definition asserts no theorem. |
| Soft order bound | [EntropyConsolidation.lean](../EntropyConsolidation.lean): `acyclic_conditional_le`, `soft_order`, `soft_order_of_acyclic`, `soft_order_entropy`. The polymatroid statement assumes no exact recovery or singleton caps; loops outside the acyclic set are allowed. | No missing step in these declarations. The conditional-entropy interpretation uses the same polymatroid inequality. |
| Entropy-to-exact-subcode selection | `SubcodeSelectionTarget` and `ConditionalSubcodeSelectionTarget` in the same file typecheck with actual finite probability laws, positive-support containment, nonempty subcodes and arbitrary correlated records. | Both are **unproved proposition targets**. They are not statements about arbitrary polymatroids and do not preserve linearity or decoder symmetry. |
| Fano inequality | [FanoCertificate.lean](../FanoCertificate.lean): `paid_fano` proves `3h(V)≤2Σh({v})+Σ[h(N_v∪{v})−h(N_v)]` for every polymatroid on the actual 28-cell residual graph. `rateBound_fano` and `residual_le` give the weighted two-thirds bound and the unit-cap upper bound 56/3. | The matching triangle construction, full 49-cell contraction adapter, order value 41, and separate joint-column-error coefficient 41/84 remain written/exactly checked outside Lean. |

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

Reproduce the generated source with the standard-library checker (Python
3.10 or later), from the repository root:

```sh
python3 lean-backlog/tools/fano-shannon/generate_lean.py --check
```

Build from the existing pinned environment:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py \
  ClosureBarriers EntropyConsolidation FanoCertificate
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
