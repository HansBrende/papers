# Macroscopic Information Transfer in Adaptive Tape Transposition

Hans Brende and GPT-6 Astra (OpenAI) · November 2026 · **Working draft**

[Paper PDF](paper/main.pdf) · [LaTeX](paper/) (CC BY 4.0) · [Lean](lean/)
(Apache 2.0) · [Publishing plan](PUBLICATION_PLAN.md)

## The question

What must happen in the original execution of an adaptive linear-time tape
transposer, without assuming that its fine trace is shared by many inputs?
We use dimension `d`, arbitrary positive entry width `b`, and bit length `d²b`;
canonical-width conclusions are identified separately.

## What is proved

The manuscript gives complete written proofs of direct adaptive replay, two
original heads with many macroscopic returns, original raw-input/output cuts,
selected-output off-carrier cuts, coherent-cluster extensions, dynamic-carrier
simulation and simultaneous large stores. It includes catalogue and strict
prior-output-prefix refinements, persistent marginal information, future-readable
and remote-return versions, and a same-tape-count redundant-archive construction
that prevents interpreting these marginals as independent useful information.

The local-getter appendix allows continuous raw-window ports, paid observer
state, one shared label and the strictly prior correct-output prefix. Shared
checkpoints handle arbitrary deterministic scans, including noninvertible
ones; an explicit paid loader supplies fixed scan archives. Separate appendices
prove changing-carrier simulation relative to raw/scan references and a
historical-cache extension forcing long secondary modification episodes.
The whole-run feedback appendix gives a dated-version feedback/deficit
tradeoff through actual halt, with a self-contained block-recovery proof and
paid spool correspondence. Cheap copying can already make that statistic large.

The transfer appendix retains two further results not subsumed by selected-slab
replay: original crossing expansion from every large output set, and capacity
certificates on original entry relations. Those asymptotic conclusions use
canonical widths. Its finite radius-3s eroded-input invoice holds at every
positive width, by the exact native frozen-trace injection. Each success-tail
statement is an ambient exceptional-input
count; it is not a conditional probability bound inside an arbitrary tiny success set.

The formalized endpoints now include actual adaptive replay and its input
injection, uniform original return, input-cut and off-carrier expansion,
the coherent-cluster extension, local-getter tails and the paid-loader application, and the complete
producer/consumer block-information lemma. The last
of these starts from one whole consumer execution and derives every window entry
state, output slice and read count.

| Proof family | Checked content |
|---|---|
| Native replay and returns | Actual old-position writes, latest-parent recovery, varying geometry, exact finite bills, and uniform all-width return tails |
| Original cuts | Literal original separators, cut-free ancestors, fragment and snapshot replay, exact menus and simultaneous input/off-carrier expansion tails |
| Coherent clusters | Actual multi-core replay, finite rounded chart metadata, original return/cut counts and simultaneous all-width tails |
| Local getters | Actual observer and strict-prefix reconstruction, multiport geometry, exact metadata, finite error bounds and uniform tails |
| Block programs | Product transcript fibres, one common shifted partition, conditional entropy, actual global consumer windows and the product constant 72 |
| Persistence | Whole-word catalogues, original-law selection, common live intervals, conditional and remote-word information and uniform rates, from explicit native thin-source count bounds |
| Carrier consequences | Exact sparse-hash, state and label budgets, storage/reference/cache tails from explicit native simulation contracts, and actual persistence/episode duration and span |
| Scan preparation | Exact native `2P+4` loader and consumer continuation; actual checkpoint getters, zero whole-run discrepancies and the resulting success bound |
| Simulator transport | Actual clock, head shadows and FIFO bounds; guarded path, raw-cone and eroded-input transport; original entry-capacity and crossing-expansion certificates with uniform success bounds |
| Supporting geometry | Order-conflict charts, protected cores, historical changed-cell supports, shared scan checkpoints, joint invoices and frozen native cut recovery |

The formal status beside each theorem is authoritative. A partial status names
both the checked component and its missing bridge. Standard Lean axioms only
are permitted: `propext`, `Classical.choice` and `Quot.sound`. The English outlines
of formalized results are reading aids; their Lean statements and proofs are
authoritative.

## Formalization todos

The remaining substantial native constructions may require weeks of work:

- Implement the dynamic sparse-carrier transition table, physical handoff
  invariant, partial sparse decoder and exact state count; extend it to the
  catalogue, raw-relative and historical-cache protocols.
- Implement the last-visit eraser and redundant-archive wrapper, with their
  exact output, state and time guarantees.
- Implement the native block monitor and paid output spool through actual halt,
  preserving the dated-version statistic and proving the full state/event bill.

Consequences of those constructions retain their explicit dependencies. The
checked persistence consequence starts from the native theorem's literal
thin-source count, retaining its constants. Lean derives the uniform law,
half-mass escape event and all subsequent estimates; it does not assert that
the missing native catalogue compiler is formalized.

Ordinary proof assembly is tracked separately. The return, input-cut,
localized off-carrier cut, getter, enlarged-rule, scan-loader application,
block-program, coherent-cluster and conditional persistence assemblies are complete.
The carrier/reference/cache state-budget consequences and short storage/episode
consequences are also checked, as are the actual simulator clock, head shadows,
FIFO bounds, guarded path projection, raw-cone and eroded-input transport,
original entry-capacity certificates and their uniform success bound.
Original-execution crossing expansion is also complete, including actual
crossing-target correspondence, exact finite guard bills and uniform constants.
All ordinary proof assemblies in this sprint are complete.
The transport work reuses an existing native simulator; it is not the same
missing construction as the carrier compiler.
The feedback tail's exact counting and finite weighted-date consequences are
also checked, conditional on the explicit native monitor bounds.
No missing proof is supplied as an extra axiom.

The [current formalization checkpoint](verification/formalization-checkpoint.md)
records the 35 fully formalized, six partial and seven written-only numbered
results, the remaining native constructions, and the latest validation.
The subsequent [cleanup and scope review](verification/cleanup-review-2026-11-10.md)
records proof reuse, the one-tape getter scope and the revised frontier roadmap.
The [draft integration record](verification/integration.md) preserves the earlier
independent reviews and validation checkpoint. The
[appendix integration record](verification/appendix-integration.md) records the
earlier expanded-package checkpoint and its validation. The earlier reviews do not claim
to have reviewed these subsequent additions. All checks preserve the
formalization boundaries above.

The [publishing plan](PUBLICATION_PLAN.md#remaining-result-integration-todos)
records all four substantive result packages and three compact supporting
additions as integrated into the manuscript. This completed content queue is
separate from formalizing the remaining written native proofs.

## What is open

Unrestricted linear-time transposition remains open. The necessary conditions
supply neither a cheap separator nor an output-sensitive information deficit for
all coupled work tapes. A redundant stored copy can meet a large marginal-information
requirement without paying for useful output recovery.

## Building and verifying

Clone the entire repository: this package requires sibling libraries through
relative paths. Lean and Mathlib remain pinned to version 4.34.1.

From this directory:

```sh
python3 tools/lean_index.py
cd lean
lake exe cache get
lake build
lake env lean PaperAxioms.lean
cd ../paper
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The generator audits both new formal-status declarations and the imported geometry
explicitly named in the text. Local `.lake/` caches are untracked. A successful
build verifies the listed Lean results, not the written-only native bridges.
The paper-local generator uses the shared `../tools/lean_paper_index.py`.
