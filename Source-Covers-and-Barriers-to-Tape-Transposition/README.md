# Source Covers and Barriers to Tape Transposition

**Hans Brende and GPT-6 Astra (OpenAI)** — October 2026

- [PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under [CC BY 4.0](paper/LICENSE).
- [Lean library](lean/), licensed under [Apache 2.0](lean/LICENSE).
- [Formalization record](FORMALIZATION.md) and [generated statement index](FORMALIZATION-INDEX.md).

The extension [memo on frozen gap areas](memo-gap-area/README.md), by Hans Brende and
Claude Opus 5.5 (Anthropic), takes the frozen point area of the complete raw-source bank
itself as the certificate. It excludes funnels and single-sweep terminal-landing
geometries, and shows that at moduli comparable to the protected rank this certificate
cannot exclude the two-exception inverse-square class. Its Lean proofs in `memo-gap-area/lean/` require this
paper's library unchanged.

## The question

Does one deterministic multitape Turing machine transpose every square
matrix with dimension `d` and entry width `b(d) = max(1, ceil(log₂ d))` in
time `O(L)`, where `L = d² b(d)`? This is question (T) in the series.

## What is proved

**All 32 numbered results and six numbered definitions are formalized in
Lean.** Every cited declaration uses only `propext`, `Classical.choice` and
`Quot.sound`. The Lean statements are authoritative; the accompanying
outlines explain those proofs. Independent reviews checked every numbered
statement against Lean and checked the manuscript's proof outlines,
citations and scope. No numbered statement required weakening.

The main argument fixes one complete computation geometry and a nonempty
correctness set. Its information deficit is `Δ = L − log₂ |C|`. It retains
all state and work-tape dependencies, including unpaid parents of revealed
output vertices, and allows arbitrary deterministic nonlinear updates.

- **Complete source banks and paid recovery (Section 2).** Actual return
  families, protected deletion phases and packed time maps yield a complete
  raw-source bank. Residual dependencies are retained and paid for. A single
  cyclic ordering of the raw coordinates then gives a correctness-deficit
  bound, charging a deterministic helper by its entropy.
- **Fractional covers and approximation (Section 3).** Fractional covers of
  complete core orbits improve the finite deficit bound. Anchored
  approximation retains the sharper quadratic erosion loss. The source
  credit and the full revelation cost concern the same computation.
- **Uniform exclusions (Section 4).** With fixed runtime, record-capacity
  and full-span-class bounds, a Q2 core plus one arbitrary complete
  exceptional family cannot have both sublinear correctness deficit and
  sublinear maximum outside-family size. With any fixed number `q` of
  exceptions, a near-full sequence requires limiting hop tails of order at
  least `R^(1−q)`. Common envelopes `H/i^p` with `p > q` are excluded.
  A separate finite-skeleton corollary excludes near-full correctness when
  only a fixed number of families are large and the largest remaining
  family has sublinear size.
- **Cover and sharing criteria (Sections 4–5).** Economical mean covers or
  raw support shared across outputs and paid for once give further uniform
  exclusions. Reciprocal-cover, complete-observable movement and global
  seed-density bounds state necessary conditions for a surviving sequence.
  These criteria keep finite cut parameters fixed before dimension grows.
- **A native limitation (Section 6).** Serial exceptional spans can require
  an exactly quadratic fractional cover at one root and phase. The example
  is already excluded by the finite-skeleton corollary; it does not refute
  an averaged cover criterion or supply a transposition algorithm.
- **Query movement (Section 7).** Covering the specified query types forces
  movement even after arbitrary reordering and coherent source matching.
  The calibration uses the [Maddah-Ali–Niesen coded-caching scheme](https://arxiv.org/abs/1209.5807v2)
  in [Yan et al.'s placement-delivery-array form](https://arxiv.org/abs/1510.05064v3).
  The additional result concerns its exact helper and raw-query interface.
- **Causal column groups (Section 8).** A locally autonomous computation
  within fixed consecutive groups yields an actual partial routing, with
  collector and return traffic charged. Under the stated native capacity
  bound and a fixed linear-runtime bound, groups of `o(log d)` columns
  force `Δ + H(Z) ≥ L − o(L)`, now with
  `Δ = L − H(X)`. Thus a helper must reveal almost all input information
  when the input law has near-full entropy. The finite estimate permits
  arbitrary positive entry widths and arbitrary correlated input laws.

The [formalization record](FORMALIZATION.md) preserves the detailed
strengthenings, dependency choices and completed stages. The
[statement index](FORMALIZATION-INDEX.md) links every numbered statement to
its formal declarations; it is not itself a verification certificate.

## What is open

These are restricted full-geometry theorems, not a decision of (T).
The full-span partition and return-core hypotheses are not supplied for
every machine. Nor are economical-cover or sharing conditions proved for
every admissible two-exception geometry with an inverse-square hop
envelope. Selecting a common geometry in an adaptive computation may
lose entropy, which must be paid for separately.

The movement result requires its specified helper and raw queries. Causal
group typing requires local functional separation and shared capacity
bounds, not merely separated final outputs; migrating groups remain
outside that restriction. No native strict separation from the union of
all prior certificates is claimed. Section 9 gives the research roadmap.

## Building and checking

Clone the whole repository with sibling folders in place. The Lean package
uses the existing Lean and Mathlib v4.34.1 pins, the second paper's adapter
for the first paper's canonical sources, Paper 8's `boundedNesting` package,
and the shared `lean-machine` library. Fetch the second paper's pinned
external dependency as described in its [README](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/README.md).

From this paper directory:

```sh
python3 tools/statement_index.py
python3 tools/statement_index.py --check
```

From `lean/` (the cache command is needed only for missing dependencies):

```sh
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

From `paper/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The index generator checks labels, proof-status markers and following
outlines, and generates axiom commands from the formal citations. It does
not execute those commands or check the mathematics. Inspect the rendered
PDF and resolve reference/citation warnings. Follow the repository's
[public-path checks](../CONTRIBUTING.md#portable-files) before publishing.
