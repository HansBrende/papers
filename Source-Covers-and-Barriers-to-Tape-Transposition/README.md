# Source Covers and Barriers to Tape Transposition

**Hans Brende and GPT-6 Astra (OpenAI)** — October 2026

**Draft with partial Lean formalization and complete written proofs for the remaining results.**

- [PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under [CC BY 4.0](paper/LICENSE).
- [Lean library](lean/), licensed under [Apache 2.0](lean/LICENSE).
- [Formalization plan](FORMALIZATION.md) and [generated statement index](FORMALIZATION-INDEX.md).

## The question

Does one deterministic multitape Turing machine transpose every square
matrix with dimension `d` and entry width `b(d) = max(1, ceil(log₂ d))` in
time `O(L)`, where `L = d² b(d)`? This is question (T) in the series.

## What is proved

Every numbered result has a precise statement and an explicit proof status.
**Lemma 2.3, family accounting, is Lean-verified**, using Paper 8's actual
hops, first-maximum owners and complete families. The hop count satisfies
`h_G <= min(o_G - p_G, U_G - o_G)`. Exact overlap counts control total hop
mass and variation. At a time boundary, the lower-endpoint bill is at most
one plus the actual crossing-hop counts of the active families; `1 + N a`
follows from uniform overlap and size bounds. The original Q2 conclusions
are direct specializations. The formalization also covers Definition 2.1
and its finite-time indexing conventions.

**Lemma 2.5, shadow and successful-word variation, is Lean-verified**, along
with the clipped shadows and finite-word orbits in Definition 2.4. The same
factor-three bound applies to every metric-valued path, independently of
the successful word's length or the number of disjointly packed families.
A stronger estimate keeps each threshold's actual crossing count. Success
means every concrete action is nonidentity; its domain is an interval.
Every actual hop with an unpaid lower endpoint is represented exactly.
The shared library proves the crossing argument once for arbitrary monotone
interval patches. A verified finite example attains three in that general
class. These results supply the variation component of the exact source bank.

**Lemma 2.6, the Q2 overlap forest and protected phases, is Lean-verified.**
Only original nonleaves need to be deleted. Leaves and components of one
or two vertices can survive without increasing the `M+1` bound on simple
paths or the `2M+3` bound on complete shadow orbits. Protected leaves
forbid no residues; the exact denominator is `M-F`, where `F` counts the
distinct residues used by protected nonleaves. Actual lower supports bound
the total payment before relaxing to unprotected-nonleaf hop mass.
The full orbit is identified with a finite set, including inactive actions
and intermediate stopping points. This supplies the core-orbit component
of the exact source bank with a potentially smaller bill. Its three shared
modules separate interval geometry, phase counting and finite action orbits.

**Theorem 2.7 (Theorem S), the exact source bank, is Lean-verified.**
One geometry-fixed list represents the complete retained-core and exceptional
orbit at every time, with the original slot, variation and core-orbit-cover
bounds. The variation estimate holds for every pseudometric-valued path and
every finite horizon. Disjoint component packing reuses the factor-three
patch bound; a four-map leaf sandwich and an ordered-exception recurrence
assemble the bank. Across every originally selected unpaid actual edge,
the lower endpoint's value set is contained in the upper endpoint's set;
every lower of a deleted core family is paid.
The root read and the `C_q (T-1)` raw variation bound are included.
Residual dependencies and full functional recovery are the next task.

**Lemma 3.2, fractional interval covers, is Lean-verified:** a finite target
in any linear order covered by order-convex sets has a subcover and an
equally large set of witness points, with at most one witness in each
original set. Thus a fractional cover rounds to a subcover of cardinality
at most its total weight. The target may be empty, and the intervals need
not be closed or bounded. This is the rounding step used by the later
raw-source gap bound. The shared library proves the result once; this
paper re-exports it without copying proofs.

**Lemma 8.3, the attached short-distance count, is Lean-verified:**
`S_ell <= min(d²b, (2 n - 1) b (2 k + 3)^(ell - 1))` for valid diagrams,
every block length `0 <= r <= d b`, and every natural radius parameter `ell` (both subtractions are
truncated at zero). Zero radius or block length gives an empty short-bit set.
The entry width remains arbitrary. A stronger geometry-dependent form
retains the actual attached-row and graph-ball counts. Its underlying local
counting inequality needs neither diagram validity nor a block-length bound.

The new occupancy argument replaces the first paper's `2b` bound per row
and output block by `b`, reusing its output-interval theorem. The remaining
proof imports its ball and row counts and applies Mathlib's finite-union
bound. The initial block touches at most one row, saving one attachment
over the two-per-block estimate.

All cited declarations use only `propext`, `Classical.choice` and
`Quot.sound`. The other **26 numbered results remain unformalized**,
including the raw-source gap and causal-group results that use these
lemmas. Their complete written proofs give the main chain:

1. The exact selected-family bank combines with paid residual recovery to
   retain actual state and work-tape dependencies, with explicit costs.
2. A finite correctness-deficit theorem uses fractional source covers and
   anchored approximation while preserving that complete recovery bank.
3. Under the fixed runtime, capacity and full-span class bounds, uniform
   impossibility follows for a two-class return core plus one arbitrary
   exceptional family, with sufficiently small outside families.
   For any fixed number of exceptions, near-full correctness imposes a
   quantitative lower bound on the limiting sorted hop tails.
4. Additional uniform exclusions follow from economical mean covers or raw
   support shared across all outputs and paid for once. Necessary cover,
   complete-observable movement and global-density bounds record what a
   surviving sequence would have to satisfy.

Three companion branches test the limits of those certificates: a native
quadratic pointwise cover example with serial exceptional spans; an
ordering-independent movement bound for a specified recovery interface;
and an almost-complete-helper requirement for causally autonomous groups
of `o(log d)` adjacent columns. The coded-caching code used to calibrate
the movement bound is credited to its original authors.

The manuscript develops the model and finite theorem first, derives their
uniform consequences next, and then presents these construction restrictions
and a roadmap. The generated index lists every numbered result and definition
as a reference for the later Lean phase.

## What is open

These are restricted full-geometry theorems, not a decision of (T). The
full-span partition and return-core hypotheses are not supplied for every
machine. Nor are the economical-cover or sharing conditions proved for
every admissible two-exception geometry. Selecting a common geometry in an
adaptive computation may lose entropy, which must be paid for separately.

The native counterexample concerns one root and phase and is itself excluded
by the finite-skeleton corollary. The movement bound retains its specified
helper and raw queries. The causal-group theorem requires local functional
separation, not just separated final outputs. No native strict separation
from the union of all prior certificates is claimed.

## Building and checking

From this directory:

```sh
python3 tools/statement_index.py
python3 tools/statement_index.py --check
```

From `paper/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

From `lean/` (the cache command is needed only for missing dependencies):

```sh
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

The index generator checks labels, proof-status markers and following proof
or outline environments, and generates the axiom commands from the formal
citations. It does not execute those commands or check the mathematics.
Inspect the rendered PDF
and resolve reference/citation warnings. Follow the repository's
[public-path checks](../CONTRIBUTING.md#portable-files) before publishing.

The Lean package uses the existing v4.34.1 pins and the second paper's build
adapter, which reads the first paper's canonical sources without copying
them, Paper 8's `boundedNesting` package for actual families, and the shared
`lean-machine` package for interval covers, incidence sums, monotone
patches, interval forests, protected phases, finite orbits and packed source
banks. Building
requires the whole repository with sibling folders in place.
The remaining plan is recorded in [FORMALIZATION.md](FORMALIZATION.md).
