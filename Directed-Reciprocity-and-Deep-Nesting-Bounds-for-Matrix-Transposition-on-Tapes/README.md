# Directed Reciprocity and Deep-Nesting Bounds for Matrix Transposition on Tapes

Hans Brende and Gemini 4 Argon (Google DeepMind), October 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It builds on the Lean libraries of the seventh and eighth papers (and through them
  the fourth, fifth, second and first papers and [`lean-machine`](../lean-machine/)) by relative paths, so the sibling
  directories of this repository must be in place.
- [`tools/`](tools/):
  - [`lean_index.py`](tools/lean_index.py) generates the index of Lean declarations (`paper/sections/leanindex.tex`)
    and `lean/PaperAxioms.lean` from the paper's LaTeX sources;
  - [`reproduce_numerics.py`](tools/reproduce_numerics.py) independently checks the finite numerical examples of
    Remarks 4.3 and 5.7 (plain Python 3, standard library only).

## The question

Can a deterministic multitape Turing machine transpose a d×d matrix of max(1, ⌈log₂ d⌉)-bit entries in time linear in
the input bit-length? For oblivious machines, the fourth paper of the series reduced impossibility to two combinatorial problems: *depth
reduction* of multi-head walk dependency DAGs (TCP(k)), and *half-rate bounds* for storage codes on bounded-degree
transitive-tournament-free (TT-free) directed recovery relations. Subsequent papers established the all-code half-rate
bound on undirected subcubic triangle-free graphs (Paper 7), proved a degree-4 scalar linear half-rate bound under
heavy-vertex separation hypotheses (S1) and (S2) (Paper 8), and isolated the 2-head deep-nesting pair DNP(s₀, m) and
block-cancellation labels B(a, K) (Conjecture A″, Paper 8) at the frontier of TCP(2). This paper resolves the open
all-code directed target on Class S, removes hypothesis (S2) at degree 4, and proves and formalizes exact stroke,
straddle, super-Fibonacci and three-regime block-pair bounds on DNP(s₀, m).

## What is proved

Every new numbered theorem, proposition, lemma and corollary of the paper is proved in Lean 4, with no axioms beyond
`propext`, `Classical.choice` and `Quot.sound` (the paper states each result with its Lean declarations and file):

- **Positional characterization of nested elimination (Proposition PN).** The stateful recursive predicate
  `HalfRate.RelCharged` of Paper 7 is equivalent to a stateless positional condition on prefixes and supplying records;
  for disjoint records, shared outside parents force either equal supplying records or prior revelation of the earlier
  supplying record, and no digon in a certified piece can lie inside a single own record (`PositionalNest.lean`).
- **Stride-s cores, universal chordless digon cycle dichotomy, and generalized Petersen hierarchy (Propositions CS and
  GP, Corollary on X₁₅, Theorem DC).** On any chordless digon cycle C_L (L ≥ 4) in a TT-free relation with at most one
  outside active parent per cycle vertex, an m-record piece certificate exists for *some* m ≥ 1 if and only if C_L is
  not a stride-3 hub cycle (`DigonCycle.lean`, `StrideCycles.lean`). This resolves both parts of Section 9.2, item 6 of
  Paper 7 in Lean 4: the unique minimum nonempty core {0,…,5} of X₁₅ admits no piece certificate for any m ∈ ℕ
  (`ClassSExamples.lean`), and the Petersen graph GP(5, 2) admits no global elimination certificate for any m ∈ ℕ, while
  GP(7, 2) requires exactly m = 4 records and GP(9, 2) drops back to m = 3 (`PetersenHierarchy.lean`).
- **Theorem S* and Corollary B* (all-code half-rate and barrier bounds on Class S).** Every finite TT-free recovery
  relation of maximum in-degree 3 in which vertices of in-degree 3 reciprocate outgoing arcs (`IsClassS`) admits a
  certified piece decomposition (`HalfRate.Decomp`), so every valid polymatroid obeys 2h(V) ≤ Σ_v h({v}) and every
  storage code C ⊆ α^V over any alphabet satisfies |C|² ≤ |α|^|V| (`ClassS.lean`). This resolves the intermediate target
  named in Section 9.2, item 2 of Paper 7 (the all-code version of Paper 4's Theorem S on its whole class; Conjecture P,
  numbered Conjecture 9.1 there, remains open). The key step inside strongly connected components is *hub augmentation*,
  which adjoins an in-degree-2 hub to an obstructed stride-3 shortest digon g-cycle to form a (g+2)-record sequential
  nested piece; on the 21-vertex strongly connected triangle-free relation G₂₁ ∈ Class S (`ClassSExamples.lean`,
  Proposition G21), the low-in-degree, W-cycle and shortest-digon-cycle rules all stall simultaneously, whereas hub
  augmentation decomposes it.
- **Theorem SH* and Corollary M* (degree-4 scalar linear codes without heavy non-adjacency).** Over every field F, a
  unit-diagonal matrix M without recovery triangles satisfying (★4) has dim_F ker M ≤ ⌊|V|/2⌋ whenever its heavy set
  H_M has size at most 2 or satisfies (S1) alone—no vertex has two distinct heavy recovery neighbours (on a
  triangle-free graph G of maximum degree 4, no two heavy vertices share a common neighbour)—eliminating hypothesis (S2)
  of Paper 8 (`TheoremSHStar.lean`). Combining Theorem SH* with the Tutte–Berge formula replaces Paper 8's distance-3
  packing invariant ρ₃(G, H_M) by the common-neighbour-free packing invariant ρ_m(G, H_M) ≥ ρ₃(G, H_M), which admits
  arbitrary induced heavy matchings at pairwise distance ≥ 3.
- **Deep-nesting stroke law, m-free V-straddle bound, and super-Fibonacci unwrapping (Proposition SL, Theorems V* and
  LU).** On U(s₀, m, 1), offsets in [0, Π_κ) biject onto stopping-depth codes with uniform depth distribution, fair
  binary branches and parity independence, and an O(m) recursive evaluator `evalPhiRec` matches cumulative turn jumps
  over a period (`DNPStrokes.lean`). Straddling half-widths around a level-κ V obey an m-free mod-q pair inequality and
  sum to exact triangular weight (Π_κ / 2)² on centres of either parity (`DNPStraddle.lean`). On a single head, any run
  of s consecutive levels with blind apex and band-0,1,2 errors at most q/8 unwraps over Z into the super-Fibonacci step
  b₀(k) ≥ b₀(k+1) + b₀(k+2) + 4, forcing 32(F_s − 1) ≤ q and s ≤ 2⌊log₂ q⌋ + 2 (`DNPFibonacci.lean`).
- **One-sided block drift, Mersenne binary clocks, and three-regime witnesses for bounded-range block pairs
  (Proposition OC, Theorem A).** Periodic block labels B(a, K) have exact positive sum 2^a(a(K+1) + 1) across all 2^(a+1)
  branch choices, and pure binary clocks fail modulo every Mersenne number q = 2^B − 1 with straddle residue q − 1 whenever
  B | (m − κ + 2). Whenever m < s₀ and 4(⌊log₂(m+1)⌋ + 1 + max(a₁, a₂)) ≤ m + 1, two fixed odd shifts ξ₁, ξ₂ (a single
  odd shift in the symmetric case a₁ = a₂, K₁ = K₂) provide three-regime blind-error and coarse-straddle failure witnesses
  for (B(a₁, K₁), B(a₂, K₂)) across *every* K₁, K₂ ∈ Z and *every* modulus q ≥ 3, with zero logarithmic loss in q
  (`DNPConjectureApp.lean`; see Remark 5.6 for the remaining steps (a)–(d) to Conjecture A″).

Not formalized (illustrative finite checks only, never used in proofs):
- the finite numerical examples of Remark 4.3 (the bipartite degree-4 family G_{8k} separating ρ_m = 2k from ρ₃ = k)
  and Remark 5.7 (finite parameter evaluations for DNP(s₀, m)), reproduced independently by
  [`tools/reproduce_numerics.py`](tools/reproduce_numerics.py).

## What is open

- Conjecture P beyond Class S (TT-free relations of in-degree at most 3 with unreciprocated arcs out of in-degree-3
  vertices) and Conjecture K on chorded digon cycles.
- Whether every relation in Class S admits a piece decomposition using O(1) (for instance ≤ 3) records per piece.
- Degree-4 triangle-free codes when heavy vertices lie at distance 2 (sharing common neighbours), and nonlinear codes at
  degree 4.
- Closing the remaining steps from Theorem A to Conjecture A″—selecting one common odd shift for asymmetric block pairs,
  establishing fine-band half-blindness at that fixed shift, converting the three-regime witnesses into doubly θ₀-served
  level counts, and extending to block lengths a ≍ (1/2) log₂ q and general low-cost labels on the r-fold cover—and
  deciding TCP(2) on the walk DAGs of DNP(s₀, m).
- Deciding (T), and extending complete source-cover and return-profile barriers beyond restricted return geometries on
  adaptive machines. See Section 7 of the paper.

## Building and verifying

The Lean package imports the seventh and eighth papers' packages (`../Nested-Elimination-and-Half-Rate-Bounds-for-Storage-Codes/lean`
and `../Bounded-Nesting-and-Depth-Reduction-for-Matrix-Transposition-on-Tapes/lean`), and through them the earlier
packages of the series and [`lean-machine`](../lean-machine/), by relative paths. Clone the whole papers repository so
that sibling directories stay in place, and on a fresh clone fetch the second paper's pinned external dependency as
described in its [README](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/).

Install [elan](https://github.com/leanprover/elan), then in `lean/`:

```bash
lake exe cache get
lake build
```

Check the axioms of every declaration cited in the paper (generated from the paper's LaTeX sources):

```bash
lake env lean PaperAxioms.lean
```

Regenerate the index of Lean declarations and `PaperAxioms.lean` after editing the paper (from this directory):

```bash
python3 tools/lean_index.py
```

Reproduce the standalone numerical remarks (from this directory):

```bash
python3 tools/reproduce_numerics.py
```

To build the PDF, run `latexmk -pdf main.tex` in `paper/`.
