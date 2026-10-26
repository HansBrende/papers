# Bounded Nesting and Depth Reduction for Matrix Transposition on Tapes

Hans Brende and Claude Opus 5.5 (Anthropic), October 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It builds on the fourth paper's library, which it requires by relative path,
  so the sibling directories of this repository must be in place.
- [`tools/`](tools/):
  - [`lean_index.py`](tools/lean_index.py) generates the index of Lean declarations and `lean/PaperAxioms.lean`
    from the paper's LaTeX sources;
  - [`clebsch_lift.py`](tools/clebsch_lift.py) performs an exact rank computation over F₂ that checks part (f) of
    the equivariant crux independently (plain Python 3).

## The question

Can a deterministic multitape Turing machine transpose a d×d matrix of ⌈log₂ d⌉-bit entries in time linear in
the input length? For oblivious machines the fourth paper of the series reduced a negative answer to two
statements: *depth reduction* of the time–space dependency graph by a cheap genie (at the level of head walks, the
trajectory cut problem TCP), and a coding bound on the remaining bounded-depth cones, the *crux*. This paper is
about the depth side and about how it meets the coding side.

## What is proved

Proved in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound` (the paper states each
result with its Lean declarations and file):

- **The owner lemma.** If ℓ nested hops above their cells of a walk with steps in {−1, 0, 1} have pairwise
  distinct owners, the cell of the innermost hop is entered at least (ℓ + 1)/2 times. (Hops below their cells
  follow by reflection, in the text.)
- **Cuts are labels.** Along a path on which a label with q values never increases, and strictly decreases at
  the marked steps, there are at most q − 1 marked steps. (Its consequence for walk DAGs is deduced in the text.)
- **Lemma W (the strip cut for one walk).** For integers w ≥ 2 and r ≥ 1, some line residue and offset give a cut
  of at most 4T/w + wT/r edges of the walk DAG of one walk, after which every path carries at most r − 1 hops.
- **The label arithmetic of the turn counter**, on top of the fourth paper's Lemma Zq. The rest of the turn-counter
  theorem (the bound on the label offset, the hypotheses of the arithmetic on the cover of the deep-nesting pair,
  and the counts of turns and hops, from the fourth paper's Lemma 5.4) is proved in the text.

Proved in the paper with complete written proofs, not formalized:

- **Theorem F (bounded nesting).** For k walks of length T, coupled arbitrarily, and any set of their long hops in
  which each head has at most ℓ distinct owners among its open hops of each side, some εT edges cut the DAG of
  these hops to depth 2^{O(k³ℓ³/ε)}, whatever the homes, drift and scales. Consequences: TCP for walks that enter
  every cell boundedly often; in every schedule the depth-robust part lives on fewer than kεT cells.
- **Theorem M.** One arbitrary walk together with walks of bounded owner-load whose families lie in boundedly many
  dyadic windows of bounded width is cut to a depth independent of the arbitrary walk and of T. TCP for k walks is, up to a
  factor 2 in k, depth reduction for DAGs with a spine and k non-crossing families of arcs; two families are
  planar.
- **The deep-nesting pair.** The turn counter cuts the pair at depth ⌈11·2^{m+1}/((m+1)ε)⌉ − 1 at every shift;
  every level class has exactly n_h/(2(m+1)) hops; for labels that change only at turns, fine classes are blind
  to the other head on average over shifts; when the other head carries a block label, coarse classes see its
  cancellations on average over shifts (Theorem V).
- **Consequences for transposers.** The crux alone excludes oblivious linear-time transposers whose work heads
  enter every cell boundedly often (Corollary F), and so does an affirmative answer to Question 9.1 of
  *Directed Recovery Structures in Tape Computations* (Corollary F′), which also covers adaptive machines whose
  traces have entropy at most ηL for a fixed η < 1/2 and whose likely traces enter every cell boundedly often
  (Corollary F″).
- **Linear machines.** For machines with a data path linear over a field, linear depth reduction together with a
  linear crux excludes oblivious linear-time transposers, and the linear crux can be stated exactly as rigidity of
  the transposition matrix relative to the schedule (Theorem D_lin).
- **The crux in special linear settings.** Extending the lift identity of *Covers and Local Generation in Linear
  Storage Codes* to asymmetric checks: lifting a binary linear code along a tower of double covers never raises
  its rate. Using mod-2 Lück approximation, there are towers that never become bipartite and have girth tending
  to infinity, along which the lifted Clebsch code has rate tending to zero; the vanishing of the Clebsch limit
  also follows from the Covers paper, and an exact rank computation over F₂ (`tools/clebsch_lift.py`) checks it
  independently. A scalar linear code on a triangle-free graph of maximum degree four has rate at most one half
  when the exceptional vertices of its matrix are few or far apart (Theorem SH).

## What is open

- TCP for two heads of unbounded owner-load, in particular whether the deep-nesting pairs are depth-robust, and
  for one arbitrary walk together with walks of owner-load one at unboundedly many separated scales.
- Depth reduction for three-stack DAGs with a spine.
- The all-code paired-distance question (Question 9.1 of *Directed Recovery Structures in Tape Computations*).
- The half-rate bound for triangle-free side information of degree four.
- The scratch question and the relative rigidity of transposition.
- See the open-problems section of the paper.

## Building and verifying

The Lean package imports the fourth paper's package and, through it, the second and first papers' packages and the
shared library [`lean-machine`](../lean-machine/), by relative paths. Clone the whole papers repository so that the
sibling directories stay in place. Then fetch the second paper's pinned external dependency as described in its
[README](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/).
Install [elan](https://github.com/leanprover/elan), then in `lean/`:

```bash
lake exe cache get
```

```bash
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

Reproduce the rank computation of the equivariant crux (from this directory):

```bash
python3 tools/clebsch_lift.py
```

To build the PDF, run `latexmk -pdf main.tex` in `paper/`.
