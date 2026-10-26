# Nested Elimination and Half-Rate Bounds for Storage Codes

Hans Brende and Claude Opus 5.5 (Anthropic), October 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It builds on the libraries of the fourth paper, of its circular memo and of
  *Directed Recovery Structures in Tape Computations*, which it requires by relative path, so the sibling
  directories of this repository must be in place.
- [`tools/`](tools/):
  - [`lean_index.py`](tools/lean_index.py) generates the index of Lean declarations and `lean/PaperAxioms.lean`
    from the paper's LaTeX sources;
  - [`verify_remarks.py`](tools/verify_remarks.py) checks the computational remarks exactly (plain Python 3).

## The question

A storage code for a recovery relation N on a finite set V is a set of words in which every symbol is
determined by the symbols at its side information N(v). How large can such a code be? The series asks it for the
bounded-degree relations that arise from tape computations: the impossibility of linear-time oblivious
transposition on multitape Turing machines has been reduced to depth reduction together with a storage-code
bound of rate one half on such relations. This paper proves that half-rate bound, for all codes over all
alphabets, on large classes of relations, and shows where its method stops.

## What is proved

Apart from three results of the fourth paper that the paper cites (Theorem 2.2 and Lemmas 2.3 and 2.4), which are
Lean-verified there, every numbered theorem, proposition, lemma, corollary and example of the paper is proved in
Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The paper states each result with its
Lean declarations and file.

- **The engine.** Nested elimination (Lemma E: the inequality form of the circular memo's exact partition
  identity, extended by nested outside charges) and the decomposition theorem (Theorem D): a relation whose
  vertex set has an ordered decomposition into certified pieces satisfies 2h(V) ≤ Σ_v h(v) for every valid
  polymatroid, so every storage code has |C|² ≤ |α|^|V|. Certificates transfer to relations with fewer arcs,
  pull back along homomorphisms, and combine across ordered blocks whose parents lie in earlier blocks;
  Lemma B_dir builds pieces from relative 2-dicolourings.
- **Classes.** The half-rate bound holds for
  - relations that are 2-dicolourable, and graphs of circular chromatic number below 3;
  - triangle-free graphs of maximum degree 3 (Theorem N3);
  - loopless relations without transitive triangles whose underlying graph has maximum degree 3
    (Theorem U3);
  - loopless relations without transitive triangles whose vertices with at least three in-neighbours induce
    an acyclic sub-relation, with no degree bound (Theorem T), and, for loopless relations, the version in
    which only in-neighbours inside a vertex's strongly connected component count (Corollary T_int, proved
    from a block form by ordering the vertices by their numbers of ancestors);
  - loopless relations partitioned into blocks with private outside parents, each block chordless and
    subcubic without transitive triangles, a chorded digon path without transitive triangles (Lemma S), or
    carrying an elimination certificate (Theorem PC), in particular with the components of the digon graph
    as blocks (Corollary 5.11);
  - every Cayley relation Cay(G, {s, s⁻¹, t}) without transitive triangles, for every finite group G, when
    {s, s⁻¹, t} has three elements and does not contain 1 (Corollary CC, through the circulant sweeps of
    Proposition CC).
- **Paired distance and deletion.** A loopless relation has no transitive triangle exactly when b_E(3) = 0,
  that is, when every paired distance is at least five (Lemma 2.1); if N − Z satisfies the half-rate bound,
  then |C|² ≤ |α|^(|V|+|Z|) for every storage code on N (Corollary 6.9); and if every loopless relation without
  transitive triangles of in-degree at most 3 satisfies the half-rate bound, as Conjecture P would imply, then
  codes on relations of in-degree at most 3 have rate at most 1/2 + b_E(3)/(2|V|) (Proposition 8.1).
- **Consequences on triangle-free graphs of maximum degree 3.** The barrier bound
  2 log|C| ≤ (|V| + |S| − |I(S)|) log|α| for every vertex set S; every storage code has |C| ≤ |α|^ν*, where
  ν* is the fractional matching number, with equality for some code over every alphabet β × β; and every
  index code broadcasts at least (|V| − ν*) log|α|, with equality for some index code over β × β whenever β
  is a finite abelian group. Hence the guessing numbers satisfy gn(G, q) ≤ ν* for q ≥ 2,
  gn(G, r²) = gn(G) = ν* for r ≥ 2 and gn(G, q) → ν* as q → ∞ (Corollary 6.5), and the broadcast rate
  lim β_t/t of index coding is |V| − ν*, which on every graph is the infimum of the weights of fractional covers
  of the vertices by vertices and edges (Corollary 6.8). The fractional Tutte–Berge formula is proved along the
  way from Hall's theorem.
- **Limits.** Cay(Z₉, {1, −1, 3}) has no proper piece with private outside parents (Proposition 7.1) but has a
  decomposition with a proper first piece whose outside parents are shared (Example 7.2). The 15-vertex relation
  X₁₅ is loopless and has no transitive triangle, every vertex has at most three parents and at most three
  children, vertex 6 has two one-way parents, and its unique minimum nonempty core (a core is a set in which
  every vertex has at most one parent outside it) is the bidirected 6-cycle {0, …, 5}, whose outside parents have
  antipodal children (Remark 7.3). The twelve chorded cycles of Remark 7.4 are loopless chorded digon cycles
  without transitive triangles. The Petersen graph is triangle-free and has a decomposition, by Theorem N3
  (Remark 7.5). The global certificates printed for Cay(Z₉, {1, −1, 3}), for X₁₅ and for the displayed
  13-cycle, and certificates for the other eleven cycles, are checked, so each of these relations satisfies the
  half-rate bound.

Not formalized:
- the remaining claims of the numerical remarks on the limits of the method, checked exactly by
  `tools/verify_remarks.py`: that X₁₅ is strongly connected and not 2-dicolourable and that its minimum
  nonempty core is not a piece (Remark 7.3); that the twelve chorded cycles have no valid sweep (Remark 7.4);
  and that the Petersen graph has no global certificate (Remark 7.5);
- the cited rank formula for folded cubes (Remark 7.6), checked numerically for k = 2, 3 by
  `tools/verify_remarks.py`; its case k = 2, the Clebsch graph, is Lean-verified in the fourth paper
  (Corollary 6.11 there);
- the cited theorem of Atkins, Rombach and Skerman on the guessing numbers of odd cycles, after Corollary 6.5;
- the heuristic Remark 7.7.

## What is open

- Conjecture P: every loopless relation of in-degree at most 3 without transitive triangles has a decomposition,
  which would give the half-rate bound for all of them.
- The half-rate bound at degree four.
- The all-code question on paired-distance-separated relations of *Directed Recovery Structures in Tape
  Computations*.
- See the open-problems section of the paper.

## Building and verifying

The Lean package imports the fourth paper's package and its circular memo (both in
[`../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/`](../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/))
and the package of *Directed Recovery Structures in Tape Computations*
([`../Directed-Recovery-Structures-in-Tape-Computations/`](../Directed-Recovery-Structures-in-Tape-Computations/)),
through them the second paper's package, through it the first paper's, and the shared library
[`lean-machine`](../lean-machine/), by relative paths. Clone the whole papers repository so that the sibling
directories stay in place. Then fetch the second paper's pinned external dependency as described in its
[README](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/).

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

Check the computational remarks (from this directory):

```bash
python3 tools/verify_remarks.py
```
