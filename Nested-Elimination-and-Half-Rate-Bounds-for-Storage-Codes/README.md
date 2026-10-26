# Nested Elimination and Half-Rate Bounds for Storage Codes

Hans Brende and Claude Opus 5.5 (Anthropic), October 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It builds on the fourth paper's library and its circular memo, which it
  requires by relative path, so the sibling directories of this repository must be in place.
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

Everything in the following list is proved in Lean, with no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`. The paper states each result with its Lean declarations and file.

- **The engine.** Nested elimination (Lemma E: the inequality form of the circular memo's exact partition
  identity, extended by nested outside charges) and the decomposition theorem (Theorem D): a relation whose
  vertex set has an ordered decomposition into certified pieces satisfies 2h(V) ≤ Σ_v h(v) for every valid
  polymatroid, so every storage code has |C|² ≤ |α|^|V|. Certificates transfer to relations with fewer arcs,
  pull back along homomorphisms, and combine across ordered blocks whose parents lie in earlier blocks (the
  passage to strongly connected components is not formalized); Lemma B_dir builds pieces from relative
  2-dicolourings.
- **Classes.** The half-rate bound holds for
  - relations that are 2-dicolourable, and graphs of circular chromatic number below 3;
  - triangle-free graphs of maximum degree 3 (Theorem N3);
  - loopless relations without transitive triangles whose underlying graph has maximum degree 3
    (Theorem U3);
  - loopless relations without transitive triangles whose vertices with at least three in-neighbours induce
    an acyclic sub-relation, with no degree bound (Theorem T), and its block form for loopless relations
    (Corollary T_int);
  - loopless relations partitioned into blocks with private outside parents, each block chordless and
    subcubic without transitive triangles, a chorded digon path without transitive triangles (Lemma S), or
    carrying an elimination certificate (Theorem PC);
  - every Cayley relation Cay(G, {s, s⁻¹, t}) without transitive triangles, for every finite group G, when
    {s, s⁻¹, t} has three elements and does not contain 1 (Corollary CC, through the circulant sweeps of
    Proposition CC).
- **Consequences on triangle-free graphs of maximum degree 3.** The barrier bound
  2 log|C| ≤ (|V| + |S| − |I(S)|) log|α| for every vertex set S; every storage code has |C| ≤ |α|^ν*, where
  ν* is the fractional matching number, with equality for some code over every alphabet β × β; and every
  index code broadcasts at least (|V| − ν*) log|α|, with equality for some index code over β × β whenever β
  is a finite abelian group. The fractional Tutte–Berge formula is proved along the way from Hall's
  theorem.

Not formalized:
- Lemma 2.1 (transitive triangles are paired paths of length three), Corollary 5.11 (Theorem PC for digon
  components), Corollary 6.9 (paid deletion), Proposition 7.1 (no private proper pieces in
  Cay(Z₉, {1, −1, 3})) and Proposition 8.1 (what the directed degree-three conjecture would give), each with a
  complete written proof in the paper;
- Remarks 6.5 and 6.8, which derive from the formalized theorems that the asymptotic guessing number is ν*
  and the broadcast rate of index coding is |V| − ν*, and identify |V| − ν* with the fractional clique cover
  number;
- the computational remarks on the limits of the method (Remarks 7.3–7.5), checked exactly by
  `tools/verify_remarks.py`;
- the cited formula for folded cubes (Remark 7.6, also checked numerically for k = 2, 3 by
  `tools/verify_remarks.py`);
- the standard existence of a topological order of strongly connected components, which turns the block form of
  Corollary T_int (Corollary 5.4) into its component form.

## What is open

- Conjecture P: every loopless relation of in-degree at most 3 without transitive triangles has a decomposition,
  which would give the half-rate bound for all of them.
- The half-rate bound at degree four.
- The all-code question on paired-distance-separated relations of *Directed Recovery Structures in Tape
  Computations*.
- See the open-problems section of the paper.

## Building and verifying

The Lean package imports the fourth paper's package and its circular memo (both in
[`../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/`](../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/)),
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
