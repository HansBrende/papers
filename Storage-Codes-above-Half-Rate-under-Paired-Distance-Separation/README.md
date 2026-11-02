# Storage Codes above Half Rate under Paired-Distance Separation

Hans Brende and Claude Opus 5.5 (Anthropic), November 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization of the combinatorics (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It requires the eleventh paper's library (and through it the libraries of the fourth and
  fifth papers and [`lean-machine`](../lean-machine/)) by relative paths, so the sibling directories of this repository must
  be in place.
- [`tools/`](tools/): [`lean_index.py`](tools/lean_index.py) generates the index of Lean declarations and
  `lean/PaperAxioms.lean` from the paper's LaTeX sources; [`twisted_tanner.py`](tools/twisted_tanner.py) computes the
  dimension of the twisted Tanner code at `p = 7`, `ℓ = 11` exactly, the numerical check of Theorem G in the paper (not
  used in any proof).

## The question

Question 9.1 of *Directed Recovery Structures in Tape Computations* (the fifth paper of the series): fix a degree bound
`Δ`; let `N_j` be recovery relations on finite coordinate sets `V_j` with `|V_j| → ∞`, whose paired incidence graphs have
maximum degree at most `Δ` and satisfy the paired-distance condition. Must every sequence of nonempty storage codes over
finite alphabets have `limsup rate ≤ 1/2`? The fifth paper proposed it as a machine-free route to lower bounds for
linear-time matrix transposition on multitape machines, and later papers of the series state results conditional on it.

## What is proved

The answer is negative.

- **Theorem A.** For `p = 127` there are recovery relations of incidence degree at most an explicit bound
  `Δ < 127^8791448`, on which the paired distance of every coordinate tends to infinity, carrying `𝔽_{127²}`-linear
  storage codes of rate at least `8100/16130 > 0.5021`. The relations are twisted quotients of the Bruhat–Tits tree of
  `PGL₂(ℚ_{127²})` by the congruence subgroups `Γ⁺(λ₀^j)` of the icosian group, `λ₀ | 509`; the codes are Tanner codes with
  Reed–Solomon local codes of length `127² + 1` and dimension `91 · 126 + 1`.
- **Corollary A′.** Writing each symbol in 14 bits gives binary storage codes of rate above `0.5013` on relations of
  incidence degree at most `14Δ` with the same property: the fixed binary alphabet has a negative answer too.
- **Theorem A\*.** For all large primes `p` inert in `ℚ(√5)` the guaranteed rates approach `4 − 2√3 ≈ 0.536` (proved in
  the paper, not formalized).
- **Corollary U.** Forgetting the directions of the relations gives graphs of maximum degree at most `2Δ` in which every
  odd cycle is long, carrying the same codes, and binary codes of rate above `0.5013` on graphs of degree at most `28Δ`.
  So the undirected crux of the fourth paper (its Question 6.1) has a negative answer too.

The ingredients:

- **Theorem D.** Every finite simple `δ`-regular graph on `n` vertices has a lift selection (one lift of each edge in a
  double cover) of degeneracy `(2 − √3)δ + O(√(δ log n))`, through an explicit balanced charging rule.
- **Peeling and descent.** On the tree, a lift selection gives every edge an explicit *private check*, a finite sum of
  local checks that sees no other edge of its class; the recovery relation they define descends to quotients of large
  girth with bounded degree and growing paired distances (**Theorem T**).
- **Theorem G.** The Tanner codes of an explicit twisted datum over `𝔽_{p²}` on the congruence quotients have
  dimension at least `(k − 1)²/(p² + 1)` times their length, for every weight `2 ≤ k ≤ p − 2`, by Riemann–Roch on the
  Goren–Oort divisor of a Hilbert modular surface in characteristic `p`.

Formalized, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`:

- the deterministic part of Theorem D: options and degeneracy, rounding by Hall's theorem, and the expected loads and
  second moments of the fluid rule (`Fluid.lean`, `LiftSelection.lean`);
- the peeling lemma, on any locally finite graph (`Peeling.lean`);
- validity of checks on Tanner codes, and interpolation by MDS local codes (`Tanner.lean`);
- the descent: storage, both incidence degrees, and paired distances, and the symmetrized graphs: degrees and long odd
  cycles (`Descent.lean`, `Incidence.lean`);
- the binary blow-ups of relations and of graphs (`BlowUp.lean`, `Undirected.lean`);
- the numerical facts used in the proofs, including Bernstein's condition for the base graph and the rates `0.5021` and
  `0.5013` (`Numbers.lean`);
- the final step: from a family of separated checks and a tower of quotients carrying codes of rate `ρ > 1/2` that the
  descended checks annihilate, the negation `¬ MergeDepth.Q91At (β − 1)` of the eleventh paper's formal statement of
  Question 9.1, and, given an injective encoding of the field in `b` bits with `ρ log₂ |𝔽| / b > 1/2`, the negation
  `¬ MergeDepth.Q91BinaryAt (b (β − 1))` of its binary form (`Main.lean`); and, from the same hypotheses, the graphs and
  codes of Corollary U (`Undirected.lean`).

Proved in the paper but not formalized: the probabilistic step of Theorem D (Bernstein's inequality and a union bound);
the passage from a lift selection on the base graph to separated checks on the tree (covering theory and transport) and
the annihilation of the quotient Tanner codes by the descended checks; the counting of balls in the tree, the
Reed–Solomon local codes, the icosian group and its congruence subgroups, and the girth bound; Theorem G, which uses
Riemann–Roch on compactified Hilbert modular surfaces in characteristic `p`, partial Hasse invariants, the uniformization
of the supersingular locus by Rapoport–Zink spaces, and a rigidity lemma for `SL₂(ℚ_{p²})`-equivariant data; and
Theorem A\*. Remarks labelled as heuristics or numerical are not used in any proof.

## What is open

Question 9.1 for the actual cone relations of oblivious linear-time machines (the form that lower bounds for
transposition need); a bound 1 − ρ, with ρ > 0 independent of the degree, on relations with the paired-distance property; `𝔽₂`-linear
codes; small degree bounds; rates above `4 − 2√3`; and linear codes in characteristic zero. See the open-problems section
of the paper.

## Building and verifying

The Lean package requires the eleventh paper's library by a relative path. Clone the whole papers repository so that the
sibling directories stay in place. Install [elan](https://github.com/leanprover/elan), then in `lean/`:

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

Every declaration should report at most the axioms `propext`, `Classical.choice` and `Quot.sound`. After editing the paper,
regenerate the index of Lean declarations and `lean/PaperAxioms.lean` (from this directory):

```bash
python3 tools/lean_index.py
```

To build the PDF, run `latexmk -pdf -interaction=nonstopmode main.tex` in `paper/`.

The numerical check of Theorem G (about 20 seconds; it prints the dimensions for `k = 2, …, 5` and ends with
`ALL CHECKS PASSED`), from this directory:

```bash
uv run --with numpy python tools/twisted_tanner.py
```
