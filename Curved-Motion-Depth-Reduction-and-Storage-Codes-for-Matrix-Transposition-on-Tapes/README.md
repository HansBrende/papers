# Curved Motion, Depth Reduction, and Storage Codes for Matrix Transposition on Tapes

Hans Brende and Claude Opus 5.5 (Anthropic), October 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)).
- [`tools/`](tools/):
  - [`certificates.py`](tools/certificates.py) generates the exact Shannon certificates used in the Lean proofs
    (needs `numpy` and `scipy`);
  - [`lean_index.py`](tools/lean_index.py) generates the index of Lean declarations and `lean/PaperAxioms.lean`
    from the paper's LaTeX sources.

## The question

Can a deterministic multitape Turing machine transpose a d × d matrix with ⌈log₂ d⌉-bit entries, written row by
row, in time linear in the input length L = d²⌈log₂ d⌉? This is the statement (T) of the
[first paper](../Matrix-Transposition-and-the-Tape-Coding-Conjecture/). It is open, and this paper does not decide it.

This paper asks what a linear-time transposer would need. We find three ingredients:
- head motion that is curved and head-dependent;
- time–space dependencies that resist depth reduction, or else extreme coding on shallow ones;
- storage codes that beat rate ½ on sparse, locally bipartite side information.

We prove restricted versions of all three. Theorem D reduces the oblivious case of (T) to two precisely stated open
problems: depth reduction for interacting walks, and an index-coding lower bound on the side information of shallow
cones.

## What is proved

**In Lean.** Everything in this list is proved in Lean, with no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`. [`lean/PaperAxioms.lean`](lean/PaperAxioms.lean) checks every declaration the paper names.

- **Theorem H.** Rate bounds pull back along homomorphisms of graphs and of digraphs, for every valid polymatroid.
  So they hold for the entropy of every storage code, linear or not, over every alphabet. The entropy layer is
  reused from the [second paper](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/).
- **Symmetrization.** A rate bound needs to be checked only on polymatroids invariant under the automorphisms of the
  side information.
- **Good targets.** A graph is good if every valid polymatroid has 2h(V) ≤ Σ_v h(v).
  - C₅, the Petersen graph and the circular clique K₁₄/₅ are good, by exact certificates.
  - If p/q ≤ p′/q′, then i ↦ ⌊p′i/p⌋ is a homomorphism K_{p/q} → K_{p′/q′} (Bondy–Hell). So every circular clique
    K_{p/q} with p/q ≤ 14/5 is good, and so is every odd cycle of length at least 5.
- **Corollary H2.** On every good graph, in particular on every graph that maps homomorphically to a good graph,
  every storage code C ⊆ α^V satisfies |C|² ≤ |α|^|V|, and every recoverable random word satisfies 2H(X) ≤ Σ_v H(X_v).
  There is no degree assumption.
- **Corollary H4: gn(Clebsch) = 10.** Every storage code on the Clebsch graph over an alphabet of size q has at most
  q¹⁰ codewords. The binary code ker(I + A) has exactly 2¹⁰, so I + A has rank 6 over GF(2). The rate bound c holds
  for all valid polymatroids on the Clebsch graph exactly when c ≥ 5/8.
- **Theorem S.** On a triangle-free graph with N vertices and maximum degree at most 3, every matrix over any field
  with unit diagonal and off-diagonal support in the edges has nullity at most ⌊N/2⌋. So every linear storage code
  over every field has dimension at most ⌊N/2⌋.
  - The proof covers every matrix with unit diagonal and no recovery triangle whose vertices satisfy a reciprocity
    condition (★★), not only graphs of maximum degree 3.
  - It gives the barrier form dim ≤ |U| + Σ_B ⌊|B|/2⌋ over separated blocks B of the vertices outside U.
  - Conversely, for every graph and field, a matching of m edges gives a linear storage code of dimension m.
  - Linear storage codes are exactly the subspaces of kernels of such matrices.
- **Depth labels.**
  - Lemma Zq: the exact cost identity for labels on a cyclic schedule.
  - The exact cases of the chain decomposition and the transfer identity.
  - Theorem E in abstract form: hop-disjoint cycles of negative defect each cost about one violation.

**In the paper, with complete proofs, not formalized.**
- **The decomposition.** Theorem D: depth reduction plus an index-coding crux refute oblivious (T). Also the forced
  trade-off between genie cost and depth, and the limits of counting arguments.
- **Depth reduction for home-based walks.**
  - Theorem B: every coupling of walks of linear leg area, in particular home-based walks, can be cut to bounded
    depth.
  - Corollary B: home-based oblivious machines reduce to the crux.
- **Curved motion.**
  - Theorems C, C′ and Cq: no machine, oblivious or adaptive, whose work heads are all home-based with legs made of
    boundedly many constant-rate runs transposes in linear time. In every macroscopic limit of a linear-time
    transposer, at least half a block unit of travel, a linear number of cells, is not countably-piecewise affine.
  - One work tape never suffices, a common change of clock does not help, and machines whose work heads all
    follow stroke trees fail.
- **Depth reduction for interacting walks.**
  - One walk is always depth-reducible, by planarity.
  - Packing certificates cannot show depth-robustness.
  - Theorem E₁: on the golden deep-nesting pair with one level of nesting, labels exact on one head pay a fixed
    price per hop on the cover at every depth, at least 67/4096 at all but the smallest scale.
- **Analytic results on storage codes.**
  - Theorem A: on locally bipartite graphs of bounded degree, complex matrices with unit diagonal, graph support and
    bounded entries have rank at least (½ − o(1))N.
  - The torsion principle for finite-field linear codes, and sign twins in odd characteristic.
  - The limits of local arguments at degree at least 4 (Proposition L) and of eigenvalue codes, and a
    code beating rate ½ on the Hoffman–Singleton graph outside characteristic 2 (Proposition HS).
  - Mycielskians leave the good graphs.
- **Classical input.** The matching form of Theorem S (minrank = N − ν) uses the Tutte–Berge formula, which is not
  formalized here.

The barrier against per-head band rules on deeply nested walks is stated with a proof sketch only. Numerical
observations are labelled as such and are never used in proofs.

## What is open

- (T) itself.
- Depth reduction for interacting walks at fixed ε (TCP, the trajectory cut problem). Its first open case has two
  walks, and its sharpest instance is the deep-nesting pair (Conjecture A′).
- The crux in positive characteristic and for nonlinear codes. On locally bipartite graphs, it is open for
  scalar linear codes over finite fields at degree at least 4 (vector-linear ones already at degree 3) and for nonlinear codes at
  degree at least 3. Its directed, depth-bounded form, which Theorem D needs, is open in general.
- Question G: is the fractional chromatic number unbounded on good graphs?

## Building and verifying

The Lean package imports the second paper's package, and through it the first paper's, by relative paths. Clone the
whole papers repository so that the sibling directories stay in place. Then fetch the second paper's pinned external
dependency as described in its
[README](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/).
Install [elan](https://github.com/leanprover/elan), then in `lean/`:

```bash
lake exe cache get
```

```bash
lake build
```

Check the axioms of every declaration the paper names:

```bash
lake env lean PaperAxioms.lean
```

After editing the paper, regenerate the index of Lean declarations and `PaperAxioms.lean` (from this directory):

```bash
python3 tools/lean_index.py
```

To regenerate a certificate, run for example (from this directory):

```bash
python3 tools/certificates.py clebsch 5 8 clebsch clebschNbhd --all-pairs
```

The script prints the automorphisms and the proof in the form used by the Lean files. To build the PDF, run
`latexmk -pdf main.tex` in `paper/`.
