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
  - The matching form: the minrank is N − ν(G) over every field, where ν(G) is the matching number. The
    Tutte–Berge formula it needs comes from [`lean-machine`](../lean-machine/), which ports J. P. Traverso
    Gianini's formalization.
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

## Formalization to-dos

What remains unformalized, grouped by what it needs, with estimates and the existing pieces, so they
need not be searched for again. Numbers are those of the paper.
- **Unit:** agent time. One agent-day is a day of continuous work by an AI agent, including builds
  and a check of each Lean statement against the paper. Estimates for small finite items have run
  high; items that need theory missing from Mathlib carry the opposite risk.
- **Paths:**
  - `P1`: the first paper's `lean/Transpose`, namespace `Transpose.Tape` unless noted;
  - `P2`: the second paper's `lean/TransposeFollowup`, namespace `TransposeFollowup`;
  - `P3`: the third paper's `lean/BitWord`;
  - `ML`: Mathlib v4.34.1.
- **External code** (Tau Ceti, GitHub repositories) goes through [`lean-machine`](../lean-machine/):
  pinned commit, full read, and a provenance record. All the projects named below pin newer Mathlib
  versions, so reuse means porting.

### 1. Finite algebra and graph theory (about 1.5–3 agent-days)
**Results:** 6.24 (index-two nilpotence at girth five), 6.25 (sign twins), 6.27 (smallest
counterexamples), 6.28 (Proposition L), 6.30 (eigenvalue codes and girth), 6.31 (Proposition HS),
6.33, 6.34 and 6.35 (Mycielskians).
- **ML:**
  - `SimpleGraph.IsSRGWith` with `IsSRGWith.matrix_eq` (Combinatorics/SimpleGraph/StronglyRegular.lean);
  - `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` (AdjMatrix.lean);
  - `Matrix.IsHermitian.spectral_theorem` and its eigenvalues (Analysis/Matrix/Spectrum.lean);
  - `LinearMap.IsSymmetric.card_filter_eigenvalues_eq` (multiplicity = dimension of the eigenspace);
  - `SimpleGraph.girth`;
  - homomorphisms `→g`, `Colorable.of_hom`;
  - `Submodule.smithNormalForm` (basis form over a PID, with no divisibility chain).
- **P1:** `Transpose.ShearFrame.rank_map_zmod_le_rank_map_rat` (Frames/RankMod.lean:70), rank mod 2 ≤
  rank over ℚ. Generalizing it to every prime is mechanical, about 1–2 hours; 6.31 needs it.
- **External:**
  - The Mycielskian `SimpleGraph.mycielski`, with `chromaticNumber_mycielski` and
    `CliqueFree.mycielski`, in
    [AItoBit/erdos-627-palomar](https://github.com/AItoBit/erdos-627-palomar), file
    `Erdos627/Mycielski.lean`: about 200 lines, Apache-2.0, Mathlib one day newer than ours.
  - The Moore-graph theorem (`isSRGWith` for (k²+1, k, 0, 1), proved through eigenvalues) in
    [jtraverso/moore-graphs-hoffman-singleton](https://github.com/jtraverso/moore-graphs-hoffman-singleton),
    Apache-2.0. It does not define the 50-vertex graph itself.
  - A Smith normal form with divisibility chain for square integer matrices of nonzero determinant:
    Tau Ceti, `TauCeti/LinearAlgebra/Matrix/SmithNormalForm.lean`.
- **Missing:** the explicit Hoffman–Singleton graph, non-backtracking walk counts, rank modulo p versus
  over ℚ for general p.

### 2. Machine-level decomposition (about 2–4 agent-days; Corollary B also needs Theorem B, item 3)
**Results:** 4.2, 4.4 (cone lemma), 4.5, 4.10 (Theorem D), 4.11, 4.13, 4.14 and 4.23 (Corollary B).
- **P1, the model:** `ObliviousOn` (Defs.lean:98), `transAt` (Defs.lean:64), `run_succ_state_of_some`,
  `headSym_eq_writtenSym` and `headSym_eq_blank` (Run.lean). With these, 4.2 is nearly immediate;
  `locality_function` applied to a one-step set also gives it.
- **P1, the cone lemma (a):** `locality_oblivious` (Locality.lean:138), `locality` (:87) and the
  adaptive `locality_core` (:224), with `entryPoints` and `entryCells` (Defs.lean). Applied to a cone,
  the entry points are the edges into the genie. The glue is about 100–200 lines: the dependency DAG,
  cones, and closure under genie-free edges.
- **P1, the cone lemma (b):** `addrCount`, `card_addresses_le` (Forest.lean), `addrCount_mul`.
- **P1, output bits:** `tpos` (Defs.lean:149), `tpos_tpos`, `tpos_lt`, `nth_encode_transpose_tpos`,
  `output_nth_eq_outBit`, `oblivious_outRev_length`, `outBit_of_mem_cutSet_on` (Counting.lean).
- **P1, templates for 4.10 and 4.11:** `ObliviousLinearTimeTransposable` (DefsCE.lean:619) and the
  proofs in CEMain.lean, `fast_of_computesWithin`, `transposes_of_transposesWithin`; idle tapes as in
  `bufTM` (BufTM.lean).
- **P1, counting for 4.14(a):** `two_pow_mul_ncard_le`, `card_le_entryData` (Counting.lean).
- **P3:** `run_congr_on_ancestry`, `ancestry_card`, `record_card_le` (ScanAncestry.lean), a cone lemma
  with a revealed record in another model; usable as a template only.
- **Missing:** index codes and side-information systems, the crux and depth-TCP, and the value width
  β. Only `cellBits` (P1, DefsM.lean) and the count of state bits exist.

### 3. Walk combinatorics (about 1.5–3 agent-weeks)
**Results:**
- 4.16–4.18, 4.20 (Theorem B), 4.21;
- 5.2, 5.4 (structure of U), 5.8, 5.10, 5.12, 5.13 (clock labels), 5.14 (packing), 5.16;
- the general chain and transfer identities 5.17 and 5.18 (their exact cases are formal);
- 5.20 (Euler) and 5.22 (Theorem E₁).

**Existing:**
- **P1:**
  - hops as previous visits: `IsLastVisit` (Defs.lean:122), `exists_lastVisit`, `isLastVisit_unique`,
    `isLastVisit_congr`;
  - unit-step walks: `UnitSteps` (Defs.lean:188);
  - monotone passes: `greedyBound`, `greedy_passPartition`, `greedyPasses_le`, `pass_fresh`
    (Passes.lean). These must be adapted from all heads to one walk, for legs.
- **P2:** `NestedExcursion` (ExcursionIntervalTransfer.lean), and depth-residue cuts on forests in the
  `AdaptiveForest*` modules (patterns only).
- **The second paper's memo:** `excursion_isLastVisit`, the hops of an explicit walk.
- **ML:** `Order.height` and `Order.height_add_one_le`, for labels from longest paths (5.2).
  Proposition 5.14 needs only weak LP duality, which is elementary.

**Missing:** the walk DAG with cuts and depth, labels, leg area, home-based walks, and the recursive
walk U(s₀, m, g) with its covers.

### 4. Motion (about 2 agent-weeks, without Connes–Feldman–Weiss)
**Results:** 3.3, 3.5–3.9, 3.12–3.14 (Theorems C, C′, Cq), 3.15, 3.16, 3.20, 3.21, 3.23, 3.24.

**A shorter route.** The paper proves Theorem Cq through Lemma 3.8, which uses Connes–Feldman–Weiss,
Ornstein–Weiss and Dougherty–Jackson–Kechris; none of these exists in Lean anywhere. They are not
needed:
- **Cq.** For N affine pieces, P2's `exists_finite_affine_branch_small_cut` gives a label with small
  classes and few retained crossings. Every other crossing has an endpoint in the omitted set O_N,
  each visit lies in at most two consecutive pairs, and Banach's inequality ∫#(O ∩ Λ(p)) dp ≤ ν(O)
  charges them. Then (⋆)_∅ gives 1 ≤ ε + 2θ + 2 Σ_t ν_t(O_{t,N}), and Σ_t ν_t(N_t) ≥ ½ as N → ∞.
- **C.** The home-level set is one constant piece and the uncovered set is countable, so the Lebesgue
  charge suffices.
- **The rest.** The same argument gives Theorem C′ and both forms of 3.16, and with small lemmas
  3.21 and 3.24.
- **Status.** This route was checked against the Lean sources; it has not been refereed. Taking it
  removes the need for 3.5–3.9 (and so for Lusin–Novikov and Connes–Feldman–Weiss), and Section 3's
  proofs would change accordingly.

**Existing:**
- **P2:**
  - `exists_finite_affine_branch_small_cut` (AffineBranchCuts.lean:100), for finitely many
    measurable pieces;
  - `exists_affine_small_boundary` (AffineFiniteBoundary.lean:66), Følner sets for finitely many
    affine maps;
  - `one_le_of_star_small_cuts` and `SatisfiesStar` (FiniteAffineTimeBound.lean);
  - `exists_countable_affine_path_cut_bound` (CountableAffinePathLabels.lean), which takes no (⋆)
    hypothesis;
  - `exists_countable_local_affine_cover`, `star_half_le_locally_affine_omission`,
    `star_half_le_affine_component_omission`, `star_common_affine_omission` (OpenAffineTimeBound.lean).
    These are the Lebesgue form of 3.16 with relatively open pieces, up to a few hours of wrappers.
  - the omitted-set charge `lintegral_levelCross_delete_le` (OmittedVisitBound.lean), through
    `compact_visit_majorant`, `interval_visit_majorant` and `lintegral_compact_visits_le`
    (CompactVisitMajorant.lean) and `exists_compact_interval_cover` (CompactIntervalCover.lean);
  - `block_physical_sample_error` (PhysicalWalkNormalization.lean), for 3.15.
- **P1:**
  - limits: `theoremMStar_level_adaptive` (MStarAdaptive.lean), `theoremMStar_level_class_on`
    (Statements/Adaptive.lean), `blockTraj_limit_lipschitz`, `exists_subseq_blockTraj` (MStarTM.lean);
  - level sets and crossings: `levelSet`, `ConsecIn`, `crossPairs`, `levelCross`, `PiecewiseConstOn`
    (DefsM.lean);
  - in MStarAnalysis.lean: `ae_finite_levelSet`; the easy half of Banach's indicatrix,
    `lintegral_encard_levelSet_le`; dyadic counting with `dyCount`, `card_le_dyCount` and
    `encard_le_liminf_dyCount`.
- **ML:**
  - `LipschitzWith.ae_differentiableAt_of_real`;
  - `LipschitzOnWith.absolutelyContinuousOnInterval` and
    `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`;
  - `lintegral_image_eq_lintegral_abs_deriv_mul` (JacobianOneDim.lean);
  - `addHaar_image_le_lintegral_abs_det_fderiv` and
    `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (Jacobian.lean);
  - `measurableSet_of_differentiableAt`, `lintegral_liminf_le`, `tendsto_measure_iInter_atTop`;
  - `exists_pos_setLIntegral_lt_of_measure_lt`, for ε–δ absolute continuity.
- **External:** the full area formula `LipschitzWith.lintegral_normDet_fderiv_eq_lintegral_encard`
  and Banach's indicatrix `ContinuousOn.eVariationOn_eq_lintegral_encard`, in
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti), `TauCeti/MeasureTheory/Function/AreaFormula/`
  (Apache-2.0, October 2026 Mathlib, a moderate backport). Only Lemma 3.3 as stated, an equality, needs
  them; the route above needs only the inequality.

**New lemmas, with estimates:**

| Lemma | Estimate |
|---|---|
| a (⋆)_∅ copy of `one_le_of_star_small_cuts` | 1 h |
| the visit majorant for arbitrary sets | 3–5 h |
| the Lebesgue form with Borel pieces | 3–6 h |
| the visit majorant for the speed measure ν | 8–16 h |
| Cq from it | 2–4 h |
| 3.15 in countable form | 8–20 h |
| a time change, for 3.21 | 4–8 h |
| ε–δ absolute continuity | 1–2 h |
| cheap labels for a single path, for 3.20 and 3.24(c) | 12–24 h |
| machine wrappers | 3–6 h, plus 2–4 h per theorem |

### 5. Theorem A and its consequences (months in full; 3–6 agent-weeks conditionally)
**Results:** 6.17 (Theorem A), 6.18, 6.21 and 6.22 (the torsion-only principle).
- **ML:**
  - Prokhorov's theorem (MeasureTheory/Measure/Prokhorov.lean);
  - weak convergence with the Portmanteau bound `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`
    (Portmanteau.lean), which gives upper semicontinuity of the spectral atom at 0;
  - `VonNeumannAlgebra`, a definition only;
  - the continuous functional calculus `cfc` and `CFC.abs`;
  - `Submodule.smithNormalForm`.
- **External:**
  - polar decomposition `ContinuousLinearMap.polarFactor` and projection-valued measures, in Tau Ceti
    (October 2026 Mathlib);
  - group von Neumann algebras with their trace in
    [openai/ten-proofs](https://github.com/openai/ten-proofs), `ConnesRigidity.lean` (Lean v4.32.0).
- **Missing everywhere:** Benjamini–Schramm local convergence, unimodular random networks and the
  mass-transport principle, traces and dimension in von Neumann algebras, and the link between
  p-divisible invariant factors and rank modulo p.
- **Shortcuts:**
  - The algebraic part of 6.22, given the conclusion of Theorem A, takes a few hours with a matrix
    Smith normal form.
  - A conditional version could take the four standard facts (L1)–(L4) of Section 6.7 as hypotheses.

### Not counted
- The remarks marked "Proof sketch only" (3.19, 5.6, 5.7, 6.38) need complete proofs first.
- The computational remarks with exact certificates take a few hours each through
  `tools/certificates.py`: the Grötzsch graph and the circulants C₁₃(1,5), C₁₆(1,3,8) and C₂₀(1,6,10),
  the last with 777 rows. Measure build time first.

## Building and verifying

The Lean package imports the second paper's package, through it the first paper's, and the shared library
[`lean-machine`](../lean-machine/), by relative paths. Clone the whole papers repository so that the sibling directories
stay in place. Then fetch the second paper's pinned external
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
