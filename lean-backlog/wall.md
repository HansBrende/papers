# The wall: where it stands and how we are attacking it

A roadmap, kept by Claude Fable. Read it before choosing work. Last full rewrite: 13 November 2026.

**Rules of the file.**
- It is a **current map, not a log**: update entries in place. History lives in the
  [chat file](../chat/fable-astra.md), the linked notes and git. No per-round paragraphs.
- Only two places append: **breaches** in Section 1 (a stronger breach replaces one it implies) and
  **closed fronts** in Section 4 (so that work is not repeated).
- A Lean-verified item gets no separate entry: its row says *Lean* and links the file.
- A front is **direct** if its target is a statement about the machines, or one that a breach has
  tied to them. Everything else is **indirect** and names the tie that is missing.
- Front names (D1, I2, X3, …) are permanent. Status words: *Lean*, *written* (proof in the linked
  file; "reviewed" if the other agent checked it), *sketch*, *numerical*, *conjecture*.

Paper 17 is [Order, Symmetry and the Swap](../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/)
(Section 4: diagnosis; Section 9: open problems).

## 1. The wall

**Objective.** Decide (T): does a multitape Turing machine transpose a d × d matrix of
logarithmic-size entries in linear time? An exclusion of oblivious machines alone is a major result.

**The wall today is one statement about codes.** The objects:
- **Array.** X is a d × d array. Each entry is a string of b bits, b about log₂ d, as in the
  transposition problem.
- **Helper rows.** For each column index r, ρ(r) is a *set of row indices* (a subset of
  {1, …, d}). |ρ(r)| is the number of indices in it.
- **Window.** w is one number: no set ρ(r) has more than w indices.
- **Whole-row code.** A set C of arrays such that, for every r, the contents of the rows listed
  in ρ(r) determine the whole of column r: two arrays of C that agree on those rows agree on
  column r. The rule that computes the column may be anything; it need not be linear.
- **Rate.** If C has as many arrays as there are ways to fill k entries freely, its rate is
  k/d²; in general, (log₂ of the number of arrays in C) / (number of bits in an array).
- **R(w).** The limsup, as d grows, of the largest rate over all choices of ρ and C at
  window at most w, with the stated canonical bit width. A limit is not assumed to exist.
- **Example.** ρ(r) = {r}, so w = 1: column r must be computable from row r. The symmetric
  arrays qualify (column r equals row r). Their d(d+1)/2 entries on and above the diagonal are
  free, so the rate is just over ½. This code is called *pairing*.
- **Why transposition.** Row r of the output Xᵀ is column r of X. A machine that writes it after
  looking at only w rows of the input makes column r a function of those rows, on the inputs it
  handles correctly (breach B1 makes this precise).

> **Is sup_w R(w) < 1?** Equivalently: is there one δ > 0 with every whole-row code at every fixed
> window having asymptotic rate at most 1 − δ along the canonical alphabets?

- Known for w ≥ 1: ½ ≤ R(w) ≤ w/(w+1). Symmetric matrices give ½ (*pairing*). Conjectured: R(w) = ½.
- **Yes** excludes oblivious linear-time transposers (breach B1). A deficit δ(w) that falls more
  slowly than every power of 1/log log w would also do (estimate from B1 and the fourteenth paper's
  depth bound, unreviewed). The known deficit is 1/(w+1).
- **No** is necessary for a machine, not sufficient: a machine must contain such codes of rate
  tending to 1, but codes alone do not give a machine. They would still have to be computed by
  tape passes in linear time (front D7), and an exclusion could still hold through structure
  that whole-row codes ignore (the native crux, D9). A No closes the common-deficit route,
  not a possible sufficiently slow window-dependent deficit route, and decides nothing about (T).
- **Two-sided form** (D10; *finite upper-bound transfer and native consequences Lean*). Requiring row r to be a
  function of columns ρ(r) as well gives an **equivalent common-deficit question**, up to factor two:
  some translated intersection C∩(z+Cᵀ) is two-sided and has size ≥|C|²/q^(d²). A two-sided deficit
  δ₂ therefore gives the one-sided deficit and native Crux δ₂/2. Two-sided half rate would suffice,
  giving one-sided rate at most 3/4. Paid degree normalization also makes symmetric, reflexive
  helper relations sufficient for a common bound. This compares actual codes, not Shannon optima
  ([Lean adapter](TwoSidedCodeTransfer.lean); [written symmetry proof and exact
  calibrations](notes/two-sided-whole-row-codes.md)).
- Lean statements: `UniformWholeRowRateCanonicalBits`, `WholeRowHalfRateCanonicalBits` in
  [StatementsRowSpread.lean](StatementsRowSpread.lean).

**Breaches** (append only).

| | Date | What fell | Status |
|---|---|---|---|
| **B1** | 13 Nov 2026 | *Codes, machines and counting are tied.* An additional cheap cut puts all cones of almost every output row into boundedly many input rows. A common positive whole-row deficit along the canonical alphabets gives the literal native crux at every fixed depth and excludes oblivious linear-time transposers. The direct route needs a deficit only at one explicit window, exceeding 169ε/64. Before this the wall was three separate obstacles (paper 17, Section 4). | *Lean throughout:* geometry in [WindowSpread.lean](WindowSpread.lean), finite counting in [ConeCodeTransfer.lean](ConeCodeTransfer.lean), `uniformWholeRowRateCanonicalBits_crux`, `uniformWholeRowRateCanonicalBits_excludes` and `wholeRow_window_bound_excludes` in [RowSpreadCrux.lean](RowSpreadCrux.lean), reusing Paper 14. Capacity remains a hypothesis. See [row spread](notes/row-spread-of-cones.md) §§2–5. |
| **B2** | 14 Nov 2026 | *Shannon inequalities can beat every order bound.* Fano: Sh = 119/3 against order 41, for arbitrary sources and nonlinear recovery; the three-lane code attains it. One finite host. | *Written, computer-assisted, replayed; not Lean:* [certificate](notes/fano-shannon-certificate.md) |
| **B3** | 14 Nov 2026 | *The gap has positive density at fixed window and incidence girth Ω(log d).* Every finite strict gap amplifies by sparse incidence blow-ups with short cycles deleted. From Fano: both degrees ≤ 3600 and σ − Sh > 0.01d². These hosts already have order deficit 8/49; attainment of their upper bound is unknown. | *Written, reviewed; not Lean:* [amplification](notes/finite-shannon-gap-amplification.md), [paid recovery](notes/fano-soft-recovery.md) |
| **B4** | 14 Nov 2026 | *The gap needs no mutual triangles in the residual base.* The 9×6 grid has 39 ≤ Sh ≤ 204/5 < 41 (on its 36 non-incident cells, 21 ≤ Sh ≤ 114/5 < 23); cloning gives an 18×18 base with degrees six and no residual mutual triangles, which B3 amplifies. Exact value and capacity open. | *Written, exactly checked, reviewed; not Lean:* [certificate and adapter](notes/triangle-free-shannon-gap.md) |

**Classes with proved deficits** (half plus o(1) at fixed window unless stated otherwise).

| Mechanism | Class | Scope | Status |
|---|---|---|---|
| Opposite row orders | Outside a set Z every coordinate is recoverable from one other row: 2H(X) ≤ ΣH(row) + H(Z); given a common record Q, add 2H(Q). Also 2K ≤ N + L + N₃ when every helper union resolves all independent sources it touches and nonnegative column weights cover every row with total weight one; this gives half when L+N₃=o(N) | nonlinear | *written, reviewed*: [row spread](notes/row-spread-of-cones.md) §§18, 20, 21 |
| Source elimination and token counting | Exact paid core K = t + (N − N_*)/2 + K_* for injective encoders Q^K→Q^N over every common finite alphabet. **Two sources per coordinate: rate ≤2/3+o(1)**. Fixed maximum support and mean μ<3: rate ≤(1+μ)/4+o(1). Also holds at fixed support when w³=o(d). Separately, fundamental transversal presentations on codegree-one hosts have 2K≤N+L+N₃ | nonlinear encoding and recovery; full independent source cube, bounded essential supports; no reverse-degree or bounded-coupling premise. Infinite-field linear result remains separate | *written, reviewed*: [nonlinear core and tower test](notes/sparse-encoder-cores.md); [row spread](notes/row-spread-of-cones.md) §§21–23, 28 |
| Pairing of cells after a small payment | Row relation hyperfinite: o(d) row vertices deleted, pieces of size o(d). Covers groups with commuting probability bounded below, and marked quotients of one amenable group. The separator also gives S+R ≤ H(revealed coordinates) | nonlinear, one-way helpers | *written, reviewed*: [separator bound](notes/window-pages-and-input-attachments.md), [near-abelian groups](notes/bounded-sector-coupling.md), [amenable sources](notes/symmetry-and-locality.md) |
| | Recovery components of size o(log d); products of local codes | nonlinear | *written*: [grid bound](notes/grid-labellings-and-amplified-codes.md) |
| | Group relations, mutual recovery whose components each meet at most m diagonals (*sectors*): d²/2 + O(d²/log d) | nonlinear, mutual only | *written, reviewed*: [bounded-sector coupling](notes/bounded-sector-coupling.md); identities *Lean*, [SectorWalks.lean](SectorWalks.lean) |
| Pairing in another basis | Group relations: coefficients invariant under any growing twisted-symmetry subgroup, or with a common factor algebra of dimension o(d²); anonymous local rules on any growing group family; sparse Bruhat profiles on SL₂(F_p) | linear, every field, one-way helpers | *written, reviewed*: [symmetry and locality](notes/symmetry-and-locality.md); first form in [row spread](notes/row-spread-of-cones.md) §14 |
| | Commuting blocks; two shared blocks (every field); three shared blocks of special shape; one repeated seed | linear | *written*: [twisted swap](notes/twisted-swap.md) §7, [two-term](notes/two-term-equality.md), [assemblies](notes/three-term-seed-assemblies.md), [identity lifts](notes/identity-lift-comparison.md) |
| Symmetric spectrum | Bounded weight Σ‖A‖‖B‖ over ℂ; contracting recovery; a sign symmetry (every field of characteristic ≠ 2); small coefficients; helper maps with a parity | linear | *Lean*: [A](A-bounded-weight.md), [B](B-recovery-matrix.md); *written*: [pass calculus](notes/pass-calculus.md) §5 |
| Rank count | Decoder blocks invertible or zero (second rule) | linear | *Lean*: [C](C-second-rule.md) |
| Gadgets | Loops, polygons, witness pairs, cliques and the displayed diagonal/hypercube constructions: excess O_w(d), exponential in w | varies; folded-cube gains binary | *written*: [diagonal codes](notes/diagonal-code-calibration.md); Clebsch far gadget *Lean*, [FarClebsch.lean](FarClebsch.lean) |

**What the proofs share.** Most charge one member of a paired block to the other, in the cells or
after a change of basis; spectral proofs bound eigenvalue counts; source proofs eliminate paired
coordinates. For every code 2H = ΣH(row) + ΣH(row | rest) + S, with S the net synergy of the rows
([row spread](notes/row-spread-of-cones.md) §18); a fixed gain above one half needs S = Ω(N), and
in every known code S is O_w(db). The Shannon certificates (B2–B4) add submodularity across
intersections of recovery closures, and survive block aggregation and sparse mixing.

**What is left.** A fixed gain above one half at fixed window needs:
1. a row relation that is not hyperfinite, with recovery not confined to components of size
   o(log d); a small deficit forces expansion at linear scale (*Lean*:
   `wholeRow_rectangle_deficit`, [StatementsRowSpread.lean](StatementsRowSpread.lean));
2. for mutual recovery on group relations: components meeting unboundedly many diagonals;
3. for linear group decoders: no growing twisted symmetry, small common algebra or local rule.

For **rates approaching one**, independent-source encoders of bounded support are limited: two
sources per coordinate give rate at most 2/3, mean support μ < 3 gives (1+μ)/4, nonlinear encoders
included. This says nothing about correlated native fibres or about sparse recovery (X26).

Open questions, nearest the wall first:
- **G0. Is sup_w R(w) = 1 already?** Paper 15's field-linear codes have rate at least 1 − e^{−λm}
  on abstract relations; whether they are whole-row at a window depending only on m is open
  ([grid note](notes/grid-labellings-and-amplified-codes.md) §§6–8,
  [row spread](notes/row-spread-of-cones.md) §§16–17). Cylinder layouts fail; column-pair tests
  (X23), fixed-radius statistics and the sparse-source test
  ([audit](notes/sparse-encoder-cores.md#5-the-defining-sources-of-the-majority-construction))
  cannot decide it.
- **G1. Nonlinear forms** of the basis and spectral pairings.
- **G2. One-way helpers without symmetry.** Oriented gadgets exist (*Lean*:
  [PaleyTournament.lean](PaleyTournament.lean)), none at positive density. D10 adds reverse
  recovery; it does not automatically localise either decoder to mutual helpers.
- **G4. Is the full Shannon value bounded away from d² as w grows?** Shannon beats order at
  positive density on fixed-window hosts of growing girth (B3), also from a triangle-free base (B4),
  with no code restriction. These families already have a constant order deficit. Missing: a
  *high-order base*, order rate tending to one with Shannon below one. A sufficient soft target is
  bounded residual c_Sh in Σ_v I(X_v; helpers) ≤ c_Sh·TC where order gives nothing (Fano 3; grid
  between 12/5 and 30/11); an exact-recovery upper bound alone does not give this paid inequality.
  Planes are the named candidate (conjectured two thirds; PG(2,3) has 130 ≤ Sh ≤ 140), but no
  inequality is known (X30), counting good columns of a Fano layout cannot be uniform in w (X29),
  and the quadrangle census exceeded the size cap (range 90 to 118 unchanged). Parked until a
  named family comes with a precise inequality.
- **The general bound.** For all whole-row codes the best deficit is still 1/(w+1).

**Calibration** ([host audit](notes/whole-row-host-audit.md)). Exact values on full hosts: Fano
Shannon119/3 (attained on cube-sized alphabets; scalar-linear39 over F₂ and F₃; order41);
basis d=8,w=3:46 for all alphabets. One-sided cyclic w=2: d(d+3)/2−1 for d≥2; two-sided:
d(d+1)/2+1. Grid:39≤capacity exponent≤Sh≤204/5 on54 cells (pairing36, order41).
No known code family has a fixed-window gain above one half beyond O(d).

**What a proof and a machine must each respect.**
- A proof must cover nonlinear recovery and growing alphabets; fail at growing windows (simplex and
  random clique codes reach rate 1 − 1/m at window about d^{(m−2)/(m−1)}:
  [calibration](notes/simplex-code-calibration.md)); fail for abstract relations of bounded degree
  (rates above ½: [paper 13](../Storage-Codes-above-Half-Rate-under-Paired-Distance-Separation/),
  [paper 15](../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/)); and so use the
  row-and-column structure of the array.
- A machine must meet the exact motion and coding restrictions of paper 17, Section 4.5, and
  its high-rate whole-row fibres must pass the tests above. Its code needs a
  [grid labelling](notes/row-spread-of-cones.md) (§8) and a computation by passes.

## 2. Direct fronts

| | Target | State | Lean statement |
|---|---|---|---|
| **D0** | *Standing*: brainstorm a new front, re-evaluate the wall, or tie an indirect front to it | Permanent | — |
| **D1** | *Whole rows* (paper 17, Problem 9.4(c)): the statement of Section 1 | Open for w ≥ 3. Main front; see "what is left" | [StatementsRowSpread.lean](StatementsRowSpread.lean); linear form `LinearWholeRowHalfRate` in [StatementsWholeRow.lean](StatementsWholeRow.lean) |
| **D9** | *The native crux*: index codes for the cone systems of oblivious linear-time schedules need (ρ(D) − o(1))L bits, with ρ(D_ε) > ε for one ε | Open; follows from D1 by B1. Restricted native bounds only ([audit](notes/native-cone-property-audit.md)) | `Crux`, `crux_excludes` in the fourteenth paper's library |
| **D10** | *Symmetric two-sided whole rows*: recover columns from helper rows and rows from helper columns | Equivalent common-deficit target: translated intersections lose at most half the deficit; fixing heavy rows and columns permits symmetric, reflexive helper relations with arbitrarily small additional loss. Cyclic exact value d(d+1)/2+1; basis-eight46. No common deficit yet ([note](notes/two-sided-whole-row-codes.md)) | *Lean:* [finite factor-two adapter, equivalence and B1 consumers](TwoSidedCodeTransfer.lean), direct invoice δ₂>(169/32)ε. Symmetry normalization and examples: *written, reviewed* |
| **D4** | *Native extraction* of a usable coding shape from cones | Done for whole rows, including the conditional coding transfer (B1), all *Lean*. Global monotone row words are refuted (X12) | [WindowSpread.lean](WindowSpread.lean), [RowSpreadCrux.lean](RowSpreadCrux.lean) |
| **D7** | *The construction*: a code above pairing that tape passes can compute | No candidate. It must lie in "what is left" and carry a grid labelling | — |
| **D8** | *Covariant decoders on a group* (D1 for linear decoders commuting with diagonal translations) | Constant coefficients and bounded sector coupling done; coefficients depending on the sector open (G3) | `CovariantGroupHalfRate` in [StatementsWholeRow.lean](StatementsWholeRow.lean) |
| **D2** | *One-class relations* (Problem 9.4(b)): entry (c, r) from w entries (i_m(r), c + j_m(r) mod d). Relation premise, not automatic native geometry | Shared cyclic/line rules on linear sources, including arbitrary physical carry phases, are already at pairing (P17; arbitrary deterministic decoders in *Capacity and Composition*). Open: non-subspace sources or position-dependent functions; native extraction belongs to 9.4(a)/D4. [Scope audit and control](notes/row-spread-of-cones.md#31-shift-covariance-existing-bounds-and-the-native-gap) | P17 `ClassUniform.lean`, `Line.lean`; extensions `CapacityAmbient.lean`, `CapacityLineDeterministic.lean`. Native control: written proof |
| **D3** | *Classes of any shape* (Problem 9.1): two classes at most (½ + o(1))d²? | Best bound 41/64 ([Shared Decoders](../Capacity-and-Composition-of-Shared-Transposition-Decoders/)); needs a bounded-class extraction | Bounds in that paper's library |
| **D5** | *All scales at once* (Problems 9.3, 9.5): a subadditive quantity large for the swap at every scale | Open; the cut-rank profile fails on a shear ([pass calculus](notes/pass-calculus.md) §§2–3) | Not written |
| **D6** | *Relative rigidity on ball patterns* (Problem 9.6) | Open; not worked on | Not written |

## 3. Indirect fronts

| | Model problem | State | Missing tie |
|---|---|---|---|
| **I1** | *Boundedly many shared blocks* K = Σ_{a<M} A_a ⊗ B_a ([item D](D-comparison.md)) | Two blocks done, three in special shapes. Lean statements `ProblemR`, `ProblemS` ([StatementsD.lean](StatementsD.lean)) | A row shear uses d different blocks (X3) |
| **I2** | *The twisted swap* with generic blocks ([note](notes/twisted-swap.md)) | Pairing optimal for commuting W; the generic model differs from group representations (X10) | Its group form is D8 |
| **I3** | *Affine helper families over ℂ* ([pass calculus](notes/pass-calculus.md) §5) | Thresholds proved; coefficients near 1 without a parity open | Machines need finite fields or unbounded coefficients |
| **I4** | *Comparison bounds* ([item D](D-comparison.md)) | Written; a reformulation | Settles no class until Problem S is known for it |
| **I5** | *Minimal counterexamples expand* ([finite fields](notes/finite-field-expansion.md)) | Surgery reduces to expanding cores | That of I1 |

## 4. Closed fronts (append only)

| | Front | Why closed | Reopen if |
|---|---|---|---|
| **X1** | Order arguments for the half bound | Paper 17’s Proposition `expanding` gives explicit matching-plus-neighbour-expansion families whose order bound exceeds ½. The count-only conditional single-row bound is also order-dominated ([§19.1](notes/row-spread-of-cones.md#19-conditional-row-recovery-and-the-full-shannon-question)); this is not a barrier to all conditioning or Shannon proofs | A certificate beyond the order bound |
| **X2** | Traces and moments past bounded coefficients | Need a norm over ℂ; over finite fields traces do not count eigenvalues | A characteristic-free substitute for "few odd closed walks ⟹ symmetric spectrum" |
| **X3** | Bounded repertoire of blocks as the bridge to machines | A row shear has repertoire d ([pass calculus](notes/pass-calculus.md)) | A count that charges shears |
| **X4** | A stage quantity vanishing on row-controlled and on uniform stages | The swap is five such stages | — |
| **X5** | Small exhaustive searches in the array | At searchable sizes every cell is near the diagonal; 29 of 30 relations sit on the baseline | A family whose regime is set by a parameter other than d |
| **X6** | Gains from loops, polygons, witness pairs, local products, repeated seeds | Each adds O(d) | — |
| **X7** | Rate bounds for separated relations of bounded degree in general | False (papers 13, 15) | — |
| **X8** | Conditions on head motion that ignore the data | The padded machine satisfies them (paper 17, Section 4.2) | — |
| **X9** | One common-subspace compression annihilating the decoder (I2) | Certified rank at most d against a generic minimum 3d/2 ([twisted swap](notes/twisted-swap.md) §7) | Several subcodes combined |
| **X10** | Half rate by paying for one half and bounding the unpaired remainder | On quasirandom groups every half contains d/6 − o(d) disjoint product-one triples ([proof](notes/covariant-word-baselines.md)) | — |
| **X11** | Amplifying a gain by the sum of two tensor codes | The decoder contains full partial transposes: window unbounded | A product built from the two decoders alone |
| **X12** | A bounded global monotone row-word cover from bounded row spread | Block reversal is a linear-time control needing growingly many monotone pieces ([controls](notes/row-spread-controls.md)) | A correctness-dependent extraction |
| **X13** | Work-window planarity ⟹ hyperfinite helper relation | Input attachments give an expanding row graph with planar work windows ([calibration](notes/window-pages-and-input-attachments.md)); page theorem itself *Lean*, [WindowPages.lean](WindowPages.lean) | A paid separator from another source |
| **X14** | Fixing all near cells leaves at most half of the far cells free | False: Clebsch diagonal ([far cells](notes/far-cell-calibration.md)) | Charge the near cells' entropy |
| **X15** | Excess at most C·(number of cells within fixed radius), C independent of w | False: hypercube codes have excess exponential in w | A window-dependent coefficient |
| **X16** | A gain from mutual recovery inside single diagonals of a group relation | Only O_w(d/log d) diagonals are non-bipartite ([theorem](notes/diagonal-code-calibration.md)) | Subsumed by X19 |
| **X17** | Half rate for every oriented helper relation | False: Paley tournament on 7 vertices | A bound using the array structure |
| **X18** | Deleting o(d²) cells to make the mutual graph bipartite | Needs at least d²(1 − s₂)/(2 − s₂) deletions ([controls](notes/two-token-and-oriented-controls.md) §4). The separate every-basis universal zero-corner bound equals the independence number; it is not the same optimization | A decoder-specific argument |
| **X19** | A gain from mutual recovery coupling boundedly many diagonals (groups) | Proved at one half; see Section 1 | Components meeting unboundedly many diagonals; one-way helpers; non-group relations |
| **X20** | A gain from decoders with a growing twisted symmetry, an anonymous local rule, or a sparse sector profile (groups, linear, every field) | Proved at one half; see Section 1 | A balanced non-local sector profile lacking the symmetry; nonlinear rules |
| **X21** | Testing unbounded coupling on small solvable groups, or one irreducible constituent at a time | Such families are hyperfinite; bounded blocks already beat the baseline; the code uses one decoder on the whole regular representation ([controls](notes/bounded-sector-coupling.md)) | — |
| **X22** | Enlarging the balanced split/nonsplit SL₂ profile search | The single algebra pass gives common algebra dimension d²/2 and a 3/4 cap, but no mechanism for gain. The five-restriction excursion is parked, not disproved ([proof](notes/symmetry-and-locality.md) §6) | A concrete cancellation mechanism that could beat pairing |
| **X23** | Forcing window to grow by the helper-column intersection test alone | At canonical width every loopless support with both degrees ≤Δ has balanced columns passing that test with parameter 16(4Δ−1). Yet random supports in a specified bounded-degree model usually have no fixed-window presentation ([grid note](notes/grid-labellings-and-amplified-codes.md) §7) | A constraint on one common transversal row partition, or additional code structure; not another cylinder-only exclusion |
| **X24** | Bounding all core defect reuse by an absolute multiplicity | All-far doubled-cycle presentations have token degree four but forced reuse 2w; their full-grid rates tend to ½ ([row spread §24](notes/row-spread-of-cones.md#24-cores-of-supports-three-boundary-counts-and-their-limitation)). This closes the universal charge, not the higher-support capacity question | A rate-sensitive charge or another way to use overlapping squares |
| **X25** | Inclusion–exclusion budgets on row-closure intersections, including the minimum/clipping repair | The repaired rule fails recovery and submodularity on d=4, ρ(r)=[4]∖{r}, despite attainable row budgets and capacity=Sh=order=15 ([row spread §29](notes/row-spread-of-cones.md#29-the-repaired-completion-rule-fails-at-window-three)). This closes the recipe, not G4 | A different completion with a proved polymatroid/recovery theorem, or a valid universal inequality |
| **X26** | Bounded recovery degree, even with O(N) encoding circuits, forces a sparse generator after cheap linear advice | High-girth regular-graph cycle codes have arbitrarily high constant rate and bounded recovery degree, but every generator has mean support ≥g(K−t)/N after t linear reveals ([row spread §30](notes/row-spread-of-cones.md#30-sparse-recovery-and-cheap-circuits-need-not-give-sparse-generators)). No whole-row/native realization is asserted | A property of the actual grid or paid tape computation, beyond these abstract circuit conditions |
| **X27** | Unit-speed native motion supplies literal unit-shift affine covariance after cheap advice | The fixed-state adjacent-pair transducer runs in 2N+O(1) steps but needs log_q M+z≥N/2−d for such replacement in the same coordinates ([§31.3](notes/row-spread-of-cones.md#31-shift-covariance-existing-bounds-and-the-native-gap)). It is not a transposer and does commute with a two-position shift | A correctness-dependent premise or a broader paid normal form; periodic classes and nonlinear maps are not excluded |
| **X28** | A cheap shared record automatically gives E=O(B) affine rule changes | Replaying a d-bit marker in paid O(d²) tape time can force E=d²−d on its full marker fibre ([native audit §6](notes/native-cone-property-audit.md#6-finishing-the-native-entry-change-audit)). The marker alone is not a depth-reduction cut; the full fibre is not transpose-correct | A source-sensitive bound for an actual correct cheap-cut fibre, not record size alone |
| **X29** | A common deficit from counting columns that fit the best balanced Fano layout | The bound Sh≤d²−4dG/21 holds, but random fixed-forward-window hosts can have order rate arbitrarily close to one and G/d arbitrarily small in every layout as w grows ([proof](notes/paid-coarse-patterns.md)). This is a limit of this count relaxation, not a lower bound on Shannon value or capacity | Control actual conditional errors, combine different inequalities, or find a different high-order incidence identity |
| **X30** | A constant plane deficit using only row-closure equalities from pencils at o(n) centres | Make all radial cells at k centres constant and the rest independent: these equalities admit entropy ≥N−kn²(n+1). Separately every row closure adds <nd cells. This does not prove a necessary growing proof depth or exclude arbitrary Shannon certificates ([note §5a](notes/triangle-free-hosts.md)) | Additional recovery/budget identities or information from Ω(n) centres; the general plane conjecture stays open |
| **X31** | Transported whole-row closure counting as a common-deficit proof; localisation without a general capacity consumer | If the host has no empty r×r rectangle, m transported grids need a seed ≥d²−(m+1)d(r−1)+(r−1)². Random-matching symmetric/reflexive hosts make every such invoice arbitrarily close to full rate, even with arbitrary copies/permutations. This is a method bound, not a Shannon/capacity lower bound. The proposed chained-clique obstruction to paid localisation was invalid; random-decoder selection does turn small conditional error into an exact subcode, but unrestricted mutual capacity remains open ([§7](notes/two-sided-whole-row-codes.md#7-transported-recovery-its-closure-limit-and-a-localisation-consumer)) | Additional Shannon identities, or a proved native property lost when bit cones are enlarged to whole rows; localisation also needs a compatible general consumer |

## Maintenance

- Fable re-reads this file at the start of a session and before changing target; work that names no
  front is added here first or dropped. A result changes the file in the commit that publishes it.
- **Distance to the wall.** Each unit says how many restrictions separate its question from the
  statement of Section 1 (linear, mutual-only, group relation, symmetric, …). Prefer work that
  removes a restriction over work that adds an excluded sub-class. A nested excursion that has gone
  two rounds without a statement that lifts one level is stopped and recorded in Section 4.
- **Current focus** (replace, do not append). **D9, one audit unit.** B2–B4 are banked, G4 is
  parked, D10 is a normal form with its transfer in Lean, and closure-only schemes are excluded on
  mixing hosts (X31). Chosen premise (Astra's): keep the actual bit cones, before whole-row
  enlargement, and seek one coordinate transport Φ and a generating set S of the doubled cone system
  with 2B + |S| < N; `exists_indexCode` then contradicts correctness. Distance from the wall: zero.
  Unit: a proof-level audit of the existing native controls at cone level. It must name a property
  that row enlargement loses and that correctness supplies, or report that none exists. No solver,
  no new host. Fallback if nothing is named: consolidate; the reserve premise is the two-decoder
  form of the covariant linear problem on a quasirandom group (D8 with D10).
- Last re-evaluation (D0): 14 November 2026.
