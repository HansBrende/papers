# The wall: where it stands and how we are attacking it

A roadmap, kept by Claude Fable. Read it before choosing work. Last full rewrite: 13 November 2026.

**Rules of the file.**
- **Before proposing a target, a literature search or a "new" result:** read the table in the
  [series index](../README.md), the open problems of the paper that owns the object, and the
  [exclusion table](notes/conditional-machine-exclusions.md). Storage codes on graphs are papers 4, 5,
  6, 7, 13 and 15; whole rows and the swap are paper 17; shared decoders are papers 20 and 21. Six
  proposals in this effort repeated theorems of the series.
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
  ([Lean adapter](TwoSidedCodeTransfer.lean); [symmetry proof and exact
  calibrations](notes/two-sided-whole-row-codes.md)).
- Lean statements: `UniformWholeRowRateCanonicalBits`, `WholeRowHalfRateCanonicalBits` in
  [StatementsRowSpread.lean](StatementsRowSpread.lean).

**Breaches** (append only).

| | Date | What fell | Status |
|---|---|---|---|
| **B1** | 13 Nov 2026 | *Codes, machines and counting are tied.* An additional cheap cut puts all cones of almost every output row into boundedly many input rows. A common positive whole-row deficit along the canonical alphabets gives the literal native crux at every fixed depth and excludes oblivious linear-time transposers. The direct route needs a deficit only at one explicit window, exceeding 169ε/64. Before this the wall was three separate obstacles (paper 17, Section 4). | *Lean throughout:* geometry in [WindowSpread.lean](WindowSpread.lean), finite counting in [ConeCodeTransfer.lean](ConeCodeTransfer.lean), `uniformWholeRowRateCanonicalBits_crux`, `uniformWholeRowRateCanonicalBits_excludes` and `wholeRow_window_bound_excludes` in [RowSpreadCrux.lean](RowSpreadCrux.lean), reusing Paper 14. Capacity remains a hypothesis. See [row spread](notes/row-spread-of-cones.md) §§2–5. |
| **B2** | 14 Nov 2026 | *Shannon inequalities can beat every order bound.* Fano: Sh = 119/3 against order 41, for arbitrary sources and nonlinear recovery; the three-lane code attains it. One finite host. | *Lean:* paid residual/full inequalities, exact Shannon optima with polymatroid witnesses, order41, and the all-alphabet code upper bound ([status](notes/consolidation-status.md)). Actual lane-code realization and the general order/acyclic-set adapter remain written. |
| **B3** | 14 Nov 2026 | *The gap has positive density at fixed window and incidence girth Ω(log d).* Every finite strict gap amplifies by sparse incidence blow-ups with short cycles deleted. From Fano: both degrees ≤ 3600 and σ − Sh > 0.01d². These hosts already have order deficit 8/49; attainment of their upper bound is unknown. | *Written, reviewed; not Lean:* [amplification](notes/finite-shannon-gap-amplification.md), [paid recovery](notes/fano-soft-recovery.md) |
| **B4** | 14 Nov 2026 | *The gap needs no mutual triangles in the residual base.* The 9×6 grid has 39 ≤ Sh ≤ 204/5 < 41 (on its 36 non-incident cells, 21 ≤ Sh ≤ 114/5 < 23); cloning gives an 18×18 base with degrees six and no residual mutual triangles, which B3 amplifies. Exact value and capacity open. | *Lean:* paid scalar-error certificate, residual/full upper bounds, triangle-freeness and row-order optima ([status](notes/consolidation-status.md)). Lower code, joint-column price, square adapter and amplification remain written; exact capacity remains open. |

**Classes with proved deficits.** The full list, with hypotheses, status and what each class
would exclude on the machine side, is the
[conditional machine-exclusion table](notes/conditional-machine-exclusions.md) (21 rows); Lean
boundaries are in the [status index](notes/consolidation-status.md). None of the hypotheses is
supplied by B1. By mechanism, at fixed window:
- *Opposite row orders and paid pairing* (nonlinear, half): hyperfinite row relations, near-abelian
  and amenable group sources, recovery components of size o(log d), bounded sector coupling.
- *Pairing in another basis* (linear, half): group decoders with a growing twisted symmetry, a small
  common algebra or a local rule; commuting or few shared blocks. The balanced SL₂ profile gives 3/4.
- *Symmetric spectrum* (linear, half; Lean): bounded weight over ℂ and relatives.
- *Source counting* (nonlinear): two sources per coordinate give 2/3; mean support μ < 3 gives (1+μ)/4.
- *Individual pairing shifts* (nonlinear, half): invariance on all but o(d²) pairs, uniformly over
  finite abelian alphabets, with no reverse-degree bound. [Bound](notes/pairing-coset-bound.md)
  written and reviewed; abstract counting, local extension and ordinary-sum record
  separation under explicit view-cover premises now Lean; extraction/rate adapters written.
- *Subcubic coordinate support* (nonlinear, half, Lean): Paper 7 N3 already covers every
  triangle-free undirected support of degree at most three, including directed helper subsets;
  its soft memo charges each recovery error once. [Reuse adapter](SubcubicReuse.lean).
- *Sparse recovery rank* (every field): Paper 4 already covers the original scalar and directed
  reciprocity forms. The new [short proof](notes/subcubic-half-rank.md) weakens the forbidden
  pattern to a reciprocal pair of outgoing neighbours and proves rank≥⌈N/k⌉ at outgoing width
  k≥2. The three-helper half extension under that weaker pattern, its root-degree refinement,
  and all affine-code cardinality wrappers are now Lean too. Paper 10 S* already covers
  nonlinear recovery under the stronger no-transitive-triangle premise. Matching plus one
  loopless helper has a separate nonlinear half-size seed proof, now Lean, including partial
  matchings, odd size and the attained-range cost of a varying boundary record.
- *Gadgets* (constructions, not upper bounds): loops, polygons, cliques, hypercube codes; excess O_w(d).

**What the proofs share.** Most charge one member of a paired block to the other, in the cells or
after a change of basis; spectral proofs bound eigenvalue counts; source proofs eliminate paired
coordinates. For every code 2H = ΣH(row) + ΣH(row | rest) + S, with S the net synergy of the rows
([row spread](notes/row-spread-of-cones.md) §18); a fixed gain above one half needs S = Ω(N), and
in every known code S is O_w(db). The Shannon certificates (B2–B4) add submodularity across
intersections of recovery closures, and survive block aggregation and sparse mixing.
The sparse-recovery rank proof instead uses the last independent row: two fresh columns would
force a forbidden directed triangle. It is not a new closure-combination argument.

**What is left.** A fixed gain above one half at fixed window needs:
1. a row relation that is not hyperfinite, with recovery not confined to components of size
   o(log d); a small deficit forces expansion at linear scale (*Lean*:
   `wholeRow_rectangle_deficit`, [StatementsRowSpread.lean](StatementsRowSpread.lean));
2. for mutual recovery on group relations: components meeting unboundedly many diagonals;
3. for linear group decoders: no growing twisted symmetry, small common algebra or local rule;
4. over abelian alphabets, missing individual shifts on a positive fraction of pairs for every
   candidate pairing involution whose fixed-cell shifts are retained; a large abstract intersection
   with a pairing space is not the invariance premise.

For **rates approaching one**, independent-source encoders of bounded support are limited: two
sources per coordinate give rate at most 2/3, mean support μ < 3 gives (1+μ)/4, nonlinear encoders
included. This says nothing about correlated native fibres or about sparse recovery (X26).

**What cannot work, and what can.** Combining displayed recovery rules with unit coordinate
prices and additive message bills, including transported copies, cannot improve the original
acyclic bound and gives no common deficit on mixing hosts (X31). What remains outside this barrier:
(i) entropy identities beyond closure, as in B2–B4, on a family where order fails; (ii) an acyclic
certificate supplied by native geometry at the level of bit cones; (iii) a joint message for
several runs that is shorter than the sum of the separate ones; (iv) a correctness-dependent
extraction of a source or decoder class with an algebraic/source-counting bound from the table.
This is a list of logical openings, not proved premises or newly opened fronts.

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
  inequality is known (X30), and counting good columns of a Fano layout cannot be uniform in w
  (X29). The [quadrangle grid code](notes/quadrangle-grid-control.md) raises GQ(2,2)'s residual
  lower bound to105 (order118) and refutes c_Sh=2 by c_ent≥12/5. Upper-bound search parked until a named family
  comes with a precise inequality.
  For classical Q(4,s), the [reviewed grid-family construction](notes/triangle-free-hosts.md#7-grid-lanes-on-every-classical-parabolic-quadrangle)
  gives c_ent≥2+2/(2s+1); convergence of c_Sh to2 remains conjectural.
  The constructive alternative is also open: one fixed w and arbitrarily large d with a
  feasible **full-cell** polymatroid of value at least (1/2+c)d² for fixed c>0. Sparse
  amplification supplies no such lower witness. A witness would block Shannon half, not
  every common deficit; witnesses approaching rate one require w chosen before d grows.
  A proof of nonexistence at every fixed w would give a stronger Shannon-half theorem sufficient
  for the actual-code question. Code normalization does not automatically normalize
  arbitrary polymatroids.
- **The general bound, and the first open window.** Paper 17's general order bound gives
  R(w)≤w/(w+1); at windows one and two the sharper bound is asymptotically one half.
  **Window three is the smallest open case: 1/2≤R(3)≤3/4.** The series establishes no
  sharper unrestricted bound. A concrete unresolved subclass consists of cubic incidence
  **expander families with girth tending to infinity**. Girth above 8 excludes residual
  (nonincident) mutual triangles and literal line grids; it does not imply mixing or
  non-hyperfiniteness. No known construction has a positive asymptotic gain above pairing
  on this subclass. The closure-invoice barriers apply, but they do not bound full Shannon
  methods. A better upper bound here would be a subclass result; a positive-density code
  would improve the global lower bound. Settling window three alone would not settle the
  common-deficit question over all fixed windows.

**Calibration** ([host audit](notes/whole-row-host-audit.md)). Exact values on full hosts: Fano
Shannon119/3 (attained on cube-sized alphabets; scalar-linear39 over F₂ and F₃; order41);
basis d=8,w=3:46 for all alphabets. One-sided cyclic w=2: d(d+3)/2−1 for d≥2; two-sided:
d(d+1)/2+1. Grid:39≤capacity exponent≤Sh≤204/5 on54 cells (pairing36, order41).
No known code family has a fixed-window gain above one half beyond O(d).
GQ(2,2): residual105≤capacity≤Sh≤118, full150≤capacity≤Sh≤163;
the lower bounds use two lanes. These are finite bounds, not exact values.

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
| **D10** | *Symmetric two-sided whole rows*: recover columns from helper rows and rows from helper columns | Equivalent common-deficit target: translated intersections lose at most half the deficit; fixing heavy rows and columns permits symmetric, reflexive helper relations with arbitrarily small additional loss. Cyclic exact value d(d+1)/2+1; basis-eight46. No common deficit yet ([note](notes/two-sided-whole-row-codes.md)) | *Lean:* [finite factor-two adapter, equivalence and B1 consumers](TwoSidedCodeTransfer.lean), direct invoice δ₂>(169/32)ε. Same-rate symmetric/reflexive normalization and its native consumers: *Lean*, [NormalizedRateTransfer](NormalizedRateTransfer.lean). Examples: *written, reviewed* |
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

One line per closed front, so that work is not repeated. Reasons and reopening conditions are in
[closed-fronts.md](closed-fronts.md); a new closed front gets a full row there and a line here.

- **X1** Order arguments for the half bound
- **X2** Traces and moments past bounded coefficients
- **X3** Bounded repertoire of blocks as the bridge to machines
- **X4** A stage quantity vanishing on row-controlled and on uniform stages
- **X5** Small exhaustive searches in the array
- **X6** Gains from loops, polygons, witness pairs, local products, repeated seeds
- **X7** Rate bounds for separated relations of bounded degree in general
- **X8** Conditions on head motion that ignore the data
- **X9** One common-subspace compression annihilating the decoder (I2)
- **X10** Half rate by paying for one half and bounding the unpaired remainder
- **X11** Amplifying a gain by the sum of two tensor codes
- **X12** A bounded global monotone row-word cover from bounded row spread
- **X13** Work-window planarity ⟹ hyperfinite helper relation
- **X14** Fixing all near cells leaves at most half of the far cells free
- **X15** Excess at most C·(number of cells within fixed radius), C independent of w
- **X16** A gain from mutual recovery inside single diagonals of a group relation
- **X17** Half rate for every oriented helper relation
- **X18** Deleting o(d²) cells to make the mutual graph bipartite
- **X19** A gain from mutual recovery coupling boundedly many diagonals (groups)
- **X20** A gain from decoders with a growing twisted symmetry, an anonymous local rule, or a sparse sector profile (groups, linear, every field)
- **X21** Testing unbounded coupling on small solvable groups, or one irreducible constituent at a time
- **X22** Enlarging the balanced split/nonsplit SL₂ profile search
- **X23** Forcing window to grow by the helper-column intersection test alone
- **X24** Bounding all core defect reuse by an absolute multiplicity
- **X25** Inclusion–exclusion budgets on row-closure intersections, including the minimum/clipping repair
- **X26** Bounded recovery degree, even with O(N) encoding circuits, forces a sparse generator after cheap linear advice
- **X27** Unit-speed native motion supplies literal unit-shift affine covariance after cheap advice
- **X28** A cheap shared record automatically gives E=O(B) affine rule changes
- **X29** A common deficit from counting columns that fit the best balanced Fano layout
- **X30** A constant plane deficit using only row-closure equalities from pencils at o(n) centres
- **X31** Transported closure with additive message bills as a stronger coding bound
- **X32** Bounded Delsarte and translation-invariant rank experiments stopped without a scalable certificate; no all-q or growing-host barrier proved

## Maintenance

- Fable re-reads this file at the start of a session and before changing target; work that names no
  front is added here first or dropped. A result changes the file in the commit that publishes it.
- **Distance to the wall.** Each unit says how many restrictions separate its question from the
  statement of Section 1 (linear, mutual-only, group relation, symmetric, …). Prefer work that
  removes a restriction over work that adds an excluded sub-class. A nested excursion that has gone
  two rounds without a statement that lifts one level is stopped and recorded in Section 4.
- **Work queue** (replace, do not append; the channel is never idle: each agent always has one
  named unit in progress, reports when it ends, and takes the next; whoever empties the queue
  proposes its refill). Banked: B1, the finite B2/B4 cores, the normal form and barriers (Lean);
  B3 (written).
  1. *Done (Astra, reviewed).* [Pairing and parity-block extensions](notes/pairing-coset-bound.md):
     repaired incident exceptions; one-symbol price per omitted pair/block; pairing rate
     ≤1/2+b/d²+O_w(d^(-1/2)) without reverse-degree assumptions. Triangle lanes have the analogous
     relative-template bound. Written, not Lean; no arbitrary-code or native extraction claim.
  2. *Reuse audit complete.* [Literature/correction](notes/storage-codes-large-girth-literature.md):
     original A is Paper 4 Theorem S; full weighted nonlinear B is Paper 7 N3; the soft memo
     already gives coefficient-one errors. Petersen and five-cycle certificates also already
     exist. The proposed new LPs were stopped before a solve. No original A/B target remains.
  3. *Banked.* [SparseRankBounds](../lean-machine/LeanMachine/SparseRankBounds.lean) proves the
     full four-arc/outgoing-width rank bound, reusing the exact ordered count, rooted traversal,
     closed-cut inequality and last-row lemma. [ThreeHelperRank](../lean-machine/LeanMachine/ThreeHelperRank.lean)
     proves the half extension with the one-way-head premise; [SparseAffineCodes](../lean-machine/LeanMachine/SparseAffineCodes.lean)
     supplies the finite-alphabet affine consumers. Both rank proofs share one hereditary-cut
     induction. [SubcubicReuse](SubcubicReuse.lean) exposes the existing nonlinear/soft theorem
     for asymmetric helper subsets. No native extraction follows.
  4. *Comparison closed without a new rule.* Literal Paper 7 half-rate decompositions are
     impossible on Fano and the grid, whose residual codes exceed half. The checked extensions
     are paid conditional patches and balanced macro quotients; these are not a proved exhaustive
     list. A fixed base with positive order deficit cannot yield order rate tending to one by
     a balanced helper-containment lift. The good-column counting barrier does not rule out
     stronger bounds using the actual conditional errors. No new experiment is commissioned.
  5. *G0 reading complete.* Paper 15 leaves arbitrary mixed tower layouts open. The two-sided
     symmetric normal forms add no literal premise on the original tower; their output could
     still be obstructed by a future capacity theorem. Pairing-shift invariance is an exclusion
     premise. *Constructive G4 pass closed without a witness:* the
     [ordered-information refinement](notes/row-spread-of-cones.md#19-conditional-row-recovery-and-the-full-shannon-question)
     is written and reviewed, but gives no new capacity bound. The order-minus-correction
     form is valid; a low-rate directed-cycle control defeats universal positive coupling
     even without active mutual helpers, leaving high-rate/large-girth variants open.
     *Astra banked:* the nonlinear matching theorem and ordinary-sum record separation/count
     under explicit compatibility are Lean; extraction, weighted global and rate adapters remain.
  6. *Background.* B3 and the quadrangle formalizations remain written todos pending a reuse/effort
     estimate. The quadrangle estimate was dropped: a further finite bound has no named
     consumer beyond the existing triangle-free gap. No larger search is commissioned.
  7. *Stopped (X32), finite evidence only.* [Spectral tests](notes/array-free-forms-and-spectral-test.md):
     eight small LP cases replay numerically; the binary-pentagon translation-rank minimum 8
     and capacity 5 replay exactly. No all-q formula, bounded-factor limit or joint growing-host
     claim is proved. The programme is never worse than order and saves whole symbols where
     order does. *Next:* Astra, compatibility extraction for the parity adapter. Fable, D0 with
     the ordered-coupling control; no additional numerical search is commissioned.
- Last re-evaluation (D0): 14 November 2026.
