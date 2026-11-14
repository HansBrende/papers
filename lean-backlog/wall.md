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
  k/d²; in general, (log of the number of arrays in C) / (number of bits in an array).
- **R(w).** The best rate at window w when d is large: the largest rate over all choices of ρ
  and C, in the limit of growing d.
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
- **No** is what a machine needs: it must contain such codes of rate tending to 1 (front D7).
- Lean statements: `UniformWholeRowRateCanonicalBits`, `WholeRowHalfRateCanonicalBits` in
  [StatementsRowSpread.lean](StatementsRowSpread.lean).

**Breaches** (append only).

| | Date | What fell | Status |
|---|---|---|---|
| **B1** | 13 Nov 2026 | *Codes, machines and counting are tied.* An additional cheap cut puts all cones of almost every output row into boundedly many input rows. A common positive whole-row deficit along the canonical alphabets gives the literal native crux at every fixed depth and excludes oblivious linear-time transposers. The direct route needs a deficit only at one explicit window, exceeding 169ε/64. Before this the wall was three separate obstacles (paper 17, Section 4). | *Lean throughout:* geometry in [WindowSpread.lean](WindowSpread.lean), finite counting in [ConeCodeTransfer.lean](ConeCodeTransfer.lean), `uniformWholeRowRateCanonicalBits_crux`, `uniformWholeRowRateCanonicalBits_excludes` and `wholeRow_window_bound_excludes` in [RowSpreadCrux.lean](RowSpreadCrux.lean), reusing Paper 14. Capacity remains a hypothesis. See [row spread](notes/row-spread-of-cones.md) §§2–5. |

**Classes proved at one half** (rate ½ + o(1), or excess O(d), at fixed window).

| Mechanism | Class | Scope | Status |
|---|---|---|---|
| Pairing of cells after a small payment | Row relation hyperfinite: o(d) row vertices deleted, pieces of size o(d). Covers groups with commuting probability bounded below, and marked quotients of one amenable group | nonlinear, one-way helpers | *written, reviewed*: [separator bound](notes/window-pages-and-input-attachments.md), [near-abelian groups](notes/bounded-sector-coupling.md), [amenable sources](notes/symmetry-and-locality.md) |
| | Recovery components of size o(log d); products of local codes | nonlinear | *written*: [grid bound](notes/grid-labellings-and-amplified-codes.md) |
| | Group relations, mutual recovery whose components each meet at most m diagonals (*sectors*): d²/2 + O(d²/log d) | nonlinear, mutual only | *written, reviewed*: [bounded-sector coupling](notes/bounded-sector-coupling.md); identities *Lean*, [SectorWalks.lean](SectorWalks.lean) |
| Pairing in another basis | Group relations: coefficients invariant under any growing twisted-symmetry subgroup, or with a common factor algebra of dimension o(d²); anonymous local rules on any growing group family; sparse Bruhat profiles on SL₂(F_p) | linear, every field, one-way helpers | *written, reviewed*: [symmetry and locality](notes/symmetry-and-locality.md); first form in [row spread](notes/row-spread-of-cones.md) §14 |
| | Commuting blocks; two shared blocks (every field); three shared blocks of special shape; one repeated seed | linear | *written*: [twisted swap](notes/twisted-swap.md) §7, [two-term](notes/two-term-equality.md), [assemblies](notes/three-term-seed-assemblies.md), [identity lifts](notes/identity-lift-comparison.md) |
| Symmetric spectrum | Bounded weight Σ‖A‖‖B‖ over ℂ; contracting recovery; a sign symmetry (every field of characteristic ≠ 2); small coefficients; helper maps with a parity | linear | *Lean*: [A](A-bounded-weight.md), [B](B-recovery-matrix.md); *written*: [pass calculus](notes/pass-calculus.md) §5 |
| Rank count | Decoder blocks invertible or zero (second rule) | linear | *Lean*: [C](C-second-rule.md) |
| Gadgets | Loops, polygons, witness pairs, cliques and the displayed diagonal/hypercube constructions: excess O_w(d), exponential in w | any | *written*: [diagonal codes](notes/diagonal-code-calibration.md); Clebsch far gadget *Lean*, [FarClebsch.lean](FarClebsch.lean) |

**What the proofs share.** Many charge one member of a paired block to the other, in coordinates
or after a basis change. Spectral proofs instead bound eigenvalue counts; they need not exhibit
two coordinate halves exchanged by the decoder. This is a guide to the mechanisms, not an
equivalence of them.

**What is left.** For a fixed positive asymptotic gain above half at fixed window:
1. the row-graph family cannot be hyperfinite, and recovery cannot decompose entirely into
   coordinate components of size o(log d). A small deficit also forces expansion at linear
   scale (*Lean*: `wholeRow_rectangle_deficit`, [StatementsRowSpread.lean](StatementsRowSpread.lean));
2. within **group relations with mutual recovery**, bounded-sector components cannot supply the
   gain. Large coupling or a different recovery class is needed;
3. within **linear group decoders**, growing twisted symmetry, small common algebras and the
   specified anonymous local rules are excluded;
4. within **bounded-degree locally bipartite supports**, bounded complex coefficients cannot
   supply it. This does not exclude every complex whole-row decoder with one-way helpers.

The unrestricted capacity question remains open. For free support coefficients the universal
zero-corner projection bound is exactly the independence number, in every basis
([symmetry and locality](notes/symmetry-and-locality.md)); this does not rule out all future
symmetry or decoder-specific arguments. The gaps, nearest the wall first:
- **G0. Is sup_w R(w) = 1 already?** Paper 15's full field kernels have rate at least
  1 − e^{−λm}; its binary fibres have rate at least 1 − (log₂q)e^{−λm}, with fixed seed field q.
  Presentability of the growing coupled family at a window depending only on m remains open.
  The displayed support fails column labels omitting any tensor factor at canonical width;
  the full field kernel fails every decoder on tensor-cylinder columns. Arbitrary mixed
  partitions and alternative binary-fibre decoders survive. For every partition, a mutual
  support must be locally bipartite at almost all vertices ([row spread](notes/row-spread-of-cones.md)
  §16); for the tower this is consistent, not an exclusion. A positive result needs the
  dimension/lane adapter in the [grid note](notes/grid-labellings-and-amplified-codes.md) §6.
  It would refute a common positive deficit, not every window-dependent or native exclusion.
  A negative result for this one tower matters insofar as its mechanism generalizes.
- **G1. Nonlinear forms.** The basis and spectral pairings are proved for linear codes only; a
  machine's code need not be linear. Wanted: an entropy version.
- **G2. One-way helpers without symmetry.** No common deficit is known. Oriented gadgets exist (Paley
  tournament, 4 of 7, *Lean* [PaleyTournament.lean](PaleyTournament.lean); a trace family with half a
  symbol of excess per diagonal at window log d), none at positive density.
- **G3. Large components with non-local coefficients.** The SL₂(F_p) balanced mutual profile
  has common factor algebra End_Z(F[G]) of dimension d²/2 and a 3/4 cap over every field
  ([audit](notes/symmetry-and-locality.md) §6). No gain was found or proved. This profile adds
  five restrictions (group, linear, mutual, one family, one profile); it is parked (X22).
- **The general bound.** Any improvement of the deficit 1/(w+1) for all whole-row codes is progress
  on the wall itself.

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
| **D4** | *Native extraction* of a usable coding shape from cones | Done for whole rows, including the conditional coding transfer (B1), all *Lean*. Global monotone row words are refuted (X12) | [WindowSpread.lean](WindowSpread.lean), [RowSpreadCrux.lean](RowSpreadCrux.lean) |
| **D7** | *The construction*: a code above pairing that tape passes can compute | No candidate. It must lie in "what is left" and carry a grid labelling | — |
| **D8** | *Covariant decoders on a group* (D1 for linear decoders commuting with diagonal translations) | Constant coefficients and bounded sector coupling done; coefficients depending on the sector open (G3) | `CovariantGroupHalfRate` in [StatementsWholeRow.lean](StatementsWholeRow.lean) |
| **D2** | *One-class relations* (Problem 9.4(b)): entry (c, r) from w entries (i_m(r), c + j_m(r)) | Open for window ≥ 3; not worked on | Not written |
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
| **X1** | Order arguments (row orders, flags, acyclic sets) for the half bound | On expanding relations the acyclic bound stays a constant above ½ (paper 17, Problem 9.4(c)) | A stronger certificate than one flag |
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

## Maintenance

- Fable re-reads this file at the start of a session and before changing target; work that names no
  front is added here first or dropped. A result changes the file in the commit that publishes it.
- **Distance to the wall.** Each unit says how many restrictions separate its question from the
  statement of Section 1 (linear, mutual-only, group relation, symmetric, …). Prefer work that
  removes a restriction over work that adds an excluded sub-class. A nested excursion that has gone
  two rounds without a statement that lifts one level is stopped and recorded in Section 4.
- **Current focus** (replace, do not append). G0: genuinely mixed column partitions for the
  growing tower (Astra). Two restrictions: this code family and its fixed coordinates; a
  displayed-support argument has the extra decoder restriction. Use the shortened-column
  gate or exact support intersections before any search. Fable: the dual linear form of D1,
  [row spread](notes/row-spread-of-cones.md) §15.2 (one restriction: linearity). B1's conditional
  transfer is complete in Lean. G3 is parked after its one algebra pass.
- Last re-evaluation (D0): 14 November 2026.
