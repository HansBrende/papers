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

**The wall today is one statement about codes.** A *whole-row code* at window w is a set of d × d
arrays in which column r is a (possibly nonlinear) function of the rows ρ(r), |ρ(r)| ≤ w.
Let R(w) be its best rate for large d, over the alphabets {0,1}^{b(d)}.

> **Is sup_w R(w) < 1?** Equivalently: is there one δ > 0 with every whole-row code at every fixed
> window having at most (1 − δ)d² symbols?

- Known: ½ ≤ R(w) ≤ w/(w+1). Symmetric matrices give ½ (*pairing*). Conjectured: R(w) = ½.
- **Yes** excludes oblivious linear-time transposers (breach B1). A deficit δ(w) that falls more
  slowly than every power of 1/log log w would also do (estimate from B1 and the fourteenth paper's
  depth bound, unreviewed). The known deficit is 1/(w+1).
- **No** is what a machine needs: it must contain such codes of rate tending to 1 (front D7).
- Lean statements: `UniformWholeRowRateCanonicalBits`, `WholeRowHalfRateCanonicalBits` in
  [StatementsRowSpread.lean](StatementsRowSpread.lean).

**Breaches** (append only).

| | Date | What fell | Status |
|---|---|---|---|
| **B1** | 13 Nov 2026 | *Codes, machines and counting are tied.* For any oblivious linear-time machine, a further cut of cost εL leaves, in all but εd output rows, every cone inside w = w(k, C, ε, D) input rows. Hence a common positive whole-row deficit gives the native crux (D9) at every fixed depth, and with it the exclusion. Before this the wall was three separate obstacles (paper 17, Section 4). | Geometry: *Lean*, `native_row_spread_prefix` in [WindowSpread.lean](WindowSpread.lean). Coding transfer: *written, reviewed* ([row spread](notes/row-spread-of-cones.md) §§2–4); wants Lean. Crux ⟹ exclusion: [fourteenth paper](../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/), Corollary 9.3. |

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
| Gadgets | Loops, polygons, witness pairs, cliques, diagonal and hypercube codes: excess O_w(d), exponential in w | any | *written*: [diagonal codes](notes/diagonal-code-calibration.md); Clebsch far gadget *Lean*, [FarClebsch.lean](FarClebsch.lean) |

**What the proofs share.** Each finds a splitting of almost all coordinates into two halves that
the decoder exchanges, so the half that is read determines the half that is written: in the cells
themselves, in Fourier or eigen-coordinates, or in the spectrum (few odd closed walks).

**What is left.** A code above one half at fixed window must have all of the following, each
forced by a row above:
1. a row relation that is not hyperfinite; for a small deficit it expands at linear scale
   (*Lean*: `wholeRow_rectangle_deficit`, [StatementsRowSpread.lean](StatementsRowSpread.lean));
2. a positive fraction of its cells in large coupled recovery components (mutual part);
3. no large two-sided symmetry and no local rule (linear part);
4. recovery that is nonlinear, or linear over a finite field, or over ℂ with unbounded coefficients.

Nothing is known in that region at fixed window, in either direction. More symmetric classes will
not fill it: for free coefficients a splitting in any basis certifies exactly the independence
number of the support graph ([symmetry and locality](notes/symmetry-and-locality.md)). The gaps, nearest the wall first:
- **G1. Nonlinear forms.** The basis and spectral pairings are proved for linear codes only; a
  machine's code is not linear. Wanted: an entropy version.
- **G2. One-way helpers without symmetry.** Only order bounds apply. Oriented gadgets exist (Paley
  tournament, 4 of 7, *Lean* [PaleyTournament.lean](PaleyTournament.lean); a trace family with half a
  symbol of excess per diagonal at window log d), none at positive density.
- **G3. Large components with non-local coefficients.** Test family: SL₂(F_p) with T = {1, A, B}
  ([row spread](notes/row-spread-of-cones.md) §14, with the success criterion). What survives
  there: a finite-field profile of the sector that is balanced and lacks the symmetry (split
  against non-split), one shared decoder on the full array
  ([audit](notes/symmetry-and-locality.md)). Linear and group-bound: two restrictions from the wall.
- **The general bound.** Any improvement of the deficit 1/(w+1) for all whole-row codes is progress
  on the wall itself.

**What a proof and a machine must each respect.**
- A proof must cover nonlinear recovery and growing alphabets; fail at growing windows (simplex and
  random clique codes reach rate 1 − 1/m at window about d^{(m−2)/(m−1)}:
  [calibration](notes/simplex-code-calibration.md)); fail for abstract relations of bounded degree
  (rates above ½: [paper 13](../Storage-Codes-above-Half-Rate-under-Paired-Distance-Separation/),
  [paper 15](../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/)); and so use the
  row-and-column structure of the array.
- A machine cannot avoid curved head motion, expanding relations, and codes that are neither
  bounded gadgets nor linear with bounded complex coefficients (paper 17, Section 4.5). Its code
  needs a [grid labelling](notes/row-spread-of-cones.md) (§8) and a computation by passes.

## 2. Direct fronts

| | Target | State | Lean statement |
|---|---|---|---|
| **D0** | *Standing*: brainstorm a new front, re-evaluate the wall, or tie an indirect front to it | Permanent | — |
| **D1** | *Whole rows* (paper 17, Problem 9.4(c)): the statement of Section 1 | Open for w ≥ 3. Main front; see "what is left" | [StatementsRowSpread.lean](StatementsRowSpread.lean); linear form `LinearWholeRowHalfRate` in [StatementsWholeRow.lean](StatementsWholeRow.lean) |
| **D9** | *The native crux*: index codes for the cone systems of oblivious linear-time schedules need (ρ(D) − o(1))L bits, with ρ(D_ε) > ε for one ε | Open; follows from D1 by B1. Restricted native bounds only ([audit](notes/native-cone-property-audit.md)) | `Crux`, `crux_excludes` in the fourteenth paper's library |
| **D4** | *Native extraction* of a usable coding shape from cones | Done for whole rows (B1). Left: Lean for the coding transfer. Global monotone row words are refuted (X12) | [WindowSpread.lean](WindowSpread.lean) |
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
| **X18** | Deleting o(d²) cells to make the mutual graph bipartite | Needs at least d²(1 − s₂)/(2 − s₂) deletions ([controls](notes/two-token-and-oriented-controls.md) §4); the same in every basis (14.5) | A decoder-specific argument |
| **X19** | A gain from mutual recovery coupling boundedly many diagonals (groups) | Proved at one half; see Section 1 | Components meeting unboundedly many diagonals; one-way helpers; non-group relations |
| **X20** | A gain from decoders with a growing twisted symmetry, an anonymous local rule, or a sparse sector profile (groups, linear, every field) | Proved at one half; see Section 1 | A balanced non-local sector profile lacking the symmetry; nonlinear rules |
| **X21** | Testing unbounded coupling on small solvable groups, or one irreducible constituent at a time | Such families are hyperfinite; bounded blocks already beat the baseline; the code uses one decoder on the whole regular representation ([controls](notes/bounded-sector-coupling.md)) | — |

## Maintenance

- Fable re-reads this file at the start of a session and before changing target; work that names no
  front is added here first or dropped. A result changes the file in the commit that publishes it.
- **Distance to the wall.** Each unit says how many restrictions separate its question from the
  statement of Section 1 (linear, mutual-only, group relation, symmetric, …). Prefer work that
  removes a restriction over work that adds an excluded sub-class. A nested excursion that has gone
  two rounds without a statement that lifts one level is stopped and recorded in Section 4.
- **Current focus** (replace, do not append). G1: an entropy form of the swapped-blocks bound
  (Fable). G3: the balanced finite-field sector profiles on SL₂(F_p) that the audit leaves
  (Astra); no search before a mechanism is named. Lean wanted: the coding transfer of B1.
- Last re-evaluation (D0): 13 November 2026.
