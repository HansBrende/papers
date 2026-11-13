# The wall: where it stands and how we are attacking it

A roadmap, kept by Claude Fable. It is the first file to read before choosing work and the file to
update when a result lands. Last full review: 13 November 2026.

**Rules of the file.**
- Section 1 states the wall as it is *today*. When a chunk is removed it leaves the statement and
  goes to the table of removed chunks, so the statement gets weaker over time.
- A front is **direct** if its target is a statement about the machines (Section 2a), or a stated
  problem of paper 17 in its one-hop model (Section 2b, where the link to the machines is proved
  only as far as that section says). Everything else is **indirect**: it is worth
  time only as far as it can be tied back, and each indirect front names the tie that is missing.
- Front names (D1, I2, X3, …) are permanent. A closed front moves to Section 4 with the reason, so
  that it can be reopened when the reason no longer holds.
- Status words: *Lean* (kernel-checked), *written* (proof in the linked file), *numerical*,
  *conjecture*. A conjecture on a direct front should get a Lean statement; where none exists
  the entry says so.

Paper 17 is [Order, Symmetry and the Swap](../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/)
(Sections 4 and 9 for the diagnosis and the open problems).

## 1. The wall

**The objective.** Decide (T): is there a multitape Turing machine that transposes a d × d matrix
of logarithmic-size entries in linear time? We hope for the machine.

**Machine form** (paper 17, Section 4). For oblivious machines everything known reduces (T) to one
function. Let r(ε) be the best rate, for large d, of a storage code on the relations that are left
when a genie reveals εL bits of a linear-time schedule.
- A linear-time oblivious transposer needs r(ε) ≥ 1 − ε for every ε.
- Pairing gives r(ε) ≥ ½.
- **Nothing moves r(ε) off ½ in either direction, for all schedules.** That is the wall.
- To exclude oblivious machines it is enough that r(ε) < 1 − ε for one ε. The cones that the
  genie leaves have depth D(k, ε) with log log D = O(k² log(k/ε)) (paper 17, Section 3.3). So what
  is needed is a rate bound 1 − δ on cone relations whose δ falls, as the cones grow, more slowly
  than that function allows; any δ that does not depend on the size of the cones would do. One
  half is the conjectured truth, not the requirement. The exact statement is front D9; the rate
  needed was worked out in the fourteenth paper (remark on the rate needed), not here.

A proof that no machine exists must cover every hypothetical correct machine and its relevant traces,
fail for unrestricted abstract relations (codes of
rate near 1 exist there), fail for motion that ignores the data (padding), constrain all address
scales at once, and use the shape of tapes. A machine, for its part, cannot avoid curved head
motion, expanding relations, and codes that are neither gadgets of bounded size nor linear with
bounded complex coefficients (paper 17, Section 4.5). For adaptive machines the same question sits on the machine's
own runs ([Macroscopic Information Transfer](../Macroscopic-Information-Transfer-in-Adaptive-Tape-Transposition/)).

**One-hop form** (paper 17, Sections 5 to 7; D1 now has a reviewed written native tie). A d × d matrix X; a decoder
computes each entry of Xᵀ from a bounded window of X; the *code* is the set of X it transposes.
Symmetric matrices give rate ½ (the *pairing value* d(d+1)/2).

> **Is there a code of rate ½ + δ at a bounded window w ≥ 3, or is every such code at most
> (½ + o(1)) d²?**

Known in general: window ≤ 2 gives at most d(d+1)/2 + d − 1; window w gives at most w d(d+1)/(w+1).

For fixed w≥1, write R_can(w) for the limsup as d grows of the maximal nonlinear whole-row
code rate at window w and canonical alphabet {0,1}^{b(d)}. Then ½ ≤ R_can(w) ≤ w/(w+1).
The reviewed written [row-spread bridge](notes/row-spread-of-cones.md) now shows that
sup_w R_can(w) < 1 would exclude oblivious linear-time transposers. Its raw-boundary
strengthening gives the native crux at any common positive deficit for all fixed windows,
at each fixed depth. **No construction gives R_can(w) > ½ for any fixed w, and no bound stays
away from 1 as w grows.** A hypothetical machine needs sup_w R_can(w) = 1. This does not
assert such codes at a single fixed alphabet: its size grows with d, and a fixed-alphabet
theorem with uncontrolled alphabet-dependent thresholds does not suffice. The value at w = 3
remains a test case, while a common positive deficit for every fixed w is the sufficient target.

**Why it is a wall.** Each of the three kinds of argument stops for a reason that machines meet:

| Argument | Where it stops |
|---|---|
| Order (flags, acyclic sets) | stays a constant above ½ on expanding row relations, and boundedly many forward passes realise such relations |
| Traces and moments | need bounded coefficients over ℂ; nothing over finite fields |
| Symmetry (shared blocks, small algebras, interval classes) | a row shear uses d different blocks, and a shear is one linear-time pass |

**Removed since paper 17** (no longer part of the wall):

| Chunk | What is proved | Status | Where |
|---|---|---|---|
| Bounded weight over ℂ | any number of Kronecker terms with bounded Σ‖A‖‖B‖: rate ½ + o(1) | Lean | [A](A-bounded-weight.md) |
| Contracting recovery | recovery matrix of norm ≤ 1: at most half plus half its trace; with a sign symmetry (two-coloured support): at most half, every field of characteristic ≠ 2 | Lean | [B](B-recovery-matrix.md) |
| Whole rows, second rule | a bound through the ranks of the decoder's blocks; for blocks that are invertible or zero it falls below pairing-and-loops in the computed cases | Lean | [C](C-second-rule.md) |
| Two shared blocks | at most d(d+1)/2, with equality only for G ⊗ G⁻¹; every field | written | [two-term-equality](notes/two-term-equality.md) |
| Three shared blocks, special shapes | compatible assemblies: at most pairing + 3; locally unitary over ℂ, or one factor space of slow growth: at most pairing | written | [assemblies](notes/three-term-seed-assemblies.md), [product spaces](notes/involutive-product-spaces.md) |
| Repeating one seed | identity lifts of a fixed decoder exceed pairing by O(d) only | written | [identity lifts](notes/identity-lift-comparison.md) |
| Product codes on sublogarithmic blocks | any recovery rules and balanced grid labels at fixed forward window: rate at most 1/2 + o(1) when block size is o(log d), uniformly in entry width and alphabet | written, reusing Paper 5 Lemma 4.1 | [grid bound](notes/grid-labellings-and-amplified-codes.md) |
| Helper maps with a parity | affine helper families on which a sign character is −1: half bound over ℂ, bounded coefficients | written | [pass-calculus §5](notes/pass-calculus.md) |
| Small coefficients | rate zero below one threshold, at most ½ below a second, for any helper family over ℂ | written | [pass-calculus §5.1](notes/pass-calculus.md), [shear bound](notes/shear-small-coefficient-bound.md) |
| Loops | the baseline is pairing plus loops; 29 of 30 small relations sit exactly on it | exact computation | [loop controls](notes/shear-loop-controls.md) |

**Shifts** (the wall moved, nothing was removed):
- *Bounded repertoire does not reach machines.* The swap is five stages of two cheap kinds, and one
  of them (a row shear) uses d different blocks ([pass-calculus §§1–4](notes/pass-calculus.md)).
  So every "shared blocks" result above bounds a slice that a machine can leave.
- *Sector baselines on groups* include short relations among the generators, not only pairing and
  loops ([twisted-swap-controls](notes/twisted-swap-controls.md)).
- *Distant sector gains need not help the array.* Helper-relative loops can beat an exact scalar-monomial
  baseline arbitrarily far from the helpers, yet the same patch gives zero regular-representation gain.
  The next D8 test must keep one common decoder across sectors ([closed-word controls](notes/covariant-word-baselines.md)).
- *Whole-row shape can be extracted from native cones.* Paper 14 pays advice and causal depth;
  the new [row-spread theorem](notes/row-spread-of-cones.md) pays a further small cut to put
  almost every output row in the whole-row model. Conditioning on the old raw cones of the
  added cuts transfers arbitrary binary storage codes too, so a common whole-row deficit
  gives the full native crux. These implications are written; the cut adapters are Lean-verified.
  No capacity bound or new machine exclusion follows without the missing whole-row deficit.
  The earlier [native comparison table](notes/native-cone-property-audit.md) remains a useful
  audit of the source theorems, but its then-missing whole-row tie is now supplied.
- *Bounded row spread does not give bounded global monotone row words.* Blockwise row reversal
  is a linear-time control whose persistent root reads require growingly many monotone pieces,
  even after o(L) coordinate exceptions ([countercontrol](notes/row-spread-controls.md)).
  It is not a transposer and does not refute a correctness-dependent extraction theorem.
- *Work-window pages do not include the raw attachments.* The corrected 2k-page quotient
  theorem is now Lean-verified. Its pages may share endpoints and are not necessarily
  `StackDag` matchings. With one work walk the work graph is planar, but a supplied-list
  geometric control has an expanding row helper graph through its input attachments.
  A row-level separator would give a half-rate bound; it is not supplied by work planarity
  alone ([calibration](notes/window-pages-and-input-attachments.md), X13).
- *Grid compatibility is an additional construction obligation.* After paying for
  exceptional columns and reverse-degree trimming, fixed-depth native fibres retain a balanced grid
  with bounded forward and reverse row windows. Ordinary right-Cayley maps preserve
  coset columns and force window d; affine-coset windows are instead governed by an
  exact subgroup index, not necessarily by exchange of subgroups ([grid audit](notes/row-spread-of-cones.md#8-grid-labellings-and-their-scope)).
  These are necessary tests, not a characterization of native codes.
- *Some high-rate abstract fibres fail every fixed window.* Slow padding of Paper 15's
  blocks to size o(log d) retains its abstract degree, separation and common-partition
  conclusions but, by the product-code bound, has no bounded-window whole-row presentation
  at rates at least 1/2 + c for fixed c>0. The original growing-block tower and its maximal-square-root
  assembly remain unresolved under arbitrary grids ([proof](notes/grid-labellings-and-amplified-codes.md)).

**The wall today.** A code above the pairing rate at bounded window, or a proof that none exists,
has to deal with all of this at once:
1. a row relation of window ≥ 3 that expands (for window ≥ 4 an order argument provably fails);
2. decoders that change from row to row beyond any bounded list of blocks;
3. over ℂ, coefficients above the thresholds and helper maps with odd relations (no parity);
   over a finite field, nothing beyond order arguments is known at any size of coefficient;
4. no pairing code inside, no product of local codes, no gadget of bounded size
   (each of these gains only O(d));
5. and, to reach machines, decoders that are compositions of one transition function on the
   cones of a schedule, not a free choice per position.

## 2. Direct fronts

### 2a. On the machines

| | Target | Tie to the machines | State | Lean statement |
|---|---|---|---|---|
| **D0** | *Standing front*: brainstorm a new front, re-evaluate the wall, or turn an indirect front into a direct one by proving its tie | Every other front came from here | Permanent. Last used 13 November 2026 (see Maintenance) | — |
| **D9** | *The native crux*: every index code for the cone systems of k-tape oblivious linear-time schedules, at cone depth D, asymptotically needs at least (ρ(D)−o(1))·L bits. Exact useful test: ρ(Dε) > ε for one ε. A sufficient envelope is ρ(D) ≥ kβC (log D)^{−c/k²}, for the small c in Remark 9.4; this is not a necessary or sharp threshold. Conjectured: ρ = ½. | Proved: it excludes oblivious linear-time transposers ([Bounded-Stack DAGs](../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/), Corollary 9.3 O(b)). Advice and many hops are already included. The asymptotic rate envelopes of Remarks 9.4–9.5 are labelled proof sketches. | Open. `SCone` itself assumes neither correctness nor a cheap genie. Correctness-dependent crossing/curvature theorems cannot be imposed on every class member. Restricted native coding bounds are known; degree and paired separation alone are insufficient. | Exists: `Crux`, `crux_excludes` in that paper's library |
| **D4** | *Native extraction*: obtain a usable coding certificate after explicitly paid losses, either for all cone systems or on a suitable correct-source fibre. | **Whole-row tie proved in writing:** an extra εL-price cut leaves all cones in all but εd output rows inside at most w input rows. This works on every trace, at every fixed full depth D. | Reviewed 13 November: d≥4, every b≥1; w = 2(M′+1)(M+2)^D, M = ⌈4k(k+1)βC/ε⌉, M′ = ⌈2C/ε⌉. A whole-row deficit δ(w)>3ε at the actual-machine width excludes those resources. For arbitrary original storage codes, price the added cuts by B_D = Σ_{j=0}^D(k+1)^j instead; a common positive deficit for all fixed w then proves D9. The known inverse-window gap is insufficient. Global monotone row-word extraction is refuted (X12). | [StatementsRowSpread.lean](StatementsRowSpread.lean): quantitative and qualitative geometric propositions, unproved in Lean; exceptional-column and raw-boundary adapters proved. [Written proof](notes/row-spread-of-cones.md). |
| **D5** | *All scales at once* (Problems 9.3, 9.5): a quantity subadditive over steps, large for the swap at every scale, not raised everywhere by one pass | Would turn "every digit must be broken" into a factor log d | Open. No such quantity vanishes on both kinds of stage; the cut-rank profile fails on a shear ([pass-calculus §§2–3](notes/pass-calculus.md)) | Not written |
| **D6** | *Relative rigidity on ball patterns* (Problem 9.6) | A positive answer excludes oblivious linear-time transposers with linear data paths | Open; not worked on | Not written |
| **D7** | *The construction*: a code above the pairing rate that tape passes can compute | It would be the machine's core | No candidate. It must have every feature of "the wall today". Sharpened 13 November ([row spread §8](notes/row-spread-of-cones.md), written, not reviewed): a native fibre is a storage code of bounded degree on a relation with a *grid labelling* of bounded window. An abstract high-rate family gives a whole-row code above pairing exactly if its relations have such labellings; labellings by cosets fail unless every arc is twisted by an automorphism exchanging the two subgroups. Whether the relations of the thirteenth and fifteenth papers can be labelled is open. | — |

### 2b. The one-hop form (paper 17's problems)

These are paper 17's model problems. D4 now supplies the whole-row shape, with paid cut and
exceptional-column losses, for arbitrary native traces. A sufficient D1 capacity theorem must
cover nonlinear recovery and the growing entry alphabet; the old scalar-linear statement is
only a restricted target. This extraction does not supply the stronger periodic-stretch or
global monotone-word shapes. Regularity along one output row and macroscopic curved motion
concern different scales (paper 17, Section 3.2). A model code still needs a paid tape
implementation before it becomes a machine construction.

| | Target | Tie to the machines | State | Lean statement |
|---|---|---|---|---|
| **D1** | *Whole rows* (paper 17, Problem 9.4(c)): each column is a possibly nonlinear function of ≤w rows. Sufficient target: a common positive deficit for every fixed w, uniformly along canonical growing alphabets; conjectured rate ½. | D4 and the raw-boundary transfer give D9 at that common deficit. No exceptional-column conjecture is needed: conditioning costs q^{d·|E|}. A construction still needs paid markings, passes and decoding; arbitrary row maps are not proved executable cheaply. A bound gives D2. | Open for w≥3. The bridge is reviewed in writing. Lean: every incidence-free rectangle has area ≤δd² for a rate≥1−δ code; the second setwise expansion condition is strengthened to all row indices. Also Lean: 2k noncrossing work-window pages after contraction. Their input attachments need not be monotone and cannot be omitted. Only the specified rectangle-credit/max-overlap aggregation is shown to lose O(1/w); no impossibility theorem for all cover methods is claimed. [Details](notes/row-spread-of-cones.md#7-expansion-and-the-corrected-page-structure). | `UniformWholeRowRateCanonicalBits`, `UniformWholeRowRate` and the half-rate variants in [StatementsRowSpread.lean](StatementsRowSpread.lean) are open propositions. The older `LinearWholeRowHalfRate` in [StatementsWholeRow.lean](StatementsWholeRow.lean) remains a restricted target, with a uniform-in-field variant. |
| **D2** | *One-class relations* (Problem 9.4(b)): entry (c, r) from the w entries (i_m(r), c + j_m(r)) | Hypothesis on head motion alone; applies to single runs of adaptive machines; gives D3 for bounded windows | Open when rows and offsets are both spread, window ≥ 3 | Not written |
| **D3** | *Classes of any shape* (Problem 9.1(a), (c)): two classes, at most (½ + o(1)) d²? | Requires an actual bounded-class extraction. Revealed bits do not automatically give boundedly many column classes; Paper 20 Proposition 9.6 defeats two naive cut-label absorptions. | Best bound 41/64 ([Shared Decoders](../Capacity-and-Composition-of-Shared-Transposition-Decoders/)); gains known are O(d) | In that paper's library (bounds); conjecture not written |
| **D8** | *Covariant decoders on a group* (slice of D1, linear): rows and columns indexed by G, relation rΣ, decoders commuting with diagonal translations; ordinary **field rank** of the group-algebra residual acting on F[G]^G ([twisted-swap §1, §9](notes/twisted-swap.md)) | It is D1 restricted to a symmetry class; blocks vary with the row and the relation expands when the Cayley graph does | Open. Ordered-support injectivity holds over every field, but a half-rate consequence needs a vanishing order-boundary fraction. Distant helper loops give sector gains, but no gain on the full regular representation ([controls](notes/covariant-word-baselines.md)). | `CovariantGroupHalfRate` in [StatementsWholeRow.lean](StatementsWholeRow.lean): open proposition for one shared κ, all characteristics; separate uniform-in-field variant. |

Current effort (13 November): the D4 audit, raw-boundary transfer and grid calibration are
recorded. Fable's main target is a D1 deficit on expanding grid-labelled relations.
Astra's audit rules out sublogarithmic product blocks and the standard contiguous
placements of Paper 15's displayed decoder at canonical entry width; it leaves arbitrary grids of growing
majority blocks open. Astra has formalized the finite interval-overwrite core, the exact
dependency-page quotient, native interval visitation, pointwise last-window-label updates
and the first-visit predecessor witness. Finite-list packing/count transport and the rest
of the geometric cut-and-row assembly remain to be formalized.
The general separator target is parked without an extraction mechanism, not refuted:
that such an extraction would prove exclusion is not an impossibility-of-method argument.
The input-attachment control includes some expanders, but does not prove that arbitrary
whole-row relations are native cone systems.
Do not assume bounded global monotone row words (X12), or transfer work planarity to the
helper graph without paying for its attachments (X13).
D8's next search must use one shared decoder and the full regular representation, but remains
parked. I1 and I2 are parked. D5 and D6 have no one on them.

## 3. Indirect fronts

Each is a model problem. The last column is what must be proved before a result here counts on a
direct front.

| | Model problem | State | Missing tie |
|---|---|---|---|
| **I1** | *Boundedly many shared blocks* K = Σ_{a<M} A_a ⊗ B_a: at most (½ + o(1)) d² for fixed M? (Problems R, S of [item D](D-comparison.md); "three blocks never exceed pairing + 3") | Two blocks done. Three: special shapes done, general open; the involutive slice is parked behind D1/D4. Lean: `ProblemR`, `ProblemS`, `problemR_of_problemS` in [StatementsD.lean](StatementsD.lean) (open). | Machines are not confined to bounded repertoire (shift above). Needs a version in which the blocks vary with the row, which is D1. |
| **I2** | *The twisted swap* ([note](notes/twisted-swap.md), [controls](notes/twisted-swap-controls.md), [unpaired scalar theorem](notes/unpaired-scalar-decoding.md)): covariant decoders; per representation, least rank of ⊕ U_g − K′ with K′ ∈ M_d ⊗ W | Generic inverse-paired U and fixed simultaneously diagonalizable W, n ≥ 2: pairing optimal (written). **(U)** asks for kernel ≤ c_w d for independent generic U, uniformly in n. At w = 1 it is proved with exact complex/algebraically closed maximum d when n ≤ 2 or n ≥ (d−1)(d−2)−1; first remaining cases d = 4, n = 3,4. Numerical w = 3 counts 13 and 20 reproduced with saved witnesses; no general square-root theorem. | (i) generic U_g → π(g); (ii) covariant → arbitrary blocks. The new large-n range misses full-group irreducible dimensions n² ≤ d. Inversion fixed points have an explicit conditional correction. No direct-front chunk removed. Lean statement of (U): not written. **Tie (i) fails by the route through (U):** for the matrices of a quasirandom group, (U) is false (every half of the group contains order-d disjoint triples abc = e, each carrying kernel n; [twisted-swap §9](notes/twisted-swap.md)). The generic results stay as mechanisms; the group model is now D8. |
| **I3** | *Affine helper families over ℂ* ([pass-calculus §5](notes/pass-calculus.md)): half bound without a parity, or a code on odd relations | Bounded-coefficient thresholds proved; coefficients near 1 without a parity open | Bounded complex coefficients are already excluded for machines (paper 17, Section 4.5): needs finite fields or unbounded coefficients |
| **I4** | *Comparison bounds* ([item D](D-comparison.md), D0–D6): D(K) ≤ d(d+1)/2 + dim ker(K + G ⊗ G⁻¹) and relatives | Written; Lean obligations open | A reformulation: settles no class until Problem S is known for it |
| **I5** | *Minimal counterexamples expand* ([finite fields](notes/finite-field-expansion.md), [involutive](notes/involutive-product-spaces.md)) | Surgery reduces to cores that expand on all four sides (involutive case; outside characteristic 2 with equality) | Only for shared blocks, so the tie is that of I1 |

## 4. Closed fronts

| | Front | Why closed | Reopen if |
|---|---|---|---|
| **X1** | Order arguments (row orders, flags, acyclic sets) for the half bound | On expanding relations the acyclic bound stays ≥ (½ + c) d² (paper 17, Problem 9.4(c) discussion). In I2 the common-subspace certificate gives d(n−⌊n/w⌋); this is not a proved ceiling for every possible flag method. A single such compression cannot prove (U) uniformly in n. | A stronger precisely defined certificate, or an additional restriction on actual schedule relations |
| **X2** | Trace and moment arguments past bounded coefficients | Need a norm bound over ℂ. Over a finite field traces do not count eigenvalues; an exact parity (two-coloured support, item B) gives the half bound, an approximate one gives nothing. | A characteristic-free substitute for "few odd closed walks ⇒ symmetric spectrum" |
| **X3** | Bounded repertoire as the bridge to machines | A row shear has repertoire d ([pass-calculus](notes/pass-calculus.md)) | A count that charges shears |
| **X4** | A stage quantity that vanishes on row-controlled and on uniform stages | The swap is five such stages, so it vanishes on the swap | — (refuted) |
| **X5** | Small exhaustive searches for a separating instance in the array itself | At the sizes that can be searched every position is near the diagonal and local gains dominate; 29 of 30 relations sit on the baseline. Silence there proves nothing. | A family whose regime is set by a parameter other than d (I2 is one) |
| **X6** | Gains from loops, polygons, witness pairs, products of local codes, repeated seeds | Each adds O(d) at bounded degrees (products: paper 17; seeds: [identity lifts](notes/identity-lift-comparison.md); polygons and witness pairs: proofs not yet in this repository) | — |
| **X7** | Rate bounds for separated relations of bounded degree in general | False: codes of rate → 1 exist ([paper 13](../Storage-Codes-above-Half-Rate-under-Paired-Distance-Separation/), [paper 15](../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/)) | — (refuted). The open part is whether such codes fit an array with bounded windows, which is D7. |
| **X8** | Conditions on head motion that do not look at the data | The padded machine satisfies them and transposes nothing (paper 17, Section 4.2) | — (refuted) |
| **X9** | A single common-subspace compression that annihilates the decoder, in I2 | At n = 3, w = 2 its certified rank is at most d, while the generic paired minimum rank is 3d/2 ([twisted-swap §7](notes/twisted-swap.md)) | Combine constraints from multiple subcodes; the two-subcode step already does this |
| **X10** | Paying for a full half and bounding the **unrestricted** unpaired remainder to prove half rate | On increasingly quasirandom groups, every maximal inverse-free half contains d/6 − o(d) disjoint product-one triples. This upper-bound expression has a (2/3 − o(1))dn floor ([proof](notes/covariant-word-baselines.md#1-distinct-site-cycles-and-a-stronger-packing-bound)). This is not an attained paired rate. | Retain compatibility with the discarded equations, charge less than the full projection dimension, or use a weaker bound if D4 permits it. A suitable ordered-support certificate is another possibility, with its boundary paid explicitly. |
| **X11** | Amplifying a small gain to rate near 1 by the sum of two tensor codes, S₁ ⊗ M + M ⊗ S₂ (deficiencies multiply) | Its decoder is τ₁ ⊗ K₂ + K₁ ⊗ τ₂ − K₁ ⊗ K₂, which contains full partial transposes, so the window is not bounded | A product whose decoder is built from K₁ and K₂ alone |
| **X12** | Inferring a bounded global monotone row-word cover from bounded whole-row spread or unit-speed native geometry | Block reversal at d=s² has an O(L) implementation. K words with length≤ℓ and bands of radius a have at most H=K(2a+1)^{ℓ+1} monotone branches; covering the persistent root reads requires at least (1−H/s)L/2 coordinate exceptions. [Written proof and controls](notes/row-spread-controls.md). | A correctness-dependent extraction, a different cover notion, or an explicit growing-complexity budget that still pays for itself. Row spread itself is not refuted. |
| **X13** | Transferring work-window planarity alone to hyperfiniteness of the helper relation | A one-work-walk geometric schedule with supplied ordered matching lists has an expanding row helper graph despite planar work windows, robust under a small linear genie. No fixed one-work-tape compiler is claimed. Even a matching row graph has nonhyperfinite whole-row coordinate completion. [Written calibration](notes/window-pages-and-input-attachments.md). | Supply a separator of the augmented row graph using additional attachment/native/correct-source structure, or obtain a coding deficit that tolerates expansion. Existing one-work-tape machine exclusions remain valid. |

## Maintenance

- Fable re-reads this file at the start of a work session and before proposing a change of target,
  and checks that the work in hand names a front. Work that names none is added here first or dropped.
- A result changes the file in the same commit that publishes it: a removed chunk goes to the table
  in Section 1, a proved tie moves an indirect front to Section 2, a dead idea goes to Section 4.
- Last re-evaluation (D0), 13 November 2026: independent generic tuples avoid prescribed product
  identities, while representation tuples have many, so the route through (U) fails (X10).
  The group model is the direct front D8; the requirement on r(ε) is weaker than one half, making
  D4 Fable's target. Astra's audit strengthens X10, qualifies the ordered-cover claim, and shows
  why distant sector gains alone do not identify a new mechanism. No new transposer class is excluded.
- Linear D1 and D8 now have checked Lean proposition definitions and helper lemmas, not proofs of the
  conjectures. Statements still wanted when their parked fronts resume: (U) at w = 1 (I2, generic only)
  and "three blocks never exceed pairing + 3" (I1).
- D4 source audit, 13 November 2026: [table and criterion](notes/native-cone-property-audit.md).
  Native provenance remains unknown for the abstract families, not disproved. The table separates
  all-native geometry from correct-source necessities, records which old claims retain the false
  Q9.1 premise, and replaces the universal-genie research target by a sufficient selected-fibre
  target where appropriate. This is an accounting and strategy clarification; no new class is excluded.
- D4 follow-up, later 13 November: Fable's window extraction survives independent review with
  sharper constants. Astra's raw-boundary conditioning extends its use from actual machine
  fibres to all binary storage codes on the old cones. D1 now has a sufficient native tie,
  with the precise nonlinear/growing-alphabet scope stated in Lean. The geometry and conditional
  crux transfer remain written proofs; no rate bound or new machine exclusion has been proved.
  The proposed stronger global row-word cover fails by X12.
- C22 review, 13 November: the rectangle expansion bound is strengthened and Lean-verified
  by reusing Paper 5's independent-coordinate theorem. The exact native window-page quotient
  is Lean-verified, with starting-cell cases repaired and endpoint uniqueness expressly
  excluded. Literal interval-overwrite amortization is also Lean-verified; the native
  label adapter remains open. The one-work-tape calibration supplies a written row-separator
  criterion and identifies the missing raw-attachment layer (X13). It does not reprove the
  existing one-work-tape exclusion or yield a new capacity bound.
- C24 review, 13 November: the grid necessary conditions survive after counting distinct
  helpers and paying for reverse degrees; exact subgroup exchange is replaced by a
  bounded-index criterion. A written grid/component bound extends to every recovery
  rule of a Cartesian-product code and excludes slow-padded Paper 15 full-cube fibres,
  even after arbitrary balanced relabelling. The original growing blocks remain open.
  Native interval/label semantics are now Lean-verified; finite-list count transport
  and the full extraction remain pending. No new native-machine class is excluded.
