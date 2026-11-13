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

A proof that no machine exists must hold for all schedules, fail for abstract relations (codes of
rate near 1 exist there), fail for motion that ignores the data (padding), constrain all address
scales at once, and use the shape of tapes. A machine, for its part, cannot avoid curved head
motion, expanding relations, and codes that are neither gadgets of bounded size nor linear with
bounded complex coefficients (paper 17, Section 4.5). For adaptive machines the same question sits on the machine's
own runs ([Macroscopic Information Transfer](../Macroscopic-Information-Transfer-in-Adaptive-Tape-Transposition/)).

**One-hop form** (paper 17, Sections 5 to 7; this is where we work). A d × d matrix X; a decoder
computes each entry of Xᵀ from a bounded window of X; the *code* is the set of X it transposes.
Symmetric matrices give rate ½ (the *pairing value* d(d+1)/2).

> **Is there a code of rate ½ + δ at a bounded window w ≥ 3, or is every such code at most
> (½ + o(1)) d²?**

Known in general: window ≤ 2 gives at most d(d+1)/2 + d − 1; window w gives at most w d(d+1)/(w+1).

Write R(w) for the best rate in the one-hop whole-row model at window w as d grows, so
½ ≤ R(w) ≤ w/(w+1). A uniform deficit for R(w) would suffice if D4 transfers it to schedule-cone
rates with controlled advice and composition losses; that bridge remains open. **No construction
gives R(w) > ½ for any fixed w, and no bound stays away from 1 as w grows.** The value at w = 3
is a test case; uniform control for growing windows is a stronger target motivated by the machines.

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
| **D9** | *The native crux*: every index code for the cone systems of k-tape oblivious linear-time schedules, at cone depth D, needs at least ρ(D)·L bits. Needed: ρ(D) ≥ kβC (log D)^{−c/k²}. Conjectured: ρ = ½ (the native half bound). | Proved: it excludes oblivious linear-time transposers ([Bounded-Stack DAGs](../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/), Corollary O(b) and the remark on the rate needed). Advice and many hops are already inside this statement: the index code is the advice, and depth reduction has collapsed the hops into cones. | Open. Known only for restricted classes of schedules. The relation-level properties proved so far (bounded degree after trimming, paired-distance separation) do not imply it: abstract relations with those properties carry codes of rate near 1. | Exists: `Crux`, `crux_excludes` in that paper's library |
| **D4** | *A class property of cone systems*: a property that the cone systems of all linear-time schedules have, that the abstract high-rate relations lack, and that forces a deficit (paper 17, Section 7.4, step 1, and Problem 9.4(a)) | With it D9 follows. It is also what would make a front of 2b count for the machines. | Open. One candidate is known: on stretches of periodic motion, translated outputs read translated positions (this is D2); it says nothing about curved motion, where the cones of one output row need not lie in few input rows. Next: a table of every proved property of cone systems against the abstract families, and the smallest class of schedules that nothing excludes. | Not written |
| **D5** | *All scales at once* (Problems 9.3, 9.5): a quantity subadditive over steps, large for the swap at every scale, not raised everywhere by one pass | Would turn "every digit must be broken" into a factor log d | Open. No such quantity vanishes on both kinds of stage; the cut-rank profile fails on a shear ([pass-calculus §§2–3](notes/pass-calculus.md)) | Not written |
| **D6** | *Relative rigidity on ball patterns* (Problem 9.6) | A positive answer excludes oblivious linear-time transposers with linear data paths | Open; not worked on | Not written |
| **D7** | *The construction*: a code above the pairing rate that tape passes can compute | It would be the machine's core | No candidate. It must have every feature of "the wall today". | — |

### 2b. The one-hop form (paper 17's problems)

These are the wall as paper 17 states it in its model. A bound here decides the crux for cone systems that have the
model's shape (the helpers of a whole output row lie in few rows, or translated outputs read translated
positions). That real cone systems have this shape is proved only for periodic motion; for the rest it is D4.
A code above the rate here would be a real operator of boundedly many passes.

| | Target | Tie to the machines | State | Lean statement |
|---|---|---|---|---|
| **D1** | *Whole rows* (paper 17, Problem 9.4(c)): each column is a function of ≤ w rows; at most q^{(½+o(1))d²} matrices? | A code above the rate on increasing maps is an operator of boundedly many passes that transposes more than pairing. A bound gives D2 for every window. | Open for w ≥ 3. Linear case open even with one decoder for all columns. | `LinearWholeRowHalfRate` in [StatementsWholeRow.lean](StatementsWholeRow.lean): open proposition, reusing `LeanMachine.WholeRow`; separate uniform-in-field variant. |
| **D2** | *One-class relations* (Problem 9.4(b)): entry (c, r) from the w entries (i_m(r), c + j_m(r)) | Hypothesis on head motion alone; applies to single runs of adaptive machines; gives D3 for bounded windows | Open when rows and offsets are both spread, window ≥ 3 | Not written |
| **D3** | *Classes of any shape* (Problem 9.1(a), (c)): two classes, at most (½ + o(1)) d²? | Revealed bits split the outputs of a periodic stretch into boundedly many classes | Best bound 41/64 ([Shared Decoders](../Capacity-and-Composition-of-Shared-Transposition-Decoders/)); gains known are O(d) | In that paper's library (bounds); conjecture not written |
| **D8** | *Covariant decoders on a group* (slice of D1, linear): rows and columns indexed by G, relation rΣ, decoders commuting with diagonal translations; ordinary **field rank** of the group-algebra residual acting on F[G]^G ([twisted-swap §1, §9](notes/twisted-swap.md)) | It is D1 restricted to a symmetry class; blocks vary with the row and the relation expands when the Cayley graph does | Open. Ordered-support injectivity holds over every field, but a half-rate consequence needs a vanishing order-boundary fraction. Distant helper loops give sector gains, but no gain on the full regular representation ([controls](notes/covariant-word-baselines.md)). | `CovariantGroupHalfRate` in [StatementsWholeRow.lean](StatementsWholeRow.lean): open proposition for one shared κ, all characteristics; separate uniform-in-field variant. |

Current effort (13 November): Fable on D4 and D9 (the class property); Astra on D8 and, at Fable's request,
the table of proved properties of cone systems. I1 and I2 are parked. D5 and D6 have no one on them.

## 3. Indirect fronts

Each is a model problem. The last column is what must be proved before a result here counts on a
direct front.

| | Model problem | State | Missing tie |
|---|---|---|---|
| **I1** | *Boundedly many shared blocks* K = Σ_{a<M} A_a ⊗ B_a: at most (½ + o(1)) d² for fixed M? (Problems R, S of [item D](D-comparison.md); "three blocks never exceed pairing + 3") | Two blocks done. Three: special shapes done, general open; the involutive slice is parked while Astra works on I2. Lean: `ProblemR`, `ProblemS`, `problemR_of_problemS` in [StatementsD.lean](StatementsD.lean) (open). | Machines are not confined to bounded repertoire (shift above). Needs a version in which the blocks vary with the row, which is D1. |
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
