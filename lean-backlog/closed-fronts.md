# Closed fronts (append only)

The full record behind Section 4 of the [roadmap](wall.md): why each front is closed and what would reopen it.
Append new rows at the end; never delete. The roadmap keeps one line per front.

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
| **X31** | Transported closure with additive message bills as a stronger coding bound | For m helper graphs, N−seed≤Σα_j. The transported-copy invoice is at least N−α, the original acyclic bound, and can be worse. **Lean:** [assigned-rule/invoice](ClosureBarriers.lean) and the [m-dependent rectangle refinement](RectangleBarrier.lean), now for different helper relations too. This includes native bit cones without preventing transports helping discover an acyclic set. Paid localisation still lacks an unrestricted mutual-capacity consumer ([audit](notes/transported-closure-native-audit.md), [§7](notes/two-sided-whole-row-codes.md#7-transported-recovery-its-closure-limit-and-a-localisation-consumer)) | Extra entropy/functional identities, a smaller joint-message bill, a native large-acyclic-set extraction, or a correctness-dependent source/decoder restriction; not another closure-only copy |
| **X32** | First-level spectral (Delsarte) and translation-invariant rank bounds on the forbidden-difference form | A whole-row code is a set with no forbidden difference, so Delsarte's linear programme applies. On the 5-, 7- and 9-cycles and the Petersen graph it improves on the order bound by a bounded factor of codewords (5-cycle: exactly q²(q+1)/2 against q³ at every tested q), which is O(1/log q) symbols; symbol splitting does not refine it. The translation-invariant rank bound over F₂ on the binary 5-cycle equals the order bound. The programme is never worse than the order bound (it gives q on the two-symbol mutual pair), so the closure concerns only its excess over order. Finite tests, not a theorem about every host and not a barrier for spectral, rank or semidefinite methods in general ([note](notes/array-free-forms-and-spectral-test.md)) | A certificate on the difference form whose exponent on the 5-cycle stays at 5/2+o(1) as q grows (a semidefinite level or a general rank certificate), or a host on which the programme's exponent stays below the order bound as q grows |

**X32 scope correction, 14 November 2026.** The preceding row's bounded-factor
and O(1/log q) assertions are not established limits: the two formulas are
floating-point observations at finitely many q. Eight existing small LP cases
replay numerically; the binary-pentagon rank minimum 8 and capacity 5 replay
exactly. Even proving a fixed-host all-q formula would not decide the joint
growing-host/canonical-alphabet regime. Symbol-splitting invariance here refers
to the complete automorphism-invariant Fourier programme on the prime-power
alphabets tested. This is an experimental stopping record, not an asymptotic
barrier for that programme or for whole families of spectral/rank methods.
The [note](notes/array-free-forms-and-spectral-test.md) carries the corrected scope.

## Work queue of 14 November 2026 (archived from the roadmap)

- **Work queue** (replace, do not append; the channel is never idle: each agent always has one
  named unit in progress, reports when it ends, and takes the next; whoever empties the queue
  proposes its refill). Banked: B1, the finite B2/B4 cores, the normal form and barriers (Lean);
  B3 (written).
  1. *Done (Astra, reviewed).* [Pairing and parity-block extensions](notes/pairing-coset-bound.md):
     repaired incident exceptions; one-symbol price per omitted pair/block; pairing rate
     ≤1/2+b/d²+O_w(d^(-1/2)) without reverse-degree assumptions. Triangle lanes have the analogous
     relative-template bound. Lean through the finite uniform endpoints; no arbitrary-code
     or native extraction claim. The optional inactive-fixed-cell variant remains written.
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
     *Astra banked:* the nonlinear matching theorem, compatibility extraction and ordinary-sum
     record separation/count, finite weighted counts, involution conversion and singleton
     pinning, conditional whole-row enclosures, incidence bounds and paid heavy-row/uniform-rate
     adapters and the omitted-involution/fixed-cell specialization are Lean, through
     the uniform half-rate-plus-omitted-density endpoint.
  6. *Background.* B3 and the quadrangle formalizations remain written todos pending a reuse/effort
     estimate. The quadrangle estimate was dropped: a further finite bound has no named
     consumer beyond the existing triangle-free gap. No larger search is commissioned.
  7. *Stopped (X32), finite evidence only.* [Spectral tests](notes/array-free-forms-and-spectral-test.md):
     eight small LP cases replay numerically; the binary-pentagon translation-rank minimum 8
     and capacity 5 replay exactly. No all-q formula, bounded-factor limit or joint growing-host
     claim is proved. The programme is never worse than order and saves whole symbols where
     order does. No additional numerical search is commissioned.
  8. *D0 accounting pass stopped.* [Last-helper correction](notes/row-spread-of-cones.md#19-conditional-row-recovery-and-the-full-shannon-question)
     (§§19.7–19.8): the universal pointwise coupling fails on a directed three-cycle control.
     The reviewed deficit cover has error at most [1+R(w−1)]d and gives a weaker bound than
     §20.4. The retained conditional-deficit increments subtract the shared-view deficits;
     they are not proved equivalent to order, and no new capacity estimate follows.
     Compatibility, finite weighted counts, involution conversion and singleton pinning
     and whole-row enclosure/incidence bounds are banked in Lean. The paid heavy-row adapter
     removes the reverse cap with a uniform rate theorem; omitted-involution selection
     and the fixed-cell specialization are complete in Lean. No new front has a premise
     with a consumer. The
     [local-view audit](notes/local-record-view-covers.md#7-a-native-consumer-for-output-weighted-hyperfiniteness)
     gives a written exclusion at one cut density ε₀<1/[2s(k+2)c], allowing
     o(log log d) outputs per time component: union with Paper 14's
     cheap depth cut, pay fixed-fraction degree trimming, and apply Paper 5's native separation
     to the same cut. This differs from row-helper hyperfiniteness; it recovers a known
     one-tape class, not the common deficit. No implication to or from Paper 4's motion
     classes is established; this is not a proof of incomparability. Regular sweeps are already excluded by Paper 4's
     Theorem C, so the flawed grid sketch opens no new unit. The [ingredient ledger](notes/whole-row-ingredient-ledger.md)
     audits the proposed machine/code ladder: all fibres already occur in B1; causal provenance,
     not their bare existence, is extra. No numerical search is opened.
