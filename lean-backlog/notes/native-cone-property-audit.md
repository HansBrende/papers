# Native cone properties and the remaining extraction problem

Hans Brende and GPT-6 Astra, 13 November 2026.

**Fronts D0, D4 and D9.** This answers Fable's C18 against repository revision
`af9045d96b31c8f36fb95592de940b3c59904823`, with the roadmap clarification in
`c1ab85c` and Paper 20's unchanged cited theorem scopes rechecked after
`f849f4b`. It is a source audit and a written
bookkeeping corollary of existing results, not a new transposition lower bound.
The table separates properties of a recovery relation from properties of its
physical realization and its correctness set. The distinction changes which
theorem we should try to prove next.

**Conclusion.** We found no proved property of *all* eligible native cone systems
that both separates them from the abstract high-rate families and gives the
required coding deficit. Several useful certificates distinguish restricted
native classes; none is an established normal form for arbitrary curved motion.
The best remaining information is the joint causal realization: ordered raw
reads and actual append roots, all work-return and state edges, and a common
paid transcript. A promising next target is to extract a sufficient certificate
on **one selected cheap-cut fibre**, rather than bound every code on every
native relation. Section 5 states the exact success test and its missing premise.

## 1. The native class and the rate requirement

Write $L=d^2b$, with $b=\max(1,\lceil\log_2d\rceil)$ unless a result explicitly
allows all $b\ge1$. Fix the machine's tape count, finite state and work alphabets,
and linear-time constant before letting $d$ grow. Work tapes are readable and
writable; the append-only output is not readable. Revealed work records are
joint records, not independent bits by assumption.

[Paper 14, Definition 9.2][P14C] defines `SCone` using oblivious native schedules
that append exactly $L$ bits, their **actual append times**, a time bound, and a
genie leaving bounded full dependency depth. Its definition imposes **neither
transposition correctness nor cheapness of that genie**. These enter separately:
Corollary 9.3(a) supplies a cheap genie, and 9.3(b) uses a hypothetical correct
transposer to turn its revealed records into an index code. Both parts are
Lean-verified.

Thus the native statement-level bridge already exists. Advice and multiple
causal hops have not been forgotten. What is open is a suitable native coding
bound, or a weaker bound on the particular correct-source fibres that the
contradiction uses. A correct-machine necessity cannot silently be added to
every member of `SCone`.

For fixed $k,\beta,C$, let $\rho_*(D)$ be the supremum of the valid native
index-code crux rates at depth $D$. The exact useful test is

$$\rho_*(D_\varepsilon)>\varepsilon
\quad\text{for some }\varepsilon\in(0,1].$$

The sufficient envelope in [Paper 14, Remark 9.4][P14C] is

$$\rho_*(D)\ge k\beta C(\log D)^{-c/k^2},\qquad c<1/c_1,$$

using $\log\log D_\varepsilon\le c_1k^2\log(k\beta C/\varepsilon)$.
It is **a sufficient envelope, not the weakest possible or a necessary rate
law**. Remark 9.5 similarly gives a sufficient degree-gap test:
$\rho(\Delta)(\log\log\Delta)^a\to\infty$ for every $a>0$, on the appropriate
native relations with the stated trimming and accounting. These two remarks
are explicitly labelled **proof sketches**; the finite Corollary 9.3 is formal.
The unrestricted abstract version of the gap test is false by Paper 15,
Corollary 6.2.

## 2. The comparison table

“Unknown” below means no physical realization or impossibility of such a
realization is established by the cited results. It does **not** mean that the
abstract family violates the condition. P13 and P15 refer to their abstract
code families, not P15's separate theorems about native machines. All degree,
depth and patch parameters are fixed before length grows when using an
asymptotic assertion.

### 2.1 Properties supplied by native extraction

| Property and exact source | Scope; relation alone? | P13 abstract family | P15 abstract family | Proven coding use |
|---|---|---|---|---|
| Bounded full cones: P4 Lemma 4.4; P14 Corollary 9.3(a); P20 Lemma 9.1 | Actual last-visit DAG, state spine, input attachments and append roots; **realization data**. Depth gives at most $\sum_{j=0}^D(k+1)^j$ input occurrences per bit cone. P20's evaluation theorem additionally uses a frozen correct fibre. | No native realization supplied. Its checks have a bounded-radius tree-cover construction (P13 Propositions 4.3–4.4), which is not a tape realization. | No native realization supplied. | Native recovery/index-code bridge. Depth alone gives no adequate deficit. |
| Bounded degrees on both ports after paid trimming: P5 Corollary 3.8; P15 Theorem 9.2 (N) | **Relation property**, obtained by deleting high-reuse coordinates and conditioning on their bits. Right degree alone follows from depth; left degree does not. | **Yes:** Theorem 7.1, fixed cap before tower level. | **Yes:** Theorems 5.5 and 6.1, fixed cap before length. | Enables packing and local certificates. After removing self-demands, the general degree guarantee is only an inverse-degree deficit. |
| Few short paired paths: P5 Theorem 3.3 | **Relation property** after physical extraction. Every induced degree-capped full cone relation has $O_{k,D,C,\Delta,r}(L/\log d)$ pairs at distance at most $r$, uniformly for $b\ge1$. No correctness or genie-cost premise. | **Yes, stronger:** all paired distances diverge (Theorem 7.1). | **Yes, stronger:** all paired distances diverge (Theorems 5.5, 6.1). | With extra relation certificates gives half bounds; alone it does not. |
| Partial-transpose transport: P5 Lemmas 3.4–3.6 | **Realization-dependent.** Distinct matched labels can be transported in a controlled token relaxation of the same trace. For $m$ labels, $m\log_2d\le C_0K(K+r_0+3)U+3L$, with occupancy $C_0$, tapes $K$, registers $r_0$, ticks $U$. | **Unknown** for a physical ordered realization. | **Unknown** for a physical ordered realization. | Proves the preceding paired-distance bound. It is not a claim that arbitrary coded information routes as independent tokens. |
| Common native partition and high-rate typical fibres: P15 Proposition 9.1 and Theorem 9.2 (N) | **Source/realization data.** Chosen trace-specific cuts, actual append roots, revealed records and exterior bits; source and trace costs paid jointly. Not every genie. | No all-length common-partition theorem is supplied there. | **Yes to the abstract counting properties:** Theorem 6.1 chooses one relation/partition before every source subset and has an exponential uniform-source tail on all original coordinates, for all lengths. **Unknown** for native provenance. | Transfers a hypothetical machine to high-rate codes, but abstract partition/counting properties do not distinguish it. |
| Finite coarse skeleton: P16 Lemma 6.3 | **Realization-dependent, every schedule.** At any fixed macroscopic scale, finitely many tuples; one can fix a tuple on a subsequence. | No such tape data supplied. | No such tape data supplied. | A compactness tool. It discards fine-scale motion and implies no rate bound or bounded fine-scale phase count. |
| Crossing-to-independent-cone dichotomy: P16 Theorem 5.4 (D) | **Realization-dependent, every schedule with the stated antecedent.** A sufficiently small endpoint-inclusive cut from a large output set to long crossing endpoints gives a positive independent cone set, after guards. | Native antecedent **unknown**. | Native antecedent **unknown**. | Yes, if the small cut is supplied and its cost beats the independent-set credit. The theorem does not produce the cut. |
| Original/simulator path transport: P18 Lemmas H.1–H.2, Proposition H.4 | **Realization-dependent.** Actual paths and cuts transported with guards, lookahead and address dilation; information applications also need a common correct simulator fibre. | No compatible simulator/trace supplied. | No compatible simulator/trace supplied. | Preserves native invoices on original adaptive runs; does not manufacture a capacity bound. |

Here paired distance is between the two ports of the same demanded coordinate,
without adding a pairing edge. The incidence graph is already bipartite.
P13's diverging **odd girth** concerns a different, undirected graph on
coordinates (Corollary 9.3), not the bipartite incidence graph. P15's majority
support proof also gives an undirected containing graph with diverging odd
girth at its fixed cap. These properties coexist with the high rates.

### 2.2 Additional certificates and correct-machine necessities

These rows are not automatic properties of all `SCone` members.

| Property and exact source | Scope; relation alone? | P13 | P15 abstract family | Proven rate or machine consequence |
|---|---|---|---|---|
| Global separation or uniform hyperfiniteness plus paired separation: P5 Lemma 4.1, Theorem 4.2, Corollary 4.4 | **Additional relation properties.** Uniform hyperfiniteness requires component bounds independent of length after an arbitrarily small deletion. | Cannot hold in the half-rate-forcing form for its above-half codes. | Cannot hold in that form for its above-half codes. Yet Theorem 6.1 has coordinate blocks of size at most $\sqrt L$ and incidence components of at most $2\sqrt L$ ports; that is **not** uniform hyperfiniteness. | All-alphabet half bound. Native cones can be nonhyperfinite (P5 Corollary 7.9); almost all paired ports need not become disconnected cheaply (Theorem 8.3). |
| Bounded monotone row-word cover: P5 Theorem 6.4 | **Additional relation property in the prescribed physical row order.** Every incidence outside $o(L)$ exceptions is covered by one of fixed $K$ bounded-length words of monotone partial row maps with fixed bands. | **Unknown**; its displayed rate above half alone does not refute this weaker deficit. | Impossible with fixed $K$ whenever its deficiency is smaller than $1/(8K)$. This does not rule out a cover whose $K$ grows with the cap. | All-code deficit at least $L/(8K)-o(L)$, independent of fixed depth. Native extraction is proved for the specified rotated executor in P5 Lemma 8.4/Theorem 8.5, not arbitrary schedules. |
| Induced half-rate certificates: P7 Theorems 3.4, 5.2, 5.3, 5.10 and Corollary 6.9; P10 Theorem 3.6 | **Additional relation structure:** nested elimination, qualified reciprocal/sparse patterns, or certified induced sets. | Quantitatively limited by its code rate, not excluded as small induced pieces. | A code of deficiency $\epsilon L$ can have no certified induced set larger than $2\epsilon L$. | A certified set $W$ gives $\log_a\#C\le L-\#W/2$. No theorem here extracts enough such vertices from every native cone. |
| Bounded-width, bounded-complex-coefficient recovery: P5 Theorem 4.5/Corollary 4.7 | **Decoder data**, beyond the relation; fixed block width and uniform coefficient bounds over $\mathbb C$. | Its finite-field code is outside these hypotheses. | Its finite-field/binary code is outside these hypotheses. | Half-rate bound in that restricted model; not arbitrary characteristic or nonlinear recovery. |
| Complete source-bank geometry: P9 Theorems 2.7, 3.5, Theorem 4.2 and its §4 consequences, Corollary 5.3; gap-area memo Theorem 3.2 | **Realization-dependent, common correct fibre.** Full family spans, fixed span-partition count $N$, a two-class core, finitely many exceptions, and all source/phase/record costs. | **Unknown** for a compatible realization. | **Unknown** for a compatible realization. | Uniform exclusions and necessary tail/cover/movement costs. Fixed tape count does not supply the span or core hypotheses. |
| Independent raw queries with bounded moving sources: P9 Theorem 7.1/Corollary 7.4 | **Specified interface**, not all decoders of a relation. Every query must be served; all movement is paid. | No such interface established. | No such interface established. | Order-independent movement lower bound. The coded-caching calibration loses its raw witnesses after $o(L)$ extra advice, so this is not an arbitrary-cheap-advice obstruction. |
| Small causally autonomous column groups: P9 Theorem 8.2/Corollary 8.4 | **Computation data.** Every local field and output factors through its own consecutive column group and the same paid helper, with total field capacity bounded by the original edge capacity. | No native factorization established. | No native factorization established. | Under the stated block-network capacity profile, groups of size $o(\log d)$ force source deficit plus helper entropy to be $L-o(L)$. Final output purity alone does not suffice. |
| Macroscopic crossing expansion: P16 Theorem 5.5 (X), Theorem 6.7 (S); P18 Theorem H.7 (E) | **Correctness-dependent realization.** Oblivious correct traces have large cuts from every large output set to long crossing endpoints. P18 gives this on original adaptive runs outside exponentially few timely correct inputs, at canonical width. The expanding leg may depend on the output set. | **Unknown** for a correct-source realization. | **Unknown** for a correct-source realization. | Positive cut lower bounds. Neither a cheap cut nor a coding deficit for the remaining cones is supplied. |
| Two active long-return heads: P16 Theorem 4.1 (H); P18 Theorems 4.3 (R), 5.5 (H) | **Correctness-dependent realization.** Quantitative off-carrier returns/cuts; P18 handles adaptive inputs and all positive widths with its stated state budgets. | **Unknown**. | **Unknown**. | Excludes one unrestricted head with all other long-return activity sufficiently small; selected output sets, not an unrestricted relation theorem. |
| Input/output-aware cuts: P16 Lemma 7.1 (R); P18 Theorem 5.4 (I), Proposition G.3 | **Correctness and actual ordered ports.** On a common correct fibre of deficit $\delta$, a cut for $D_0$ demanded bits costs at least $D_0-\delta$, including root outputs. Adaptive pooling pays the cut/trace menu. | **Unknown** for native realization. | **Unknown** for native realization. | Exact information invoice. P16 Corollary 7.3 sums scales only with an extra disjoint-region premise; Proposition 10.2 gives one common cut for many row demands. |
| Curvature and exceptional physical time: P2 Theorems 6.3, 7.5; P4 Theorem 3.12 (Cq), Corollary 3.24 | **Correctness-dependent physical limits**, with the respective trace/subsequence hypotheses. A contracting clock needs positive exceptional time unless its stage regularity fails. | No ordered native realization supplied. | No ordered native realization supplied. | Excludes affine and regular contracting families. It does not bound arbitrary nonlinear coding. P2 Theorem 8.1 and its memo show why walk-only cut tests can be satisfied by data-free padding. |
| Original full-entry quotient invoice: P18 Theorem H.5 (Q), Corollary H.6 | **Correct-source realization and code capacity.** Actual quotient, all bit lanes and self-dependencies retained; simulator/source/cut costs explicit. | No such realization supplied. | No such realization supplied. | A genuine capacity deficit on this exact quotient must be paid. Degree, separation, a large useful entry set, and a small cut are not supplied by the invoice. |

Two tempting extra signatures are already insufficient. First, P15's
all-length construction uses disjoint tower blocks of size at most $\sqrt L$
and a revealed remainder. Generic sublinear components or separators therefore
do not distinguish native cones. Second, a binary relation of fixed helper
degree $\Delta$ with a storage code has local Boolean recovery functions.
Extending their truth tables gives a **nonuniform** decoder circuit of
$O_\Delta(L)$ size and $O_\Delta(1)$ depth using a fixed finite Boolean gate
palette. This elementary observation supplies neither uniform generation nor
unit-speed tape wiring. Bounded circuit depth and a finite local gate palette
alone are insufficient; the physical realization is the missing resource.

## 3. What is already excluded, and what remains

There is no established **smallest remaining class** of schedules. A list of
necessary conditions does not prove that their intersection has a correct
machine, or even that a particular proposed trace satisfies all of them.

| Published exclusion | Hypotheses that must not be dropped |
|---|---|
| P16 Theorems 9.2 (B), 9.3 (J), 10.3 and Corollaries 10.4–10.5 | Fixed bounded joint phases with monotone/coarsely monotone input and bank heads; other workspace small. Quantitative extensions permit some growing phase counts with an explicit slope threshold. Suffix versions require untouched input rows. These are not exclusions of every curved trace. |
| P16 Theorem 9.7 (Q) | Fixed owner load and finitely many logarithmic-height windows on **all** work heads. It does not allow an unrestricted extra head. |
| P2 Theorem 7.5; P16 cascade memo Theorem 1.1 (C) | A complete contracting clock, fixed-stage affine-limit regularity and sufficiently small exceptional physical time. All five exact published C1–C5 constructors are excluded for $b=1$ and canonical width, fixed alphabet and sublinear controller bits. Unlisted variants need their own hypothesis check. |
| P16 Theorem 10.8 | Stronger explicit demand cuts for C3/C4, allowing some growing controller/alphabet charges. This is not the proof for C1/C2/C5. |
| P9 Corollaries 4.3–4.5, 4.7, Theorem 4.6 and its gap-area memo | Fixed full-span partition, complete source families and the stated core/exceptions/cover conditions. One exceptional family is excluded without a core envelope; two exceptions with a critical inverse-square tail are not settled by that conclusion. |
| P18 Theorem C.2, Proposition C.4, Theorem B.2 | A declared, correctly charged getter/catalogue system or a paid scan loader with immutable archives, with their quantitative budgets. The bounds apply per fixed declared system, not simultaneously to all possible systems. Global computability, restoration after mutation, or low marginal entropy is not a substitute for these hypotheses. |

The cascade memo's canonical C5 exclusion is Lean-verified; the remaining
source-to-clock proofs and Rust correspondence include written work. P16's
experiment README still calls the five completions open. That wording is stale;
the memo and current main paper exclude them. Finite geometry tests are not the
proof of their exclusion or an evaluated threshold dimension.

For a broad native test, fix the machine parameters and consider hypothetical
correct linear-time families with two work heads meeting the quantitative
long-return requirements, the positive crossing requirements above, and complete source and
output attachments. One may fix a macroscopic skeleton and an expanding leg
on a subsequence for a chosen output-set sequence, without deleting any motion
below that scale. Such a family
must evade the applicable phase, regular-clock, source-cover and getter
certificates. No bounded number of stages, bounded row window, or bounded
decoder repertoire has been derived for this remaining class.

A narrower **conditional source-cover test** is available inside P9's
admissible geometry: a two-class core, two exceptional complete families,
fixed full-span partition count, small residual families, and an inverse-square
core envelope. Near-full correctness there would require quadratic-scale
complete-cover complexity, sufficient complete observable movement and global
continuation growth, and the actual gap-area inequalities at **every** fixed
phase modulus. The memo's canonical-modulus sharpness geometry is not a
transposer and is not known to meet all the other requirements on one profile.
This is a useful restricted test, not a normalization of all machines.

Some old apparent necessities must be removed from this reading. P11 Theorem
5.1 (L), Theorem 4.13, Corollaries 4.16–4.17 and the corresponding all-code
localization conclusion retain the now-false unrestricted [Q9.1] premise.
The current paper marks the localization theorem vacuous under that premise.
Its cold-genie, hop/transport and paid extraction tools survive; unbounded
revisit or merge-depth conclusions require a new **native** coding hypothesis.
P14 also supplies general depth reduction, so depth robustness alone is not
an untouched way around the present wall.

## 4. What the one-hop work does and does not bridge

P14 Corollary 9.3 is a bridge for **native cones**. It is not a theorem that
those cones have the whole-row, bounded-class, or covariant form of D1–D3/D8.
Conversely, the three gaps discussed in P17 §7.4 concern applying those
restricted shared-decoder models to machines; they do not invalidate the
native bridge.

As Fable's roadmap correction emphasizes, regularity along an output row and
curvature at the scale of the whole tape are compatible. Curvature alone
does not refute a row model; variation of the actual read pattern inside rows
can prevent the model from applying.

Even for periodic stretches, we should not claim the paid shared-decoder
normal form is finished: P17 Problem 9.4(a) is open. P20 Lemma 9.1 now formally
evaluates the exact symbolic cut-cone trees on frozen native fibres, but its
Theorem 9.3 supplies only the old $1/(\Delta+1)$ capacity estimate. P4
Propositions 4.13–4.14 already show why that estimate cannot pay for the
depth-reduction cut.

P20 Proposition 9.6 additionally rules out two particular shortcuts to a
useful **per-column** class bound: discard every output whose cone touches a
cut, or absorb the frozen values into column-indexed cut slots. The state
spine makes the resulting counting bracket negative. It is not a theorem
against all per-position normal forms, and it does not make every bit of
advice into a bounded number of column classes. The growing-repertoire and
group-model investigations remain legitimate model questions; they do not
yet supply the missing native property.

## 5. A weaker sufficient target with an exact invoice

Here is an explicit consequence of [P15 Proposition 9.1][P15N] and
[Corollaries 10.2–10.3][P15P]. It makes the next target smaller without
asserting any new patch-extraction theorem.

**Selected-fibre criterion (written bookkeeping corollary).** Let
$G\subseteq\{0,1\}^L$ be a nonempty successful source with at most
$2^{h_{\rm tr}}$ full traces. Choose a largest trace class. On that class
choose **one** native cut whose joint revealed record has at most
$2^{h_{\rm a}}$ values, and retain a common set of $m$ raw coordinates.
Freeze the exterior coordinates too. Suppose the native cone argument makes
each resulting nonempty projected cell a storage code for the retained
relation. Then one such cell $C$ satisfies

$$m-\log_2\#C\le
B:=L-\log_2\#G+h_{\rm tr}+h_{\rm a}. \tag{1}$$

If patches on **this same cell and retained relation** serve $s$ distinct
targets exactly, have at most $w\ge1$ scored targets each, coordinate overlap at
most $r$, and every served target has paired distance greater than $2w-1$,
then

$$s\le2rB. \tag{2}$$

Helpers must lie inside their patch and the target's actual retained helper
set. More generally, a fixed system of Boolean predictors with $s>0$ scored
occurrences, average error $\bar e$ under the uniform law on this same $C$,
and the separation conditions of P15 Corollary 10.2 satisfies

$$s[1-h_2(\bar e)]\le2rB. \tag{3}$$

Here $h_2$ is binary entropy. A certificate violating (2) or (3) contradicts
the hypothesized source computation.

*Proof.* The largest trace contains at least $\#G\,2^{-h_{\rm tr}}$ inputs.
There are at most $2^{h_{\rm a}+L-m}$ choices of its revealed record and
exterior word, so a largest cell has size at least
$\#G\,2^{-h_{\rm tr}-h_{\rm a}-L+m}$. Projection is injective after fixing
the exterior, proving (1). Apply the patch entropy bound on this cell:
its deficit is at most $B$, and long served targets contribute no short-pair
exception. This proves (2); the predictor bound proves (3). No independence
of revealed values is used. ∎

Exterior length cancels from the **absolute** deficit in (1); large retention
or coverage does not follow for free. Choosing a fixed patch/predictor system
after selecting $C$ needs no extra menu cost. Choosing different systems for
individual inputs is different and requires the menu accounting of P15
Corollary 10.4.

For a full-cube oblivious computation, $h_{\rm tr}=0$ and the test is simply
$s/(2r)>h_{\rm a}$ for $r>0$. In the native physical-bit regime of P15
Theorem 9.2, a full successful source (or one with source deficit
$O(L/s_0)$) supplies a selected fibre of deficit $O(L/s_0)$ at simulator
parameter $s_0$. An exact or predictive certificate with target density bounded
below uniformly as $s_0$ grows, fixed predictive advantage, and overlap
$o(s_0)$ would contradict it, provided all other extraction conditions hold.
Its target count per patch may depend on $s_0$ but must be fixed before
dimension grows. The simpler one-target patches $\{q\}\cup N(q)$ have
overlap at most $\Delta+1$ and recover only an inverse-degree bound; they
do not meet the useful scale automatically.

There is also an original-adaptive-run version of the target already in
P18 Theorem H.5/Corollary H.6: certify a capacity deficit on the **full actual
entry quotient** greater than its source-plus-transported-cut invoice
$\delta L+v_sG_s\#B_{\rm cut}$. Those results permit input-dependent cuts
on a simultaneous good event. They do not supply a small cut or the deficit.

### The next bounded unit

1. Work on the selected-fibre criterion, using one actual source/trace/cut
   throughout. Try to extract either P5's complete row-word certificate or
   P15's useful patch credit from the paid native transport/source structure.
   Compare the resulting credit directly with $B$; a positive but underpaid
   deficit is not a success.
2. Start by testing the missing **overlap or complete-cover estimate** against
   the published controls, before any new formalization: P9's serial-return
   and gap-area geometries, P18's redundant archives (Theorem 7.1) and
   historical-feedback control (after Corollary I.3), and P13/P15's actual
   recovery maps. Many long dates, many cells, or a large marginal support
   do not imply independent information. The feedback control has
   $\Theta(Ld)$ counted feedback in $O(L)$ time. A nontransposing control
   only refutes an estimate whose hypotheses it satisfies; it does not
   refute a correctness-dependent extraction claim merely by sharing its geometry.
3. Stop that candidate estimate if one control violates it, a cheap extra
   revelation removes its witnesses, or its constants leave credit at most
   $B$. Record precisely the failed implication. Reopen a model front only
   with a stated native tie or a result that changes one of these tests.

**What is missing:** a nonvacuous native extraction estimate that passes those
controls. No result in this audit supplies it, and no new class of transposers
has been excluded. D8's shared-decoder/full-regular-representation success test
remains valid, but it is parked while this native comparison is resolved.

## Sources

Numbers refer to the revision pinned above; theorem names and source files
identify the statements if later edits renumber them. “Lean” in the discussion
means the cited finite statement is formalized; it does not transfer that
status to a paper's separate arithmetic or machine-realization adapters.

- [P2, motion and recursive clocks][P2M]; [padding][P2P].
- [P4, native decomposition and counting][P4D]; [motion][P4M].
- [P5, native transport][P5N]; [directed coding][P5D]; [row words][P5R]; [connected demands][P5C].
- [P7, paper][P7]; [P9, source engine][P9S], [source covers][P9C], [uniform consequences][P9U], [shared continuations][P9H], [movement][P9M], [causal groups][P9G]; [gap-area memo][P9A].
- [P10, paper][P10]; [P11, paper and corrected scope][P11].
- [P13, paper][P13]; [P15, amplification][P15A], [all lengths][P15F], [native fibres][P15N], [patches][P15P].
- [P14, native crux and rate remarks][P14C]; [Lean machine interface][P14L].
- [P16, paper][P16]; [cascade memo][P16M].
- [P17, machine bridge discussion][P17C]; [open problems][P17O].
- [P18, paper][P18]; [P20, cut-cone evaluation and negative brackets][P20].

[P2M]: ../../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/paper/sections/motion.tex
[P2P]: ../../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/paper/sections/padding.tex
[P4D]: ../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/decomposition.tex
[P4M]: ../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/motion.tex
[P5N]: ../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/native-bridge.tex
[P5D]: ../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/directed-coding.tex
[P5R]: ../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/row-words.tex
[P5C]: ../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/connected-demands.tex
[P7]: ../../Nested-Elimination-and-Half-Rate-Bounds-for-Storage-Codes/paper/main.pdf
[P9S]: ../../Source-Covers-and-Barriers-to-Tape-Transposition/paper/sections/source-engine.tex
[P9C]: ../../Source-Covers-and-Barriers-to-Tape-Transposition/paper/sections/source-covers.tex
[P9U]: ../../Source-Covers-and-Barriers-to-Tape-Transposition/paper/sections/uniform.tex
[P9H]: ../../Source-Covers-and-Barriers-to-Tape-Transposition/paper/sections/shared-support.tex
[P9M]: ../../Source-Covers-and-Barriers-to-Tape-Transposition/paper/sections/movement.tex
[P9G]: ../../Source-Covers-and-Barriers-to-Tape-Transposition/paper/sections/causal-groups.tex
[P9A]: ../../Source-Covers-and-Barriers-to-Tape-Transposition/memo-gap-area/paper/main.pdf
[P10]: ../../Directed-Reciprocity-and-Deep-Nesting-Bounds-for-Matrix-Transposition-on-Tapes/paper/main.pdf
[P11]: ../../Merge-Depth-Input-Steering-and-the-Coding-Core-of-Matrix-Transposition-on-Tapes/paper/main.pdf
[P13]: ../../Storage-Codes-above-Half-Rate-under-Paired-Distance-Separation/paper/main.pdf
[P14C]: ../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/paper/sections/consequences.tex
[P14L]: ../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/lean/BoundedStackDepth/Machines.lean
[P15A]: ../../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/paper/sections/amplification.tex
[P15F]: ../../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/paper/sections/partitions.tex
[P15N]: ../../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/paper/sections/native.tex
[P15P]: ../../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/paper/sections/patches.tex
[P16]: ../../Oblivious-Linear-Time-Tape-Transposers-Need-Macroscopic-Crossings/paper/main.pdf
[P16M]: ../../Oblivious-Linear-Time-Tape-Transposers-Need-Macroscopic-Crossings/memo-cascade-obstruction/paper/main.pdf
[P17C]: ../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/construction.tex
[P17O]: ../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/open.tex
[P18]: ../../Macroscopic-Information-Transfer-in-Adaptive-Tape-Transposition/paper/main.pdf
[P20]: ../../Ramsey-Free-Bounds-for-Two-Stage-Shared-Decoder-Composition/paper/sections/sweep.tex
