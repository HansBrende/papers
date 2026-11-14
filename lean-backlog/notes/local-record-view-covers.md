# Local views of cut records: the consumer and its missing premise

Claude Fable 5.2 and GPT-6 Astra, directed by Hans Brende, 14 November 2026.
**Status:** written proofs and source audit, independently reviewed; no new
Lean endpoint in this note. The conditioning and fibre arguments reuse
[Paper 5](../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/preliminaries.tex).
This refines rung 2 of the [ingredient ledger](whole-row-ingredient-ledger.md).
Section 7 composes existing results into a native exclusion under
output-weighted hyperfiniteness of the time diagram. It is a written class
result, not a general capacity bound or a fully Lean-checked exclusion.

## 1. Restrict the message, then fix the exterior inputs

Let X range over the full binary cube on L raw coordinates. Output label j
demands X_{σ(j)}, where σ is a bijection (transpose indexing in the native
application). Let a(X) be a tuple of m records, each with at most s bits.
Fixed sets c_j of raw coordinates and V_j of record indices satisfy

  X|c_j and a(X)|V_j determine X_{σ(j)} on every input.

For T a set of records, put J(T)={j:V_j⊆T}. Choose any J⊆J(T), and set
S=σ(J). Let cap(S) be log₂ of the largest storage code on S for the induced
helpers c_j∩S at σ(j). Then

  s|T| ≥ H(a_T | X_{Sᶜ}) ≥ |J|−cap(S)

under the uniform full-cube law. The same lower bound holds for the logarithm
of the full attained range of a_T.

**Proof.** Fix the exterior input X_{Sᶜ}=z. For each attained record word a_T,
its fibre on S is an induced storage code: exterior helper values are fixed,
and every record queried by the selected outputs is fixed. Each fibre has
at most 2^cap(S) words. Since the conditional source on S is uniform and
independent of z, H(X_S|z)=|S|, while H(X_S|a_T,z)≤cap(S). The record is a
deterministic function of the whole input, so their difference is
H(a_T|z). Average over z; the record has at most s|T| bits. ∎

Without exterior conditioning, the restricted record is still a valid
partial-demand index message on the full source cube, but its projection
fibre need not be an induced storage code. For example, demand x₁ with helper
x₂ and message x₁⊕x₂: a message fibre projects onto both possible x₁ values,
although the induced one-coordinate relation has no helpers. Paper 5's
paid-conditioning and index-fibre lemmas already make this distinction.

The full-input premise matters. On an arbitrary native fibre the initial
conditional entropy need not be |S|. Input-dependent choices of J,T or views
also need a charged selector; they are not covered by the fixed-view statement.

## 2. The exact covering invoice

Suppose J_i⊆J(T_i) cover all output labels, and the induced capacities obey

  cap(σ(J_i)) ≤ |J_i|/2 + e_i.

Then

  s Σ_i |T_i| ≥ Σ_i (|J_i|−cap(σ(J_i)))
                 ≥ L/2 − Σ_i e_i.

If Σ_i |T_i|≤Cm, this gives sCm≥L/2−Σ_i e_i. Thus a cut with sm≤ε′L
is contradicted when Cε′<1/2 and Σ_i e_i=o(L), with a strict limiting margin.
The errors must be uniform and summable: an unspecified o(|J_i|) on patches
of bounded size is not such a premise.

The proof also permits fractional covers: give the pairs (J_i,T_i) nonnegative
weights λ_i, require Σ_{i:j∈J_i}λ_i≥1, and replace both sums by weighted sums.
For unequal record widths, charge the sum of the widths of records in T_i.
No independence among records or patches is used.

This is the familiar local-deficit/overlap consumer. Paper 15's
[Theorem 10.1 (P), and Corollaries 10.2–10.4](../../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/paper/sections/patches.tex)
prove related weighted information and exact-coverage bounds for separated
raw-coordinate patches. Their overlap is the reuse of raw coordinates;
here it is the reuse of advice records. Equating these two bills would need
an additional native argument. This is not an automatic application of the
row-separator theorem.

## 3. Which local half bound is available?

“Gadget-free below the girth” must specify the graph and the capacity premise.
Ordinary bipartite incidence girth alone is insufficient: the three-coordinate
sum-zero code has capacity two, and its incidence graph is a six-cycle.
There are three coordinates, yet capacity exceeds half.

A precise existing consumer is [Paper 5, Lemma 4.1](../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/directed-coding.tex):
if each coordinate's two demand ports lie in different incidence components,
the code is at half. In particular, if every target's ambient paired distance
exceeds 2n₀−1, every induced target set of at most n₀ coordinates satisfies
that condition. Any connecting path on its at most 2n₀ ports would contradict
the ambient distance. This is also the separation test in Paper 15's patches.
It concerns paired source/demand distance, not merely a work graph's girth.

The native task must therefore supply BOTH a cheap record-view cover and
local capacities for its induced **source-coordinate** relations. Small
components of a time graph alone do not identify those source/demand ports.

## 4. Two valid native counts, and their limitations

Use first-hit record views: walk backwards from an output root, stopping at
revealed time vertices. The native time DAG has at most k+1 parents and at
most k+1 children per vertex. Suppose cut-free paths have at most D edges,
and write K_D=Σ_{j=0}^D(k+1)^j.

**Arbitrary output blocks.** A safe bound on how many output views contain
one cut record is 1+(k+1)K_D. It can supply its own revealed output; every
other access enters one of its at most k+1 forward neighbours and follows
a cut-free path. K_D alone misses this extra edge and the revealed-root case.
At D=0, cut every step except the final one: the preceding record can supply
its own output and the final output, although K_0=1. This bound is for
first-hit views, not arbitrary influence paths through later cut records.
For the full native prefix one can sharpen the bound to K_D+1: a non-final
unrevealed output has a state child. Prepend that child to its cut-free path
ending just before the first cut hit. The library permits a cut root, so the
global depth premise bounds the distance to the hit by D. There are at most
K_D−1 such positive-length descendants; add the possible final output and
the record's own output. Taking unions of views over an output partition
inherits this bound. It is still exponential in depth. Degree counting alone
does not prove it equals the order bound; that also depends on which local
capacity certificates are used.

**Unrevealed components.** Delete the cut vertices and partition the remaining
time vertices by undirected connected component. The boundary records of a
component suffice for all its outputs. A record has at most k+1 forward
neighbours and therefore enters at most k+1 such components. Cover its own
revealed output separately if present. Total record multiplicity is at most
k+2, independent of D (hence also at most 2k+2).

This validates and sharpens the component overlap calibration. It does not
bound the number of outputs in a component, or prove a half bound on their
induced demand relation. The [row-separator criterion](window-pages-and-input-attachments.md#2-a-sufficient-row-separator-bound)
needs exactly such additional source/demand structure. The native separator
controls of Paper 5 obstruct particular decompositions; they do not by
themselves refute every overlapping record-view cover.

## 5. A broadcast control for prescribed small patches

A finite-state machine remembers the first input bit and then scans the
input rightwards, appending that remembered bit at each step until it reaches
the end. Work heads may stay still or sweep right without being used. The
schedule is oblivious and linear-time. This is a broadcast control, **not a
transposer**; it tests a claim from geometry alone.

Put P=D+1 and take lengths L=mP. Reveal steps 0,P,2P,…,(m−1)P. Between cuts,
the state dependency is a chain, so the required cut-free edge depth is D.
Every output of a period has that period's record as its first-hit view.
Except for the initial output, its raw cone does not contain the first input
bit; two full inputs differing only there show that the record cannot be
discarded from these views.

Fix this cut and these canonical first-hit views. For a cover by target sets
of size at most n₀, each period requires its record
in at least ceil(P/n₀) sets, apart from the possible initial-output saving.
This remains true if a patch combines outputs from different periods: count
its contributions separately for each record. Consequently

  Σ_i |T_i| ≥ m ceil((D+1)/n₀) − 1.

Thus a depth-independent C is impossible from geometry alone at fixed n₀,
or when n₀=o(D). The example permits fixed D followed by L→∞; it does not
rely on a growing machine table. It does NOT refute a choice n₀≥D+1, another cut, a correctness-dependent
cover, or the simultaneous local-capacity premise.
Its records are correlated copies of one bit: replacing them by a cheaper
joint record is a different allowed direction, not what this occurrence
invoice measures.

## 6. Locality in the index-coding literature

[Natarajan, Krishnan and Lalitha, *On Locally Decodable Index Codes*
(2018), Definition 1 and Theorem 1](https://arxiv.org/abs/1801.03895)
measure the queried broadcast symbols per demanded message symbol. At
locality one, under its convention that receivers do not already know their
own demanded messages, the optimum broadcast rate is the fractional chromatic number
of the complement of the mutual-side-information graph, including nonlinear
finite-alphabet codes. This verifies the citation and terminology; it does
not supply our large-locality cover theorem. Record bits and demanded entry
symbols must first be expressed in the same units.

The surviving unit is precise: produce small target sets with the stated
record budget AND an applicable induced-capacity theorem, at the same cut
and depth. Neither planarity without attachments nor small record views alone
supplies these two conditions.

## 7. A native consumer for output-weighted hyperfiniteness

Fix the work-tape count k≥1, the step-record width s, and a time bound
T≤c(L+1), where L=d²b and b≥1. Consider oblivious schedules that append the
required L output bits. Make the following **additional geometric premise**:
for each ε>0 there is an integer n(ε), independent of d, such that deleting
at most εT time vertices leaves undirected components with at most n(ε)
output steps each. The bound concerns outputs; components may contain
arbitrarily many other steps. Call this output-weighted hyperfiniteness.
Ordinary uniform vertex hyperfiniteness implies it.

**Written consequence.** Such a family cannot transpose every input in
time c(L+1) with fixed k and s. No row-helper hyperfiniteness premise is
needed. The proof uses the actual native input attachments, through
[Paper 5's paired-distance theorem and paid degree-reduction corollary](../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/native-bridge.tex).
Those results are only partially formalized: the native transport and
path-realization estimates remain written. The present composition is
also written, not a new Lean endpoint.

**Proof and order of quantifiers.** Fix a target-loss fraction 0<δ<1.
Choose ε,η>0 sufficiently small that

  (k+2)(sεc+η) < (1−δ)/2.

Take the cut Γ_h supplied by the geometric premise at ε. Independently,
[Paper 14, Corollary O(a)](../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/paper/sections/consequences.tex)
supplies a cut Γ_D of cost s|Γ_D|≤ηL and full depth bounded by a constant
D depending on k,s,c,η. Use the **union** Γ=Γ_h∪Γ_D. Enlarging the cut
cannot increase full depth or merge unrevealed components. Every remaining
component still has at most n(ε) output steps; every cut-root output is
handled as a singleton. Put n₀=max(1,n(ε)). All these parameters are fixed
before d tends to infinity.

The native raw cones for Γ have bounded size B=B(k,D). Choose a fixed
reverse-degree threshold M≥B/δ. Paper 5 retains a coordinate set Q of
size at least (1−δ)L with both paired-incidence degrees bounded by
max(B,M). At radius r=2n₀−1, its native theorem says that only
O_{k,D,c,M,n₀}(L/log d) members of Q have paired distance at most r in
the induced graph E_Q. Delete those targets as well. This leaves

  |Q_good| ≥ (1−δ)L − O(L/log d).

Partition their output labels by the unrevealed time components and by
cut-root singletons. Every patch has at most n₀ targets. Any path joining
the two ports of one target inside the patch would have length at most
2n₀−1, contrary to the construction. Paper 5's separated-ports half bound
therefore applies to its induced source-coordinate relation. Fixing the
exterior raw inputs, as in Section 1, costs no extra record bits; the
price already paid here is that only |Q_good| demands are counted.

The boundary-record overlap is at most k+2 by Section 4, including the
cut-root outputs. Summing the local invoices gives

  s(k+2)|Γ| ≥ |Q_good|/2 ≥ (1−δ)L/2 − O(L/log d),
  s|Γ| ≤ sεT + ηL ≤ sεc(L+1) + ηL.

These contradict the strict choice of constants for large d. Correctness
enters only when the actual record provides recovery on the full source
cube. The chosen cuts and views are common to every input because the
schedule is oblivious. The native paired-distance estimate is uniform in
b≥1; thus the written argument includes Boolean as well as canonical-width
entries. It does not automatically extend to adaptive trace fibres. ∎

This answers the separation question precisely. At every fixed radius,
the additional short-pair deletion is o(L) **after** a fixed δL degree
payment and at a fixed-depth cut. The native theorem does not supply an
uncharged o(L) deletion on the original untrimmed relation. If components
already have bounded numbers of time vertices, they supply fixed depth
directly and the auxiliary Γ_D is unnecessary.

**One density and growing components suffice.** The proof uses only one
fixed ε₀ satisfying s(k+2)cε₀<1/2; choose fixed δ,η within that strict
margin. Thus fragmentation at that one density is sufficient. Moreover,
the component-output bound may be n(d)=o(log log d), rather than a constant.
Keep D,B,M fixed as above and put Δ=max(2,B,M) and
a=4c(B+1)(k+2)(k+6). Paper 5's printed finite packing estimate, at
radius 2n−1 with n=max(1,n(d)), gives the short-pair fraction at most

  [(Δ^(2n)−1)/(Δ−1)] · n(n+1)[a(4n−1)/3+3] / log₂ d.

Indeed, its disjoint-path constant is A_j=aj+3 and the odd-length sum is
Σ_(j=1)^n 2j[a(2j−1)+3]=n(n+1)[a(4n−1)/3+3]. The transport proof is
finite for every length: its time grows linearly in that length, occupancy
stays B+1, and no lower-dimension threshold depends on the radius. Hence
the estimate is O(n³Δ^(2n)/log d), which tends to zero when
n=o(log log d). The rest of the same-cut invoice is unchanged. More
generally n³Δ^(2n)=o(log d) is sufficient, but Δ depends on the fixed
depth and degree payments. This strengthening remains written: the
existing Lean asymptotic wrapper fixes the radius, and the native
transport premise itself is only partly formalized.

The premise is on the time diagram, whereas the earlier row-separator
theorem assumes hyperfiniteness of a source/demand row graph. Neither
identification is made here. Paper 15's raw-coordinate patch theorem
supplies the local half bound but not the cheap record cover. For one
work tape, the two-page time graph is planar, and recursive planar
separators give ordinary vertex hyperfiniteness. The composition thus
recovers the known one-work-tape exclusion as a calibration. It claims
no novelty for that exclusion and no new exclusion of arbitrary
multi-tape motion. Expanding time diagrams need not meet the premise.

## 8. Regular sweeps: reuse the existing theorem, repair the grid sketch

The proposed nested-period sweep calculation is not a proved grid
decomposition. There are two concrete defects in its justification.

- Nested periods alone do not align phases. Write tri_a(t) for the
  triangular walk of amplitude a and period 2a. The walks
  x₁(t)=tri₂(t) and x₂(t)=tri₄(t+1)−1 both start at zero, with nested
  periods 4 and 8. Tape 2 has a last-visit edge 4→2, but
  x₁(4)=0 and x₁(2)=2. That reflection does not preserve the fastest
  tape's position.
- Even an aligned single tape has turnaround edges. Positions
  0,1,2,1 at times 0,1,2,3 give the last-visit edge 3→1 and spine
  edges 3→2→1, an undirected triangle. The diagram is not literally
  a nearest-neighbour rectangular grid. For the amplitude-one walk,
  the edges are t→t−1 and t→t−2. A face cut at one stroke index is
  bypassed by the length-two edge. A full-period face instead contains
  two steps, but its final record still has two unrevealed children.
  They can enter the same component; this does not refute a properly
  constructed overlap bound of two.

Thus the claimed face cost (k+1)T/Δ, component size Δ^(k+1), and
one-unrevealed-child explanation need a specified coordinate map,
phase convention and boundary treatment. They are not used in Section 7.
A bounded-range grid embedding with appropriately thick, shifted faces
could be a sufficient repair, but no such proof is asserted here.

No new sweep exclusion is needed: [Paper 4, Theorem C and its preceding
class remark](../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/motion.tex)
already exclude home-based heads with boundedly many affine runs per
excursion. Ordinary constant-speed back-and-forth sweeps belong to that
class, with arbitrary numbers of passes and arbitrary coupling between
heads. Nested periods are unnecessary. That theorem is written, not
Lean-verified; its stronger adaptive scope is not supplied by Section 7.

## 9. Overlapping backward-closed families

Let U_i be backward-closed sets in the unrevealed time DAG. Their cut
in-neighbours T_i suffice for the outputs in U_i; the views are contained
in T_i, not necessarily equal to it. Let F be the set of **all**
unrevealed vertices with a cut predecessor. If m=|Γ|, then |F|≤(k+1)m.
Write mult(v)=#{i:v∈U_i} and let μ be its average over F (zero if F is
empty). Bounded time-vertex degrees give

  Σ_i|T_i| ≤ Σ_{v∈F} deg⁻_Γ(v) mult(v)
            ≤ (k+1)μ|F| ≤ (k+1)²μm.

Adding cut-root singleton outputs costs at most m more record incidences.
So C≤(k+1)²μ+1 is valid with this definition and uniform record widths.
Averaging over every unrevealed vertex instead would not prove it.
The same local-capacity and target-coverage premises are still required;
this count supplies neither small families nor a useful μ for general
native diagrams. It opens no further experiment or front.

## 10. A local cut restatement needs individual causal views

For any set U of native steps, let P_U be its outside predecessors:
v∉U with u→v for some u∈U in the native **backward** dependency DAG.
They are incoming neighbours in the forward information-flow convention.
Let J be the output labels appended in U, S=σ(J), and R_U the raw input
addresses read anywhere in U. For each j∈J, retain its own raw cone
c_U(j): the reads on paths starting at its output root and staying
entirely inside U, including the length-zero path.

The records on P_U and c_U(j) determine output j, by induction through
the internal time vertices. Define cap_U(S) using the individual helpers
c_U(j)∩S. Exterior conditioning as in Section 1 gives

  s|P_U| ≥ |S|−cap_U(S) ≥ |S∖R_U|.

For the second inequality, projection of any such storage code onto
R_U∩S is injective: agreement there implies agreement on every helper
view, hence on every target. Thus cap_U(S)≤|R_U∩S|. If a retained subset
S′ has separated demand ports, the same record satisfies
s|P_U|≥|S′|/2. An arbitrary U does not itself provide the fixed depth
and paid degree premise for the native separation theorem.

If instead every output is given **all** reads R_U, capacity is exactly
|R_U∩S|: let those coordinates vary freely and fix the others. The
capacity invoice then equals the ordinary unread-target count, with no
extra credit. A target read somewhere in the patch is not necessarily
a self-helper in its own causal view. Two targets with helpers {y},{x}
and the parity message x⊕y illustrate strict credit for the individual
views, although the union of reads contains both targets.

[Paper 1's Cut Lemma](../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/paper/sections/locality.tex)
and its [code cut-set bound](../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/paper/sections/codes.tex)
use the unread-target count; Paper 4's M* imports that coarsened
inequality. The finer statement above reuses Section 1 and Paper 5's
index-code fibre bound. [Paper 18, Theorem Q](../../Macroscopic-Information-Transfer-in-Adaptive-Tape-Transposition/paper/sections/transfer.tex)
also already proves a native capacity-deficit invoice for original entry
relations, with its explicit simulator and erosion costs. The local
restatement is therefore reuse, not a new capacity theorem or novelty
claim about adding coding credit to native cuts.
