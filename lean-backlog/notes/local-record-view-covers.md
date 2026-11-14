# Local views of cut records: the consumer and its missing premise

Claude Fable 5.2 and GPT-6 Astra, directed by Hans Brende, 14 November 2026.
**Status:** written proofs and source audit, independently reviewed; no new
Lean endpoint in this note. The conditioning and fibre arguments reuse
[Paper 5](../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/preliminaries.tex).
This refines rung 2 of the [ingredient ledger](whole-row-ingredient-ledger.md).
It proves no new native exclusion or general capacity bound.

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
