# Half-rank bounds for sparse recovery

Hans Brende, GPT-6 Astra and Claude Fable 5.2, 14 November 2026.

**Status:** the rank proof and its strengthenings, including the weaker-pattern three-helper
half theorem, the arbitrary-width bound and the affine-code cardinality consequences, are
Lean-verified. The separate nonlinear matching-plus-one-helper Lemma 3 remains written and
independently reviewed. **Reuse correction:** the original asymmetric triangle-free
subcubic theorem, the directed reciprocity form below, and the two-helper special case were
already proved in Paper 4, Theorem S, including in
[`MotionDepthCodes/Subcubic.lean`](../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/lean/MotionDepthCodes/Subcubic.lean).
The initial version of this note overlooked that coverage. Nonzero diagonal reduces to its
unit-diagonal statement by invertible row scaling. The existing memo even gives a matching-number
bound on graph-supported scalar codes.

Hans directed the research. Fable proposed the re-examined target, tested finite instances and
supplied the removal argument. Astra developed the shorter row-order/last-row proof below.
The additions relative to Theorem S are the weaker **four-arc exclusion** and the bound for
**arbitrary outgoing width k**; the new proof does not depend on zero forcing. Paper 10's
Theorem S* already proves the nonlinear all-alphabet half bound under the stronger
no-transitive-triangle hypothesis and the same degree-three reciprocity condition. Our
weaker-pattern extension assumes scalar affine equations. No external literature novelty
claim is made.

## 1. The theorem and its coding consequence

Let F be any field, V a finite index set of size N, and B an F-valued V×V matrix. Its **actual
undirected support graph** has edge {u,v}, for u≠v, exactly when B_uv≠0 or B_vu≠0.

Write u→v when u≠v and B_uv≠0; degrees below count only these off-diagonal entries.

**Theorem A (directed form).** Assume the diagonal is nonzero and the actual undirected support
is triangle-free. Suppose every vertex has at most three outgoing neighbours, and every
one-way arc u→v (so v↛u) has a head v with at most two outgoing neighbours. Then

`2 rank_F(B) ≥ N`, or equivalently `nullity_F(B) ≤ ⌊N/2⌋`.

The one-way condition says that a vertex with three outgoing helpers receives arcs only from
those helpers. Incoming degrees at vertices with fewer helpers are unrestricted.

**Corollary A1 (the original subcubic target).** The same bound holds whenever the actual
undirected support is triangle-free of maximum degree at most three. Indeed, the head of a
one-way arc has a neighbour that is not outgoing, leaving at most two outgoing neighbours.
Opposite entries may be unequal or vanish independently. Matrices supported inside any
specified triangle-free subcubic graph are therefore covered.

**Corollary A2 (two outgoing helpers).** If the actual undirected support is triangle-free and
every row has at most two off-diagonal nonzeros, the bound holds without any incoming-degree
or undirected-degree cap.

Matching blocks, with one isolated nonzero diagonal entry when N is odd, attain the bound over
every field.

**Coding consequence.** Let A⊆F be a finite alphabet of size q and let C⊆A^V satisfy Bx=a for
one fixed vector a, with B as above. Then `|C|≤q^⌊N/2⌋`. The set C need not be a linear subspace:
if nonempty it lies in a translate of ker B, and an information-set projection of that affine
space is injective on C. The empty-code case is immediate. In particular this bounds all codes
with scalar affine recovery equations whose resulting matrix has the stated support and
nonzero-diagonal properties.

The Lean information-set theorem is more general: for any matrix B with N columns, even
with an infinite set of equations, any finite alphabet A with coordinate-dependent embeddings
`e_v : A ↪ F`, and any C⊆A^V satisfying `B(e_v(x_v))=a`,

`|C| ≤ |A|^(N−rank B)`.

Neither the field nor the complete affine fibre need be finite, and C need not be a subspace.
The embedding is a hypothesis: a fixed finite field need not contain every alphabet size.

This reproves the already formalized Target A of the
[literature note](storage-codes-large-girth-literature.md), in every field and at every size. Nonlinear storage capacity on the triangle-free subcubic graphs was already bounded by
Paper 7's Theorem N3. The whole-row question at window three remains separate. Three helper **rows** can contain many helper coordinates;
three outgoing coordinate helpers need not give undirected degree three. A self-helper can also
make the diagonal of a recovery equation vanish. None of these additional native premises is
obtained merely from a cone-size bound.

## 2. A row-order rank certificate

Call a column *new at a row* if that row has a nonzero entry there and every earlier row has zero
there. Nonzero diagonal entries ensure that all N columns are eventually introduced.

**Lemma 1 (last independent row).** Assume the nonzero diagonal and triangle-free support as
above. Suppose the rows have been ordered so that every row after the first has its own
diagonal column already introduced. Select a row greedily whenever it
increases the span of the preceding rows. If rank B≥2, the last selected row introduces at most
one column.

**Proof.** Let v be the last selected row. If distinct columns j,k were new there, all earlier
selected rows would vanish in both columns. Every row is a linear combination of the selected
rows. Since B_jj≠0, the coefficient of row v in the expression for row j is nonzero. Hence
B_jk≠0 as well. Also B_vj and B_vk are nonzero. The own-column premise gives v∉{j,k}, so
v,j,k form a triangle in the actual support graph, a contradiction. ∎

**Lemma 2 (counting introduced columns).** In addition, suppose the first row introduces at most
a columns and every later row introduces at most h. If r=rank B≥2, then

`N ≤ a + h(r−2) + 1`.

**Proof.** A row in the span of its predecessors introduces no column. There are r selected
rows; charge at most a columns to the first, at most h to each intermediate one, and at most
one to the last by Lemma 1. ∎

At h=2, a≤3 gives N≤2r. The case a≤4 gives N≤2r+1 and also suffices when N is even.
If r=1, write B=uvᵀ. Its nonzero diagonal makes every entry of u and v nonzero, so the actual
support graph is complete. Triangle-freeness then gives N≤2, which already proves Theorem A.

The last-row step uses linear dependence of entire rows. The argument does not claim that a
coordinate seed of size ⌊N/2⌋ exists for the single-equation pivot rules.

## 3. A closed-set reduction and the row order

All hypotheses of Theorem A are inherited by principal submatrices. In particular, a vertex
that has three outgoing neighbours after restriction already had exactly those three before
restriction; an incoming one-way arc still cannot enter it.

Suppose a counterexample over a fixed field has the fewest vertices. If a nonempty proper
subset P has no outgoing arc to its complement, ordering P first makes the matrix block
triangular. Nonsingular minors in its two principal blocks combine to give

`rank B ≥ rank B[P,P] + rank B[V∖P,V∖P] ≥ ⌈|P|/2⌉ + ⌈(N−|P|)/2⌉ ≥ ⌈N/2⌉`.

This contradicts minimality. Thus every nonempty proper processed set has an outgoing arc.

If some vertex has outgoing degree at most two, start with its row, which has at most three
nonzero entries. Otherwise all outgoing degrees are three. The one-way condition then forbids
every asymmetric arc, so the undirected graph is cubic and N is even. Start anywhere; the
first row has four nonzero entries.

Grow the processed set by choosing an outgoing arc u→v with u processed and v unprocessed.
Column v has already appeared in row u. If v→u also exists, columns v and u are both old, so
row v adds at most two of its at most four support columns. Otherwise the one-way condition
makes v's outgoing degree at most two: its own column is old, so again at most two columns
are new. In either case its own diagonal column was already introduced. The closed-set
property lets this process continue until every row is ordered.

If rank B≥2, Lemma 2 now gives N≤2r in the first case. In the cubic case it gives N≤2r+1;
N is even, so N≤2r again. The rank-one case was handled separately, and rank zero is impossible
for a nonempty matrix with nonzero diagonal. The empty matrix satisfies the bound. This proves
Theorem A. ∎

**A weaker forbidden-pattern hypothesis.** The proof actually needs only the absence of distinct
v,j,k with arcs v→j, v→k, j→k and k→j. In Lemma 1 the expansion of row k also forces B_kj≠0.
Thus Theorem A and both corollaries remain valid with triangle-freeness replaced by exclusion
of this four-arc configuration. Oriented triangles are allowed. This condition is hereditary,
and a rank-one matrix on at least three vertices violates it. No other step uses triangle-freeness.

**Corollary A3 (arbitrary outgoing width).** For any integer k≥2, nonzero diagonal, outgoing
degree at most k and exclusion of that four-arc configuration imply `k rank B≥N`. No condition
on incoming degrees or one-way heads is needed. To prove this, a smallest counterexample again
has an outgoing arc across every nontrivial cut. Grow the row order along such arcs. The first
row has at most k+1 entries; subsequent rows have their own column already introduced and add
at most k columns. For r≥2, Lemma 2 gives `N≤(k+1)+k(r−2)+1=kr+2−k≤kr`. For r=1, the
forbidden pattern gives N≤2≤k. The same block-triangular reduction handles smaller closed sets.

At k=3 this gives code rate at most 2/3 with arbitrary incoming degrees. Theorem A improves this
to half when its one-way-head premise holds. At larger k the deficit is only 1/k; this does
not supply the common whole-row deficit or the depth-dependent native invoice.

**Sharper reachable form (Lean-verified).** If a chosen vertex reaches all vertices, the
closed-cut induction is unnecessary. For rank at least two the same count gives
`N + k ≤ k rank B + 2`, without assuming k≥2. The Lean hypothesis asks only that every
proper cut containing the chosen vertex have an outgoing arc. It does not ask that the
whole relation be strongly connected. At k≥2 this saves k−2 compared with A3.

**Sharper three-helper form (Lean-verified).** Under the half theorem's degree and one-way-head
premises, the same rooted traversal retains the actual outgoing degree of its root s:
`N + 2 ≤ 2 rank B + outdeg(s)`, provided rank B≥2. A root of degree at most two gives half
directly; a root of degree one saves an additional unit. When every degree is three, all arcs
are reciprocal and the handshaking lemma makes N even, removing the possible extra unit.
The general closed-cut induction then gives the half theorem without any reachability premise.

**Degree-four comparison.** Paper 7's thirteen-vertex degree-four example is triangle-free,
so its scalar F₄ recovery matrix satisfies the four-arc exclusion. A3 gives rank at least
⌈13/4⌉=4, hence dimension at most 9; its seven-dimensional code is consistent with this
bound. The finite rate ceiling here is 9/13 (the coarser uniform ceiling is 3/4). The example's
Lean implementation uses two-bit symbols and 2×2 binary recovery blocks. Four symbol helpers
must not be read as four scalar binary helpers when applying A3.

The one-way-head premise in the half theorem cannot simply be discarded at outgoing degree
three: the existing [seven-vertex Paley code](../PaleyTournament.lean) has four binary dimensions
and no reciprocal edges. It satisfies the four-arc exclusion, but all its one-way arcs enter
vertices with three outgoing helpers.

## 4. A nonlinear subcase: a matching plus one helper

The configuration Fable proposed for a first test admits a stronger, nonlinear result.

**Lemma 3.** Suppose V carries a partial matching. Each matched coordinate is determined by its
mate and at most one further coordinate f(v); each unmatched coordinate is determined by at
most f(v). The partial function f has no self-loop. Then there is a generating coordinate set
of size at most ⌊N/2⌋. Every code with these recovery rules, over any alphabet of size q, has at
most q^⌊N/2⌋ words. The conclusion also holds conditional on fixed boundary data.

**Proof.** For even N, extend the matching to a perfect matching by pairing unmatched vertices.
This only grants additional helpers. The directed cycles of f are disjoint and have length
at least two. Any t of these cycles contain at least 2t vertices and hence meet at least t
matching edges. Hall's theorem assigns each cycle a distinct matching edge touching it.
Choose the endpoint on that cycle as a seed, then choose one endpoint from every remaining
matching edge. This gives N/2 seeds and meets every f-cycle.

An unseeded vertex has a seeded mate. Following f from it reaches a seed or a vertex with no
f-helper, since no f-cycle is wholly unseeded. Recover backwards along that path. For odd N,
add a known dummy vertex and match it to an unmatched vertex, then complete the remaining
matching. Reserve the dummy edge with the dummy chosen. Any t cycles meet at least t other matching edges, since the reserved edge covers at
most one of their at least 2t vertices. The same Hall argument leaves exactly (N−1)/2 actual
seeds. Fixed boundary values simply enter the recovery functions as parameters. ∎

In particular, directed one-way cycles threaded through a reciprocal perfect matching are at
half rate even for nonlinear recovery. Lemma 3 needs neither triangle-freeness, a reverse-degree
bound, nor source independence. The full Theorem A uses linear algebra to handle the mixed
branching configurations that Lemma 3 does not cover.

## 5. Status, reuse and the next gap

Paper 4's `finrank_subCode_le_half` uses `RecTriangleFree` and `Star`. The latter is exactly
the directed reciprocity premise of Theorem A. The former forbids **either** direction between
two outgoing neighbours of a vertex; our proof only forbids a **reciprocal** pair there.
Its graph specialization `rank_ge_half_of_degree_le_three` already covers partial and asymmetric
supports over every field. The shorter proof here is an alternative proof of those endpoints,
not their first verification. The arbitrary-width Corollary A3 is outside their degree hypotheses.
Paper 10's [`IsClassS`](../../Directed-Reciprocity-and-Deep-Nesting-Bounds-for-Matrix-Transposition-on-Tapes/lean/DirectedReciprocity/ClassS.lean)
uses the same reciprocity premise with no transitive triangle and already has a full nonlinear
half-rate decomposition (Theorem 3.6, §3.3). The existing
[`classS_soft`](../../Nested-Elimination-and-Half-Rate-Bounds-for-Storage-Codes/memo-soft-recovery/lean/SoftRecovery/ClassS.lean)
also gives its soft-recovery form. The weaker four-arc exclusion allows a one-way transitive triangle,
so its affine-code extension is not an instance of that theorem.

The [last-row support argument](../../lean-machine/LeanMachine/LastRowSupport.lean) is now
Lean-verified as `subsingleton_of_rows_mem_span_insert`, `card_le_one_of_rows_mem_span_insert`
and `new_columns_subsingleton`. It works over any semiring without zero divisors, with arbitrary
ambient index type and only the displayed columns' diagonal/span hypotheses. The proportional
restriction lemma needs only a semiring. The rank statements remain field statements.
[OrderedRowRank.lean](../../lean-machine/LeanMachine/OrderedRowRank.lean) proves the exact
ordered bound `N≤a+h(rank−2)+1`, including the count of selected rows and the partition of new
columns. [SupportTraversal.lean](../../lean-machine/LeanMachine/SupportTraversal.lean) supplies
an ordering from the root-containing cut condition.
[ClosedCutRank.lean](../../lean-machine/LeanMachine/ClosedCutRank.lean) proves the principal-cut
rank inequality, the rank-at-most-one boundary and a reusable induction principle for hereditary
matrix classes. Both global rank bounds use this induction instead of separate copies.
[SparseRankBounds.lean](../../lean-machine/LeanMachine/SparseRankBounds.lean),
`card_le_mul_rank`, combines them by induction to prove A3 in full; its
`card_add_width_le_mul_rank_add_two_of_cut` proves the sharper reachable form.
The k=2 instance gives half under the weaker four-arc exclusion.
[ThreeHelperRank.lean](../../lean-machine/LeanMachine/ThreeHelperRank.lean),
`card_le_two_mul_rank`, proves the three-helper half theorem under the same weaker exclusion,
including the one-way-head premise and cubic parity step. Its
`card_add_two_le_two_mul_rank_add_root_degree_of_cut` proves the root-degree refinement.
[SparseAffineCodes.lean](../../lean-machine/LeanMachine/SparseAffineCodes.lean) proves the
information-set bound and its half and general-width consequences: for nonempty embedded
alphabets, `|C|≤q^⌊N/2⌋` and `|C|^k≤q^((k−1)N)`, respectively.
Only Lemma 3's nonlinear Hall argument remains unformalized in this note.
Existing scalar half/matching endpoints should be reused rather than reproved merely to
obtain the original statement. Fable's binary census is consistent with the theorem;
neither that census nor a floating-point search is used in the proof.

For the main tape question, the missing step is still a native property with a consumer.
Corollary A1 consumes scalar affine recovery on a triangle-free support of **undirected** degree
at most three; Corollary A2 removes the reverse-degree issue for two outgoing helpers. Neither
turns arbitrary cones into the required non-tautological affine equations or supplies the forbidden-pattern condition. Separately,
Paper 7's `rateBound_n3` already removes linearity on triangle-free subcubic graph supports;
`soft_half` in its soft-recovery memo also charges each center's recovery error once. The
[reuse adapter](../SubcubicReuse.lean) makes the directed-subset consequence explicit. Those
results do not assume the newly weakened four-arc condition alone. Lemma 3 remains a separate
ordinary seed proof for a matching plus one helper, with no triangle-free premise.
