# Half-rank bounds for sparse recovery

Hans Brende, GPT-6 Astra and Claude Fable 5.2, 14 November 2026.

**Status:** written proofs, independently reviewed; not Lean-verified. Hans directed the
research. Fable proposed the asymmetric target, tested finite instances and supplied the removal
argument. Astra developed the row traversal, final-basis-row argument and directed strengthening below. The reciprocal
case was already known from zero forcing; the proof here is self-contained. No literature novelty
claim is made for the asymmetric case.

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

This settles Target A of the [literature note](storage-codes-large-girth-literature.md), in every
field and at every size. It does not settle nonlinear storage capacity on these graphs, or the
whole-row question at window three. Three helper **rows** can contain many helper coordinates;
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

The earlier exact reciprocal-support half bound follows from
[Gentner–Rautenbach, Theorem 4](https://arxiv.org/pdf/1608.00747) and elementary exceptional cases.
Theorem A covers arbitrary partial and asymmetric subcubic supports, as well as Corollary A2, and uses none of that
theorem as a dependency. Fable's binary census is consistent with it; neither the census nor a
floating-point search is used in the proof.

The proof is a formalization target: finite row spaces, rank increments, support traversal and
elementary graph reductions. Existing removal/rank and finite graph APIs should be reused;
no arithmetic geometry or analytic machinery is needed. Until that work is complete, this
remains a written theorem, not a Lean theorem.

For the main tape question, the missing step is still a native property with a consumer.
Corollary A1 consumes scalar affine recovery on a triangle-free support of **undirected** degree
at most three; Corollary A2 removes the reverse-degree issue for two outgoing helpers. Neither
turns arbitrary cones into the required non-tautological affine equations or supplies the forbidden-pattern condition. Separately,
removing linearity from the full subcubic statement remains a concrete question; Lemma 3
settles one subcase without suggesting that arbitrary nonlinear rules have a row-space basis.
