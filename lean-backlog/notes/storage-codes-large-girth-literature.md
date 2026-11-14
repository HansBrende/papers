# Storage codes at large girth: literature leads and a subcubic rank target

Status: literature survey by Claude Fable (through a web-search subagent, abstracts and HTML pages
only; no paper was read in full), 14 November 2026. Astra's subsequent scope audit and primary-source
check of Gentner–Rautenbach's Theorem 4 are in Sections 2–3. Tags: [H] read on an abstract or HTML page,
[S] search snippet only, [I] my inference. Statements tagged [S] or [I] must be checked against the
papers before any use. Section 3 is a written, independently reviewed audit; not Lean-verified.

**Update:** Target A is now proved over every field by the self-contained
[sparse-recovery rank theorem](subcubic-half-rank.md), with directed strengthenings. The finite
searches below are historical calibration and are not used in that proof. Target B remains open
in this project; its literature status is not asserted by this survey.

A *storage code* on a graph is a set of words in which every coordinate is a function of its
neighbours' coordinates (guessing games, index coding with symmetric side information). Pairing on a
perfect matching gives rate 1/2; the linear capacity is n minus the minimum rank of a matrix with
nonzero diagonal supported on the edges, over the specified field. Graphs here are loopless.
Whole-row window w is a different parameter: a cell may read wd cells, or more bit coordinates
with lanes. A degree-w graph is a comparison problem, not an automatic whole-row reduction.

## 1. Findings

**No theorem, conjecture or refutation was found for "bounded degree and girth → ∞ implies capacity
n/2 + o(n)".**

- *Degree two.* Odd cycles have capacity n/2 (Christofides–Markström, EJC 2011 [S];
  Blasiak–Kleinberg–Lubetzky, arXiv:1004.1379 [S]; exact values in Atkins–Rombach–Skerman,
  arXiv:1602.03586 [S]).
- *Triangle-free is not enough.* Cameron–Dang–Riis, arXiv:1410.2405 [H]: Clebsch (degree 5, girth 4)
  has 10 ≤ capacity ≤ 11 of 16; Hoffman–Singleton (degree 7, girth 5) has capacity ≥ 29 of 50 by a
  linear code over F₅; Higman–Sims ≥ 77 of 100. The conjecture that the clique-cover value is exact
  for triangle-free graphs is therefore false. Families with rate → 1 on triangle-free graphs
  (Barg–Zémor arXiv:2110.02378; Barg–Schwartz–Yohananov arXiv:2212.12117; Huang–Xiang
  arXiv:2301.01668) [H] all have growing degree, and are Cayley graphs of F₂^r [I], so contain
  four-cycles.
- *Large odd girth is not enough.* Golovnev–Haviv, arXiv:2002.08580 [H]: for every odd ℓ there are
  graphs with no odd cycle of length ≤ ℓ and minrank n^{1−δ} over every finite field.
- *Four-cycle-free gives a linear bound over ℝ only.* Codenotti–Pudlák–Resta, TCS 2000 [H, via
  Haviv arXiv:1806.00638]: C₄-free graphs have real minrank above n/6; triangle-free graphs with
  minrank O(n^{3/4}) exist.
- *Small graphs.* Baber–Christofides–Dang–Riis–Vaughan, arXiv:1410.8349 [H]: a floating-point search
  found the Shannon bound equal to the clique-cover value on all graphs with at most 10 vertices
  except two. For triangle-free graphs the clique-cover value is the fractional matching number, at
  most n/2 [I]; so Petersen has capacity 5 although n − α = 6 [I].
- *Entropy arguments beyond n − α.* Mazumdar–McGregor–Vorotnikova, arXiv:1706.09197 [H], for all
  alphabets and nonlinear codes: if V = X ⊔ Y with both induced graphs bipartite and both boundary
  sets independent, capacity ≤ n/2; a cycle with chords whose ends are at least four apart has
  capacity n/2.
- *Zero forcing.* The survey found no explicit use for index or storage codes. For an exact
  reciprocal off-diagonal pattern G, nullity is at most Z(G), even with unequal coefficients in
  the two directions. Gentner–Rautenbach's stronger maximum-degree theorem and its exceptions
  are checked below. Random cubic bounds reported by the original survey remain a literature
  lead (Bal et al., arXiv:1812.06477 [H]), not a bound for arbitrary partial support inside a host.
- *Product structure.* Nothing on the swapped tensor square (p,c) ~ (q,m) iff q ~ c and m ~ p.
  Nearest: Cameron–Dang–Riis's blow-up lemma gn(G(t), s) = t·gn(G, s^t) [H].

## 2. What this says about our open case

- This survey did not settle the abstract degree-three capacity problem. That is not a proof of
  literature novelty or openness. The explicit examples above one half cited here have degree
  at least five; the exact reciprocal linear subcubic slice is already bounded by one half.
- Any purported half-rate bound covering all those abstract degree-five or degree-seven graphs
  is false. A more restricted proof may use degree three, large girth, or the array structure.
- A perfect matching supplies n/2 symbols; without one this lower bound needs another argument.
  The independence bound is capacity ≤ n−α. The original survey's numerical large-girth estimate
  needs its hypotheses and citation checked before use. Neither estimate transfers from graph
  degree three to whole-row window three.

## 3. What forcing adds, and what remains to test

For a matrix B over any field, write S_i={j:B_ij≠0}. Every pivot j∈S_i supplies the valid rule
S_i∖{j}→j on ker B. One-unknown equation propagation is **exactly closure with all these rules**.
The [assigned-rule argument](transported-closure-native-audit.md) applies to this expanded
multi-option system too. It may improve on the original diagonal recovery rules; it is not by
itself a way around the closure barrier. Combining equations or proving rank directly could add
information not captured by these single-equation pivots.

**Known reciprocal slice.** [Gentner and Rautenbach, *Some Bounds on the Zero Forcing Number of
a Graph*, arXiv:1608.00747v1, Theorem 4](https://arxiv.org/pdf/1608.00747) gives
Z(G)≤((Δ−2)/(Δ−1))n for connected maximum degree Δ≥3, apart from K_{Δ+1}, K_{Δ,Δ},
K_{Δ−1,Δ} and two displayed graphs containing triangles. This bounds nullity over every field
when every edge is present in both directions; the coefficients need not be equal. For triangle-free
subcubic patterns the remaining exceptions K_{2,3}, K_{3,3} are bipartite, so a diagonal principal
submatrix on a larger independent part gives rank at least half. Paths, cycles of length at least
four and isolated vertices are elementary. Thus every exact reciprocal triangle-free subcubic
pattern with nonzero diagonal has nullity at most ⌊n/2⌋. No new theorem is needed for this slice.

**Host versus actual support.** Z(G) does not bound every matrix merely supported inside G.
On the twelve-vertex hexagonal prism, two adjacent rungs form a zero-forcing set of size four.
The matrix B=I−P, where P exchanges the endpoints of each vertical rung, has nullity six over
every field and is supported inside that prism. Its actual graph is just a matching. Also, for
asymmetric support, a force along an edge of the undirected union may use a zero coefficient.

**Target A (abstract, linear; proved, written and independently reviewed).** Let B be n×n with B_ii≠0 over any field. Suppose
the undirected graph with edge {i,j}, for i≠j, exactly when B_ij≠0 or B_ji≠0 is triangle-free and has
maximum degree at most three. Then nullity(B)≤⌊n/2⌋, allowing asymmetric zeros.
The [proof](subcubic-half-rank.md) uses the last independent row of a support-respecting row order;
it does not assert a small all-pivot generating seed. It also gives half for two outgoing helpers
with no incoming-degree cap, and two-thirds for three outgoing helpers, under the stated weaker
four-arc exclusion. These are coordinate degrees, not whole-row windows. Not yet Lean-verified.

**Target B (abstract, nonlinear; conjectural).** Does every loopless triangle-free graph of maximum
degree at most three have storage capacity at most n/2? The small-graph and cycle results above
are leads; no exhaustive literature claim is made here.

**Target C (arrays/native application; conditional).** Apply A after obtaining scalar affine
equations, valid on the counted fibre, with nonzero diagonal and the stated triangle-free
**actual undirected** support. The fibre need not itself be a linear subspace.
A cone of size three supplies only an outgoing-helper bound. It supplies neither these additional
graph conditions nor linearity; a self-helper may make its diagonal equation tautological.
No extraction of the required premises from a native schedule is proved here.

Thus the proposed abstract low-degree linear counterexample is ruled out. A native use still
needs these additional support and recovery premises; the common whole-row deficit remains open.

## 4. First step on Target A: peeling

Fable's removal/peeling argument, independently reviewed by Astra, 14 November.
Written, not Lean. The support and closure qualifications below are part of the statement.

Write u → w when B_uw ≠ 0 (u ≠ w), N⁺ for out-neighbourhoods, N⁻ for in-neighbourhoods.

**Lemma (removal).** Let T⊆U be vertex sets with N⁺(T)⊆U. Then
rank(B) ≥ rank(B − U) + rank(B[T, U]), where B − U deletes the rows and columns of U. The same holds
with columns: N⁻(T)⊆U and rank(B[U, T]).

*Proof.* Choose nonsingular minors of sizes rank(B−U) in B−U and rank(B[T,U]) in
B[T,U]. Their rows and columns are disjoint. Combining them gives an upper block-triangular
minor: its lower-left block is zero because N⁺(T)⊆U. Its determinant is the product of the two
nonzero determinants. The column version follows by transposition. ∎

**Corollary (peeling).** If I is an independent set of the support graph, then B[I, I] is diagonal
and nonsingular. With U = I ∪ N⁺(I) the lemma gives nullity(B) ≤ nullity(B − U) + |N⁺(I)|. Hence, by
induction on n: **if every nonempty induced sub-pattern has a nonempty independent set I with |N⁺(I)| ≤ |I|
or |N⁻(I)| ≤ |I|, then nullity(B) ≤ n/2.** No degree or girth condition is used.

At each stage a vertex of out-degree or in-degree at most one is peelable (I a singleton).
The hereditary criterion covers bipartite graphs (I the larger side), forests and functional
digraphs. Outgoing peeling is also original-rule closure: seed N⁺(I), recover I, then use a seed
for the conditioned remainder. Incoming peeling uses the transposed rank argument. Removing a
mutual pair at price one does not distinguish this method from closure.

**Earlier reduction, now subsumed by the proof of A.** A smallest counterexample would have every nonempty independent set expand
strictly in both directions. In particular every vertex has out-degree and in-degree at least
two among at most three neighbours, and hence a reciprocal edge. The final proof uses a simpler
closed-row-set reduction and resolves the residual case; this peeling lemma remains reusable.

**A sharp control over every field.** The exact Petersen pattern has strict independent-set
expansion in both directions. If A is its adjacency matrix, A−I has nullity exactly five.
Order outer pentagon before inner star, and let P be the five-cycle permutation matrix. Put
C=P+P⁻¹−I and D=P²+P⁻²−I. Since P⁵=I, CD=DC=I over the integers, and

`A−I = [[C,I],[I,D]] = [[I],[D]] [C,I]`.

The factorization gives rank at most five and the off-diagonal identity gives rank at least five,
over every field. Its kernel has no nonzero word supported on two coordinates, so it is not an
orbit-constant pairing code. This is a sharp control for the proved rank bound.

## Historical counterexample pass (Fable, 14 November)

Statement tested: B has nonzero diagonal, its undirected off-diagonal union is triangle-free of
maximum degree three, asymmetric zeros are allowed; then nullity(B) ≤ ⌊n/2⌋. Equivalently the
index-coding minrank of the graph is at least n/2. Graphs: connected, triangle-free, non-bipartite
cubic graphs, sampled as random regular graphs and deduplicated up to isomorphism.
Scripts: [minrank_f2.py](../tools/host-probe/minrank_f2.py),
[minrank_cubic.py](../tools/host-probe/minrank_cubic.py).

| n | graphs | exact over F₂: rank ≤ n/2 − 1 exists | real field, heuristic: converged at rank n/2 − 1 |
|---|---|---|---|
| 10 | Petersen and one of girth 4 | none | none |
| 12 | 17 reported | none | none |
| 14 | 30 exact, 97 heuristic | none | none |
| 16 | 60 heuristic | not run | none |

- The F₂ test is exhaustive for each graph: depth-first search over all rows with unit diagonal and
  support in the neighbourhood, a maximum independent set first, pruned by rank. Rank n/2 exists on
  every graph tested.
- The real test is alternating least squares at rank n/2 − 1 with rank n/2 as control. It never
  converged below n/2 (errors near 3·10⁻³, often with growing entries); the control converged to
  machine precision except once at n = 16. It is a search, not a proof.
- No counterexample. Nothing was tested over F₃ or larger fields, on non-regular subcubic graphs,
  or beyond 16 vertices.

**Reproduction audit.** The binary DFS is exhaustive for each supplied labelled graph; ordering
independent rows first and pruning by rank are sound. The reported graph list and run logs were
not saved, so the census table and its completeness are not independently reproduced here.
The sampling routine deduplicates its sample, but the separately prepended Petersen graph can
duplicate a sampled graph. Preserve graph identifiers, commands and versions for a future census;
no rerun is needed to establish A now that the all-field proof is available.

## Target B, first evidence: the Shannon bound is exactly n/2 on every small case (Fable, 14 November)

Status: floating-point LP values (HiGHS), one hand proof, no general proof. Scripts:
[shannon_graph.py](../tools/host-probe/shannon_graph.py) (all 2^n subsets, all elemental
inequalities, so the optimum is the full Shannon bound),
[petersen_certificate.py](../tools/host-probe/petersen_certificate.py).

| graphs | n − α (order bound) | Shannon bound | n/2 |
|---|---:|---:|---:|
| Petersen, and one cubic graph of girth 4 on 10 vertices | 6 | 5.000000 | 5 |
| all 17 connected triangle-free non-bipartite cubic graphs on 12 vertices | 7 | 6.000000 each | 6 |

So on every triangle-free cubic graph with at most 12 vertices the Shannon inequalities alone give
rate one half for arbitrary nonlinear codes, strictly below the order bound. In the soft language:
the statement "2H(X) ≤ Σ_v H(X_v) for every storage code" is c_Sh = 2, and it holds on all these
graphs. (For n ≤ 10 this agrees with the floating-point search of Baber et al.)

**The five-cycle by hand.** Vertices 1..5 in cyclic order, each a function of its two neighbours.
The closures of {1,3} and {2,4} are {1,2,3} and {2,3,4}; their union generates everything and they
meet in the edge {2,3}. So h(1,3) + h(2,4) ≥ H + h(2,3). And {2,3,5} generates, so
h(2,3) + h(5) ≥ H. Adding: **2H ≤ h(1,3) + h(2,4) + h(5) ≤ 5.** The seeds {1,3}, {2,4}, {5}
partition the vertices; the gain over order comes from an edge appearing as the intersection of two
closures.

**Petersen.** Reduced by its 120 automorphisms the LP has 34 subset orbits and 148 distinct
inequalities; dual simplex returns value 5 with 19 nonzero multipliers (printed by the script).
It is a certificate in floating point, not yet an exact or readable proof.

**Conjecture (Target B, Shannon form).** For every triangle-free graph of maximum degree three,
every polymatroid with the recovery equalities satisfies 2h(V) ≤ Σ_v h({v}). With the linear
theorem (rank at least ⌈N/2⌉ over every field) this would make degree three the first case where
one half is proved for all codes on a family on which the order bound fails: for cubic graphs of
large girth the order bound is about 0.555n.
