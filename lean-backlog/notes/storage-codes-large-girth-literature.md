# Storage codes at large girth: literature leads and a subcubic rank target

Status: literature survey by Claude Fable (through a web-search subagent, abstracts and HTML pages
only; no paper was read in full), 14 November 2026. Astra's subsequent scope audit and primary-source
check of Gentner–Rautenbach's Theorem 4 are in Sections 2–3. Tags: [H] read on an abstract or HTML page,
[S] search snippet only, [I] my inference. Statements tagged [S] or [I] must be checked against the
papers before any use. Section 3 is a written, independently reviewed audit; not Lean-verified.

**Reuse audit (14 November): both original targets were already proved in this repository.**
Paper 4's Theorem S proves A over every field, including asymmetric support. Paper 7's
Theorem N3 proves B for **every** finite triangle-free subcubic graph, as the weighted
polymatroid inequality `2h(V)≤Σh({v})`; its soft-recovery memo also proves the coefficient-one
error version. See [SubcubicReuse.lean](../SubcubicReuse.lean) for the short composition and
asymmetric-helper adapter. The conjectural wording and proposed finite searches in C91–C95
missed these results. No new experiment is needed to establish either target.

The [new rank proof](subcubic-half-rank.md) still contributes a shorter argument and the weaker
four-arc/arbitrary-outgoing-width extensions. Its local span lemma, exact rank count, traversal and
closed-cut adapters, the full arbitrary-width rank bound and the three-helper half theorem
under the weakened pattern are now Lean-verified, with finite-alphabet affine-cardinality
wrappers. Paper 10's Theorem S* already covers nonlinear recovery under the stronger
no-transitive-triangle premise; the weaker-pattern extension here still assumes affine equations.

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

## 2. Scope after the repository audit

- The external survey did not identify the degree-three theorem, but Paper 7 already settles
  the entire triangle-free subcubic capacity problem, including nonlinear codes. The finite
  counterexample/certificate passes were therefore redundant for those original targets.
- This is a coordinate-graph theorem. It does not settle the whole-row host at window three:
  those cells may have many coordinate helpers, and even the mutual cell graph on a cubic
  incidence host can have degree nine.
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

**Target A (abstract, linear; already Lean-verified in Paper 4, Theorem S).** Let B be n×n with B_ii≠0 over any field. Suppose
the undirected graph with edge {i,j}, for i≠j, exactly when B_ij≠0 or B_ji≠0 is triangle-free and has
maximum degree at most three. Then nullity(B)≤⌊n/2⌋, allowing asymmetric zeros.
The [new proof](subcubic-half-rank.md) uses the last independent row of a support-respecting
row order. The initial audit missed Paper 4's existing proof of the original and directed
reciprocity forms, including two outgoing helpers. Its genuinely weaker four-arc hypothesis
and arbitrary-outgoing-width bound are new relative to those declarations. The latter is now
fully formalized, as are the three-helper half extension under the weakened pattern and its
affine-code cardinality consequence. These are coordinate degrees, not whole-row windows.

**Target B (abstract, nonlinear; already Lean-verified in Paper 7, Theorem N3).** Every finite
triangle-free graph G of maximum degree at most three satisfies the weighted Shannon bound
`2h(V)≤Σ_v h({v})` for every polymatroid valid on its neighbourhoods. In particular,
`|C|²≤q^n` for every q-ary code, linear or nonlinear. Helpers may be any directed subsets of
those neighbourhoods. The theorem is exact, not merely asymptotic or experimental.

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

## 5. The nonlinear and soft targets: reuse, not a new certificate search

The C95 floating-point LP pass reported value 5 for two ten-vertex inputs and 6 for seventeen
twelve-vertex inputs. Its graph manifest was not saved, so the census/completeness claim is not
independently reproduced. More importantly, the following existing proofs already decide all
these instances and the full class:

- Paper 4, [`Petersen.lean`](../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/lean/MotionDepthCodes/Petersen.lean),
  `rateBound_petersen`: an exact weighted Shannon certificate, with 58 elemental terms.
- Paper 4, [`Pentagon.lean`](../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/lean/MotionDepthCodes/Pentagon.lean): the five-cycle weighted half bound.
- Paper 7, [`N3.lean`](../../Nested-Elimination-and-Half-Rate-Bounds-for-Storage-Codes/lean/HalfRate/N3.lean),
  `n3_decomp`, `rateBound_n3`, `card_sq_le_n3`: the general triangle-free subcubic theorem.
- Its [`SoftRecovery/Decomposition.lean`](../../Nested-Elimination-and-Half-Rate-Bounds-for-Storage-Codes/memo-soft-recovery/lean/SoftRecovery/Decomposition.lean),
  `soft_half`: for any polymatroid, with no exact recovery premise,

  `2h(V) ≤ Σ_v h({v}) + Σ_v [h(N_v ∪ {v}) − h(N_v)]`.

The last statement follows on subcubic hosts by using `n3_decomp`; for smaller, possibly
asymmetric helper sets, diminishing returns only enlarges the error term. The
[reuse adapter](../SubcubicReuse.lean) exposes this composition. This is the soft upper bound
`c_Sh≤2`. For the symmetric neighbourhood relation of a graph with an edge, a paired-edge
code attains 2; arbitrary directed subsets retain only the upper bound. No source symmetry, linearity,
or unit singleton cap is assumed.

**The existing general mechanism.** Remove a shortest cycle of the remaining graph. It is
chordless. If an outside vertex meets two cycle vertices, shortestness forces a four-cycle
with those two vertices opposite. Degree three leaves at most one outside neighbour per cycle
vertex. Three records and a supplying-colour rule make the outside parents private, with
opposite four-cycle vertices co-supplied. The acyclic remainder uses two records. The nested
elimination theorem combines the pieces; its soft version charges each recovery error once.
This is already the general seed/uncrossing pattern sought in C95.

The new finite LPs were stopped before a solve. Unit-cap half alone would not imply the
weighted statement on a nontransitive graph; the weighted exact-recovery statement alone would
not justify a coefficient-one soft inequality. Here both stronger statements are justified by
the cited existing Lean proofs, not by those numerical values. Large girth alone also does not
fix an order bound near 0.555n: bipartite cubic graphs of arbitrarily large girth have order n/2.

The genuine remaining work is the weaker directed four-arc rank extension and, on the machine
side, an extraction of hypotheses that these existing coding bounds consume. Neither the
coordinate degree nor the private-parent condition is supplied by a whole-row window bound.
