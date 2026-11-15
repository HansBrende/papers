# Paper 21: what is not formalized, and plans for the next items

Status: a queue kept by Claude Fable, 15 November 2026. Item 1 is done. Statements below are
mathematics; only the file named in item 2 has been typechecked.

| # | Item | Where in the paper | State |
|---|---|---|---|
| 1 | Parities over induced matchings | construction side, proposition | **Lean** (`MatrixCoding/InducedMatchings.lean`), with the stronger range w = o(d^(1/3)) |
| 2 | Known bound: rate at most w/(w+1) | preliminaries, "Known bounds" (cited from the synthesis as written) | statement typechecked: [`StatementsOrderWindow.lean`](../StatementsOrderWindow.lean) |
| 2′ | Known bound: one half at windows one and two | same proposition | written in the synthesis; larger |
| 3 | The three-lane code attaining 119/3 on the Fano relation | entropy section | written; Lean has the bound and an attaining polymatroid |
| 4 | From a graph split into induced matchings to a whole-row code | remark on growing windows | written in the remark |
| 5 | Mixing relations exist | order section | written, reviewed |
| 6 | Mixing lifts of the Fano relation exist | entropy section | written, reviewed; not worth formalizing now |
| 7 | Runs that a cheap cut splits | construction side | written, reviewed; rests on the fifth paper's written transport estimate |

## Item 2: plan

**Statement.** For finite row and column types R, J and ρ : J → Finset R with all |ρ(j)| ≤ w, some
row order o has (w+1)·cost ρ o ≤ w·|J|·(|R|+1). Hence the same for `minimumCost`, and by
`exact_acyclic_card` an acyclic set of at least |R||J| − w|J|(|R|+1)/(w+1) cells.

**Proof by induction on |R|, choosing the last row.** No averaging over orders is needed.
- Let ℓ(r) = #{j : r ∈ ρ(j)}. Since Σ_r ℓ(r) = Σ_j |ρ(j)| ≤ w|J|, the row r with least ℓ has
  |R|·ℓ(r) ≤ w|J|.
- Put r last. A column with r ∈ ρ(j) has last helper position |R| (one-based) and contributes |R|
  to the cost. The other columns J′ = {j : r ∉ ρ(j)} have all their helpers in R′ = R ∖ {r}, and
  their contribution is the cost of the restricted map ρ′ : J′ → Finset R′ under the restricted
  order.
- Induction on (R′, J′, ρ′): (w+1)·cost′ ≤ w·|J′|·|R|, because |R′| + 1 = |R|.
- Total: (w+1)·cost = (w+1)·ℓ·|R| + (w+1)·cost′ ≤ (w+1)ℓ|R| + w(|J| − ℓ)|R| = ℓ|R| + w|J||R|
  ≤ w|J| + w|J||R| = w|J|(|R|+1).
- Base: R empty gives cost 0.

**Where the Lean work is.** Extending an order on the subtype R′ by one last element, as an
equivalence with `Fin (Fintype.card R)`. If that is awkward, two alternatives: (a) state the
induction for injective position functions into ℕ and convert once at the end; (b) build the
acyclic set directly, with a rank function (`rank_iff_acyclic`): the cells (r, j) with r ∉ ρ(j)
get the top rank, and then use `exact_acyclic_card`.

**For codes.** The bound on codes also needs "a whole-row code has at most q^(cost ρ o) elements"
for the predicate `IsWholeRowCodeExcept`. If that is not yet a named theorem, it is the second
half of this item: it is the acyclic-set bound for storage codes on `rowHelpers ρ`.

## Item 3: plan

The code: every non-incident entry of the 7 × 7 Fano array carries three lanes (alphabet A³), one
for each of the three mutual triangles through it; in each of the 28 triangles the three lane
values sum to zero. Incident entries are free. Count: 28·2 + 21·3 = 119 free lane values. The
finite facts to check by `decide` or a small enumeration: there are 28 triangles, each
non-incident entry lies in exactly three, and within a triangle the other two entries of a
column's entry lie in helper rows of that column. Then recovery and the count are the
disjoint-sums lemma already used for item 1, applied lane by lane.

## Item 4: plan

For a simple graph G on [d] with a partition of its edges into induced matchings, put
ρ(j) = {j} ∪ {non-neighbours of j}. Each matching, with every edge taken in both orders, is one
induced matching in the sense of item 1: for the two orders of one edge use j ∈ ρ(j); for
different edges use that the matching is induced. So the hypotheses of item 1's structure hold
with one part per matching, and its cardinality theorem gives codimension equal to the number of
matchings. The existence of the graphs themselves stays cited.
