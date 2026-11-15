# Paper 21: what is not formalized, and plans for the next items

Status: 15 November 2026. Items 1 and 2, including the window-one upper bound, are proved in Lean.
The remaining plans below are written mathematics.

| # | Item | Where in the paper | State |
|---|---|---|---|
| 1 | Parities over induced matchings | construction side, proposition | **Lean** (`MatrixCoding/InducedMatchings.lean`), with the stronger range w = o(d^(1/3)) |
| 2 | Known bound: rate at most w/(w+1) | preliminaries, "Known bounds" | **Lean** (`MatrixCoding/KnownBounds.lean`); the former target [`StatementsOrderWindow.lean`](../StatementsOrderWindow.lean) is a compatibility import of the shared proof |
| 2′ | Known bound: one half at windows one and two | same proposition | Window-one upper bound is **Lean**; the sharper window-two upper bound remains the synthesis's written multigraph-ranking argument |
| 3 | The three-lane code attaining 119/3 on the Fano relation | entropy section | written; Lean has the bound and an attaining polymatroid |
| 4 | From a graph split into induced matchings to a whole-row code | remark on growing windows | written in the remark |
| 5 | Mixing relations exist | order section | written, reviewed |
| 6 | Mixing lifts of the Fano relation exist | entropy section | written, reviewed; not worth formalizing now |
| 7 | Runs that a cheap cut splits | construction side | written, reviewed; rests on the fifth paper's written transport estimate |

## Item 2: completed

**Statement.** For finite row and column types R, J and ρ : J → Finset R with all |ρ(j)| ≤ w, some
row order o has (w+1)·cost ρ o ≤ w·|J|·(|R|+1). Hence the same for `minimumCost`, and by
`exact_acyclic_card` an acyclic set of at least |R||J| − w|J|(|R|+1)/(w+1) cells.

**Proof.** The shared [OrderAverage](../../lean-machine/LeanMachine/WholeRow/OrderAverage.lean)
uses finite counting over row orders: label swaps make each member of a finite set equally
likely to be last. It retains the stronger numerator w|R||J| + Σ_j|ρ(j)| and includes empty
arrays and empty helper sets. The original target names remain available, without an admitted proof.

**For codes.** [OrderCode](../../lean-machine/LeanMachine/WholeRow/OrderCode.lean) proves
the bound q^(cost ρ o) by well-founded recovery and restriction to the complementary cells.
[KnownBounds](../../Tape-Transposition-and-the-Matrix-Coding-Conjecture/lean/MatrixCoding/KnownBounds.lean)
uses `IsWholeRowCodeExcept` and proves |C|^(w+1) ≤ q^(wd(d+1)), the real-exponent version,
the window-one bound q^(d(d+1)/2), and the limiting rate uniformly over finite alphabets.
The optional window-two improvement is not included.

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
