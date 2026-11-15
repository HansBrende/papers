# Paper 21: what is not formalized, and plans for the next items

Status: 15 November 2026. Items 1–4, including both window-one and window-two bounds, are proved in Lean.
The three remaining items are written mathematics.

| # | Item | Where in the paper | State |
|---|---|---|---|
| 1 | Parities over induced matchings | construction side, proposition | **Lean** (`MatrixCoding/InducedMatchings.lean`), with the stronger range w = o(d^(1/3)) |
| 2 | Known bound: rate at most w/(w+1) | preliminaries, "Known bounds" | **Lean** (`MatrixCoding/KnownBounds.lean`); the former target [`StatementsOrderWindow.lean`](../StatementsOrderWindow.lean) is a compatibility import of the shared proof |
| 2′ | Known bound: one half at windows one and two | same proposition | **Lean**: shared `WholeRow/WindowTwo.lean` proves the rectangular induction; `KnownBounds.lean` gives the code bound and an alphabet-uniform threshold. The original target is a compatibility import |
| 3 | The three-lane code attaining 119/3 on the Fano relation | entropy section, Theorem E(a) | **Lean** (`MatrixCoding/FanoLaneCode.lean`): exact cardinality, whole-row recovery and optimality over every finite abelian base alphabet; arbitrary prescribed triangle sums |
| 4 | From a graph split into induced matchings to a whole-row code | remark on growing windows | **Lean** (`MatrixCoding/GraphMatchingCode.lean`): exact size and recovery over finite abelian groups, graph-degree window, and exact linear codimension over every field; graph existence remains cited |
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
The window-two improvement and the symmetric-array lower witness are now included as item 2′.

## Item 2′ (window two): completed

**Proof:** [WindowTwo](../../lean-machine/LeanMachine/WholeRow/WindowTwo.lean).
The original [`StatementsWindowTwo.lean`](../StatementsWindowTwo.lean) is a compatibility import, with no
admitted proof. Both `exists_cost_window_two_le` and its square specialization are checked.

**Statement.** For ρ : J → Finset R with all |ρ(j)| ≤ 2, some row order has cost at most
g(n, m), where n = |R|, m = |J| and

    g(n, m) = n(n+1)/2 − (n − m)              if m < n,
    g(n, m) = n(n+1)/2 + n(m − n) + (n − 1)   if m ≥ n.

For m = n = d this is d(d+1)/2 + d − 1. `OrderCode.card_le_window_two` combines the order theorem
with `card_le_order`. The paper adapter proves this code bound, the threshold d ≥ 3n for
|C|^(2n) ≤ q^((n+1)d²), and the limiting half-rate uniformly over all finite alphabets.
The shared [SymmetricCode](../../lean-machine/LeanMachine/WholeRow/SymmetricCode.lean) supplies an exact
q^(d(d+1)/2) lower witness over every finite alphabet, with no group structure. The "Known bounds"
proposition is fully formal.

**Why this closed form.** The synthesis proves the square case with a potential that is not a
closed formula. The function g is an invariant of the same greedy step, so the proof is one
induction on n with integer arithmetic. It was checked by exhaustive enumeration for n ≤ 5 and
is attained at m = n and m = n − 1.

**Induction step (n ≥ 2).** Let ℓ(r) = #{j : r ∈ ρ(j)}; Σ_r ℓ(r) ≤ 2m, so the row r with least ℓ
has n·δ ≤ 2m for δ = ℓ(r). Put r last: the δ columns helped by r cost n each; the other m − δ
columns have all helpers among the remaining n − 1 rows. So cost ≤ n·δ + g(n − 1, m − δ), and it
remains to check n·δ + g(n − 1, m − δ) ≤ g(n, m):
- m < n: then δ ≤ 1. For δ = 1 there is equality. For δ = 0 it is g(n − 1, m) ≤ g(n, m), in both
  sub-cases m < n − 1 and m = n − 1.
- m ≥ n, with ε = m − n: then δ ≤ ε + 2 (from n·δ ≤ 2m and n ≥ 2). If δ ≤ ε + 1 the second branch
  of g applies to (n − 1, m − δ) and the inequality reduces to δ ≤ ε + 2. If δ = ε + 2 then
  m − δ = n − 2 < n − 1, the first branch applies, and there is equality.
- Base: n = 0 gives cost 0; n = 1 gives cost at most m = g(1, m) for m ≥ 1, and 0 for m = 0.

**Lean implementation.** The numerical recurrence is `windowTwoBound_step`. Strong induction on
the row count uses injective numberings on arbitrary finite row and column types, deleting the
least-used row and its incident columns. A final conversion gives a row-order equivalence.
The zero-row and one-row cases and empty helper sets are included.

## Item 3: completed

[FanoLaneCode](../../Tape-Transposition-and-the-Matrix-Coding-Conjecture/lean/MatrixCoding/FanoLaneCode.lean)
reuses `FanoAttainment.triangle` and `triangle_mutual`, checks that each residual cell lies in
three triangles, and assigns those triangles bijectively to its three lanes. The resulting
28 supports are nonempty and pairwise disjoint on all 147 scalar coordinates. The shared
`DisjointSums.fiber_card` gives exactly |A|^119 codewords over A³, for any finite abelian group A
and any prescribed triangle sums. The zero-sum code is the construction in Theorem E.

`mem_code_iff` identifies precisely the triangle equations, `update_incident` leaves every
incident entry free, and `isWholeRowCode` uses the actual Fano helper map. `optimal` combines
this construction with the existing upper bound; `exists_code_for_cardinality` specializes to
ZMod q for every positive integer q. Theorem E now has fully formal status. No attainment is
claimed for the grid or the sparse mixing lifts.

## Item 4: completed

The shared [GraphMatchings](../../lean-machine/LeanMachine/WholeRow/GraphMatchings.lean)
uses Mathlib's `Subgraph.IsMatching` and `Subgraph.IsInduced`, nonempty parts and unique edge
membership. Taking both orders of every edge produces an `InducedMatchingPartition` for
ρ(j) = {j} ∪ {non-neighbours of j}. Its window at j is exactly d − degree(j).

[GraphMatchingCode](../../Tape-Transposition-and-the-Matrix-Coding-Conjecture/lean/MatrixCoding/GraphMatchingCode.lean)
then proves the paper's whole-row predicate and exactly |A|^(d²−m) words for every finite abelian
group A and arbitrary prescribed matching sums. Diagonal and non-edge coordinates are free.
The zero-sum construction is a linear subspace of codimension exactly m over any field,
including infinite fields. The graph-existence results and their asymptotic parameters remain cited.
