# Subcubic Storage Bounds beyond Scalar Recovery

Hans Brende and GPT-6 Astra (OpenAI), October 2026.

Extension memo to the fourth paper by Hans Brende and Claude Opus 5.5.
[PDF](https://hansbrende.github.io/papers/Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/memo-subcubic/paper/main.pdf) · [LaTeX](paper/) (CC BY 4.0) · [Lean](lean/) (Apache 2.0).

## The question

Which features of scalar recovery are enough to retain the subcubic storage
bound for vector or nonlinear data?

## What is proved

The Lean-verified reversible-rule package retains the original directed
no-recovery-triangle and reciprocity hypotheses:

- Half-size generators on vertex subsets and matching-size generators on the
  full graph. The generators depend only on the supports.
- A productive recovery schedule that uses each center at most once.
- Injective projection for every compatible alphabet and code; finite-code
  cardinality and arbitrary-field vector-dimension bounds.
- Invertible participating blocks as a specialization, with no commutativity.
- Exact directional ambiguity ledgers for finite inverse fibres, real
  polymatroids, and singular linear-block nullities. Row maxima are paid once.
- The original directed scalar half and matching bounds, and both clauses of
  the graph minrank equality, rederived from the new generator theorem.

For triangle-free subcubic graph support, the library also proves the intrinsic
half bound for arbitrary-field linear codes of unequal, unbounded coordinate
widths when each row has at most one component of rank above one. The proof
includes the rank-one endpoint and constructs actual quotient and coordinate-dual
recoveries. Exceptional rows pay their exact intersection deficit, bounded by
the dimension of their span. Identity-diagonal block-rank bounds and the scalar
specialization are corollaries.

For arbitrary block ranks, put `E = offdiag(W²)` and let `N` be the total
scalar dimension. The library proves `N ≤ 2 rank(I ± W) + 12 rank E`, with
a sharper payment on the actual kernel. If `E = 0`, it proves the exact
identity `2 rank(I − W) = 2 rank(I + W) = N + rank(W² − I)` over every
field. The earlier injective-summand bound and the involution equality
are direct corollaries. The full graph input is formalized: every finite
triangle-free subcubic graph covered by four-cycles maps to `K₈/₃` and
satisfies its weighted polymatroid half bound.

The cited proofs use only `propext`, `Classical.choice`, and `Quot.sound`.
The restriction, subspace-deficit, and coordinate-dual lemmas are shared in
[`lean-machine`](../../lean-machine/).

## What is open

Ordinary recovery of a center need not be reversible in every row direction.
The zero-cost bound does not cover unrestricted nonlinear or singular-block
codes. No native tape-to-subcubic representation or cheap decoder is supplied;
linear-time transposition remains open.

## Building and verifying

Clone the whole repository. This memo imports `../../lean`, which imports
its existing sibling dependencies. In `lean/`:

```sh
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

From this directory, run `python3 tools/lean_index.py` to regenerate the
index and axiom checks. In `paper/`, run `latexmk -pdf main.tex`.
