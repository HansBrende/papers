# Order, Symmetry and the Swap: A Synthesis of Matrix Transposition on Tapes

Hans Brende and Claude Fable 5.2 (Anthropic), November 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (`SwapRigidity`, Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It requires [`lean-machine/`](../lean-machine/) by a relative path, for the pinned
  Mathlib, so that sibling directory of this repository must be in place. It uses no library of an earlier paper.
- [`tools/`](tools/): scripts for the index of Lean declarations and for the exact computations of the paper's numerical
  remarks and of its section on small sizes. Each script documents its usage at its top.

## The question

Can a multitape Turing machine transpose a d×d matrix of b(d) = max(1, ⌈log₂ d⌉)-bit entries, written row by row, in time
linear in its length L = d²b(d)? This is statement (T) of the
[first paper](../Matrix-Transposition-and-the-Tape-Coding-Conjecture/). Sixteen papers and eight memos of this series
study it without deciding it. This paper is written for a reader who wants to know where the series stands without
reading all of them. It has three parts.

- **A synthesis** (Section 3): the main results of the earlier papers in one place, by theme, each with its hypotheses and
  its citation.
- **A diagnosis** (Section 4): for oblivious machines the question is now one function, the best rate of a storage code on
  the cone relation of a linear-time schedule after a genie reveals εL bits. A transposer needs rate 1 − ε for every ε;
  pairing gives ½; nothing above ½ is proved or excluded on the relations of real machines. Arguments from head motion
  alone, from codes alone and from pass counting are each exhausted, for one reason: the log d of the folklore algorithm is
  a sum over address scales, and every tool looks at one scale or at none.
- **Two theorems** (Sections 5 and 6) about the swap τ on V ⊗ V, V = F^d, and the code ker(τ − K) of the matrices that an
  operator K = Σ A_a ⊗ B_a transposes correctly.

## What is proved

Proved in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound` (the paper states each result with its
Lean declarations and file; declarations below are in the namespace `SwapRigidity`):

- **Theorem FL, the flag bound, in coordinates (`Flag.lean`):** `finrank_swapCode_le_of_flag`. If P and Q are invertible
  and column b′ of every P⁻¹B_aQ vanishes from row g(b′) on, then dim ker(τ − K) ≤ Σ min(g(b′), d), for arbitrary A_a
  (`finrank_swapCode_le_of_staircase` is the case P = Q = 1; `finrank_swapCode_le_of_flag_left` has the hypothesis on the
  A_a; `finrank_swapCode_swap` exchanges the sides). The bound is attained for every g
  (`finrank_swapCode_staircase`, `exists_staircase_finrank_eq`). For a pair of flags the bound is d(d+1)/2
  (`two_mul_finrank_swapCode_le_of_triangular`).
- **The pigeonhole lemma (`Pigeonhole.lean`):** `two_mul_finrank_ker_sub_le`. For operators τ, K, T on an N-dimensional
  space, 2 dim ker(τ − K) ≤ N + dim ker[τ,T] + rank[K,T]; also the sharper form `two_mul_finrank_ker_sub_le_ker`, the
  commuting case, `finrank_range_commutator_le` (a commutator has rank at most twice the rank of a factor) and its
  subadditivity under composition `finrank_range_commutator_comp_le`.
- **The swap (`Swap.lean`):** `card_le_finrank_ker_swap_commutator`: dim ker[τ,T] ≥ d for every T, in every
  characteristic.
- **Theorem TP, the translate pigeonhole (`ClassUniform.lean`):** `IsClassUniformCode.finrank_le`. If every row c of a
  matrix is a linear function, depending only on the class of c, of the matrix with its columns rotated by c, then for a
  set of s + 1 shifts and a set S of rows meeting every component of the linking graph, (s+1)·dim ≤ s·d² + d·|S|. For M
  cyclic intervals: 2·dim ≤ d² + Md (`IsClassUniformCode.two_mul_finrank_le`).
- **Attainment for equal intervals (`BlockSymmetric.lean`):** `isClassUniformCode_blockSymmetric`,
  `two_mul_finrank_blockSymmetric`, `blockSymmetric_attains_bound`: the block-symmetric matrices are such a code of
  dimension (d² + Md)/2.
- **The line form (`Line.lean`):** `IsLineUniformCode.two_mul_finrank_le`: the same bound for windows on a line, without
  wrap-around.
- **Twist classes (`Twist.lean`):** `succ_mul_finrank_swapCode_le_of_twist_classes`.
- **Classes with no almost-period (`AperiodicExample.lean`):** `exists_classUniformCode_gt`. For d = 6 over GF(2) and the
  classes {0,1,3}, {2,4,5} there is a class-uniform code of dimension 25 > 24 = (d² + Md)/2
  (`finrank_aperiodicCode`, `isClassUniformCode_aperiodicCode`). The code was found by a SAT solver; Lean checks it from
  the data in `AperiodicExampleData.lean`, which `tools/gen_aperiodic_example.py` generates from
  `tools/data/aperiodic_d6_dim25.json`.

Proved in the paper but not formalized:

- the passage from flags to adapted bases in Theorem FL;
- the corollaries of Theorem FL for two Kronecker terms, for commuting or triangularizable families, for p-groups, for
  all affine index maps when d = p^m in characteristic p, and the expansion estimates;
- the equality case of dim ker[τ,T] ≥ d, the bound for copy rules, the bound for decoders with s modulation frequencies,
  and the dimension count and sharpness in the corollary that every address digit must be treated asymmetrically.

Numerical remarks (exact computations over GF(2), reproduced by the scripts in `tools/`, not used in any proof) are
labelled as numerical in the paper and collected in its section on small sizes.

Both theorems are statements about a linear one-hop model. They are not lower bounds for machines.

## What is open

Statement (T). For oblivious machines: whether storage codes on the cone relations of real schedules exceed rate ½. In the
one-hop model of this paper: the largest code of a class-uniform rule whose classes have no almost-period; whether the
bound (d² + Md)/2 is attained for every partition into intervals; a bound for rules that use masks at all dyadic scales on
both indices; a version of Theorem TP for the cone systems of oblivious schedules; and a subadditive quantity that is
large for the swap at every scale separately and is not raised at all scales by one linear-time operation. The paper's
last section states these precisely.

## Building and verifying

With `elan` installed, in `lean/`:

```sh
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

`PaperAxioms.lean` runs `#print axioms` on every declaration that the paper cites; each should report at most `propext`,
`Classical.choice` and `Quot.sound`. It and the index appendix `paper/sections/leanindex.tex` are generated from the
LaTeX sources:

```sh
python3 tools/lean_index.py          # regenerate both
python3 tools/lean_index.py --check  # fail if a cited name is missing or a generated file is stale
```

The data of the explicit example are generated, and checked to be current, by

```sh
python3 tools/gen_aperiodic_example.py --check
```

The computations of the numerical remarks:

```sh
python3 tools/exhaustive_flag_checks.py          # needs numpy; about 90 s
python3 tools/exhaustive_pigeonhole_checks.py    # needs numpy; about 45 s
python3 tools/verify_class_uniform_code.py tools/data/*.json
python3 tools/class_uniform_sat.py 6 "0,1,3|2,4,5" 25 --rref   # needs pycryptosat; about three minutes
```

The paper is built with `latexmk -pdf main.tex` in `paper/`.
