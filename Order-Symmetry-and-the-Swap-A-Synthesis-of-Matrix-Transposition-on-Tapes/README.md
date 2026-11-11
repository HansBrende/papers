# Order, Symmetry and the Swap: A Synthesis of Matrix Transposition on Tapes

Hans Brende and Claude Fable 5.2 (Anthropic), November 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (`SwapRigidity`, Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It requires [`lean-machine/`](../lean-machine/) by a relative path, for the pinned
  Mathlib, so that sibling directory of this repository must be in place. It uses no library of an earlier paper.
- [`tools/`](tools/): every script that was used for the paper, and the saved codes of its numerical remarks:
  the generators of the index of Lean declarations and of the data of the explicit example, the exact computations of
  the numerical remarks, and the searches and controls behind the table of small sizes.
  [`tools/README.md`](tools/README.md) lists them, with the versions used and a record of the solver runs. Each script
  documents its usage at its top.

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
- **Changes that affect single entries (`Entry.lean`; Proposition 6.15, added in the revision that follows the memo
  below):** `IsEntryRuleCode.two_mul_finrank_le`, `IsEntryRuleCode.two_mul_finrank_le_of_changes`. Let entry (c, r) of
  a matrix be a linear functional a(c, r) of the matrix with its columns rotated by c. If a set P of positions contains
  (c + 1, r) whenever a(c, r) ≠ a(c + 1, r), and meets every anti-diagonal, then 2·dim ≤ d² + |P|; in particular
  2·dim ≤ d² + d + E when the functional changes from one row to the next at E pairs (c, r) in all. So each place
  where the decoder of an output entry changes from one row to the next costs at most half a symbol, where a change of
  class costs half a row (`IsEntryRuleCode.two_mul_finrank_le_of_rows` gives the bound of Theorem TP for the unit
  shift again).
- **Advice and changes at single entries (`EntryAdvice.lean`; Corollary 6.16, added in the same revision):**
  `IsEntryRuleCodeWithAdvice.natCard_fiber_le`, `IsEntryRuleCodeWithAdvice.natCard_pow_two_mul_finrank_le`. Over a
  finite field F, let the advice be any map to a finite set Ω, whose value may select the functionals of all entries
  and add a constant to each. If every selected rule changes from one row to the next at no more than E pairs, then
  at most |F|^⌊(d² + d + E)/2⌋ matrices of the code share a value of the advice, and
  |F|^(2·dim) ≤ |Ω|²·|F|^(d² + d + E). The counting follows the memo's Theorem 5.5.
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
  and the dimension count and sharpness in the corollary that every address digit must be treated asymmetrically;
- in Proposition 6.15, the size Σ_t max(1, m_t) of the set P that the proof exhibits for the Lean statement, where m_t
  is the number of changes on the anti-diagonal t;
- Proposition 6.17, added after the memo's update (see below): for every d ≥ 8 divisible by 4, over every field and
  for every nonzero λ, an explicit class-uniform rule for the two classes {0, 2, ..., d − 4} and the rest has a largest
  code of dimension (d² + 2d)/2 + d/4 − 1. So these two classes carry a code that exceeds (d² + 2d)/2 by d/4 − 1, over every
  field, including GF(2). For λ = 2 over fields in which 2 ≠ 0 this is the memo's Theorem 4.8; in Lean the memo
  proves, at d = 8, 12 and 16, that the two classes carry a code of that dimension. The codes over GF(2) at d = 8, 12
  and 16 are saved in `tools/data/`, and `tools/two_class_family.py` checks every rank stated in the proof for d ≤ 48
  over five small fields.
- Lemma 6.18 and Corollary 6.19, added with it: a blow-up may use a different code at each position (for equal codes
  this is the memo's blow-up theorem, proved in Lean there). With the code of Proposition 6.17 at ⌊M/2⌋ of the
  k = ⌈M/2⌉ positions and, for odd M, the symmetric matrices at the last, there is for every M ≥ 2 a partition of
  Z/kd into M classes with a code of dimension (n² + Mn)/2 + ⌊M/2⌋(n/4 − k), n = kd. So for every fixed number
  M ≥ 2 of classes the gain over (n² + Mn)/2 is unbounded, over every field. The script checks instances for M = 3, ..., 7.

- Proposition 6.21, added after two later papers of the series (see below): two bounds for sets of matrices over
  any alphabet and for decoding functions that are not linear. (a) If every entry of row c is a function of entries in
  columns j with g(j) > c, the set has at most q^(Σ g(j)) matrices; this is the elimination step of Theorem FL, and it
  holds with rows and columns exchanged. (b) If every entry is a function of one entry (possibly itself), the set
  has at most q^z matrices, z the number of cycles of the map between positions; for M classes of copy positions that
  is at most q^((d² + Md)/2). Both are instances of the acyclic-subgraph bound of Bar-Yossef, Birk, Jayram and Kol;
  what the proposition supplies is the two sets of positions. `tools/set_bounds_check.py` checks small instances.
- Propositions 6.22 and 6.23, added in the revision after that, on Problem 9.4(b). A *one-class relation of window w*
  lets the entry at (c, r) depend on the w entries at (i_m(r), c + j_m(r)), for arbitrary maps i_m, j_m of Z/d.
  - 6.22(a): for every ranking φ of the rows, a set of matrices on such a relation has at most
    q^(Σ_r max_m φ(i_m(r))) elements. (b): for w ≤ 2 that is at most q^(d(d+1)/2 + d − 1), for all maps, all functions
    and all sets; it holds whenever every column is a function of at most two rows. The bound is attained at d = 3,
    and for even d there are sets with q^(d²/2 + d) matrices, so the constant C of Problem 9.4(b) at window two,
    with a function for each position, lies between 1 and 3/2. (c), (d): if the offsets, or the
    differences of the rows from a permutation, take at most s + 1 values, at most q^(d²/2 + 6 d^(2 − 1/(s+1))),
    for every window.
  - 6.23: for every ε > 0, all but ε d² of the pairs of positions that help each other are related by one of at
    most 2w²/ε translates of the swap, so a code that uses only such pairs has at most q^((1/2 + o(1)) d²)
    elements; and o(d²) positions meet all loops and transitive triangles, so the theorems of the seventh paper for
    relations without them apply.
  - The bounds are the acyclic-subgraph bound with suitable orders; the two statements of 6.23 about pairs and
    triangles are counts. Problem 9.4(b) is now asked for w ≥ 3. Searches reported in Section 6.7 indicate that for
    large windows the acyclic-subgraph bound cannot answer it; for one instance this is proved.
  - `tools/order_bounds_check.py` checks the lemmas and small instances; `tools/acyclic_set_search.py` reproduces
    the searches.

Numerical remarks (exact computations, reproduced by the scripts in `tools/`, not used in any proof) are labelled as
numerical in the paper. Those over GF(2) at sizes up to six are collected in its section on small sizes; the remark on
the two-class rule also uses GF(3), GF(5), GF(7) and GF(11).

Both theorems are statements about a linear one-hop model. They are not lower bounds for machines.

## What is open

Statement (T). For oblivious machines: whether storage codes on the cone relations of real schedules exceed rate ½. In the
one-hop model of this paper: for classes with no almost-period, whether a fixed number M of classes can gain more than
a multiple of d over (d² + Md)/2, and whether o(d) classes can gain at positive rate (the best bound for two classes
is now 41/64, from a later paper); for which partitions into intervals the bound (d² + Md)/2 is attained with linear
decoders; a
bound for rules that use masks at all dyadic scales on both indices; a version of Theorem TP for the cone systems of
oblivious schedules, and, in the one-hop model over a fixed alphabet, whether sets of matrices whose entries are
functions of three or more entries, boundedly many, at positions that move with the row stay at rate ½, with one
function for all rows or with a function for each position (Problem 9.4(b); for two entries they do, by
Proposition 6.22); and a subadditive quantity that is
large for the swap at every scale separately and is not raised at all scales by one linear-time operation. The
paper's last section states these precisely.

**Subsequent memo:** [Class-Uniform Codes in Every Characteristic but Three, Their Blow-ups, and the Price of Advice](memo-class-uniform-codes/)
shows that the two classes of the paper's Proposition 8.2 carry a code of dimension 25 over every field in which
3 ≠ 0, answers Problem 9.1(c) as first worded by blowing such a code up (the number of classes grows with d) and
restates it for a bounded number of classes, and proves, in the one-hop model over finite fields, an exchange rate for
the depth-reduction step: at most one dimension per symbol of advice plus half a row for each class change the advice
induces. An update of the memo adds explicit two-class rules whose codes have excess d/4 − 1 over (d² + 2d)/2 for
every d = 4k ≥ 8, over every field in which 2 ≠ 0 (proof in the memo; Lean at d = 8, 12 and 16). So the excess of two
classes is unbounded, and Problem 9.1(c), as revision 14b157a of the paper stated it, has a negative answer for two
classes over these fields.

The memo left the paper unchanged. The revision of the paper that follows it cites the memo and corrects three
passages:

- Section 7.4 and Problem 9.4 no longer charge each bit revealed by a genie as a change of regime at half a row. Half
  a row is the price of a change that affects a whole row. Each place where the decoder of one output entry changes
  from one row to the next costs at most half a symbol, and advice that enters additively changes no decoder (the
  memo). The new Proposition 6.15 and Corollary 6.16 state this; their bounds in terms of the number E of changes are
  proved in Lean, and one count in the sharper form of Proposition 6.15 is proved in the text.
- Problem 9.1(c) is stated for a fixed number of classes.
- The first sentence of Section 7.3 states the hypothesis it had dropped: for a linear code, positive characteristic
  or coefficients that cannot be rescaled to be bounded.

Remark 8.1(d) and Problem 9.1(b) are updated.

After the memo's update, a further revision of the paper cites the two-class rules and adds Section 6.6, which settles
the two cases that the memo's update leaves open.

- Characteristic 2 (Proposition 6.17, above): the memo's rule, with its coefficients 2 and 1/2 replaced by λ and 1/λ,
  has a code with the same gain d/4 − 1 over every field.
- Three or more classes (Lemma 6.18 and Corollary 6.19, above): for every fixed number M ≥ 2 of classes the gain over
  (d² + Md)/2 is unbounded, over every field.

Problem 9.1(c) therefore no longer asks whether the gain of a fixed number of classes is bounded. It asks whether the
gain is O(d). These results are proved in the text and are not formalized. The other results of the paper and their
formal proofs are unchanged.

**Two later papers of the series** followed revision ac70dc4:
[Macroscopic Information Transfer in Adaptive Tape Transposition](../Macroscopic-Information-Transfer-in-Adaptive-Tape-Transposition/)
and [Capacity and Composition of Shared Transposition Decoders](../Capacity-and-Composition-of-Shared-Transposition-Decoders/).
Revision 3911d87 of this paper cites them and changes the following; no earlier result or number of the paper
changes.

- Problem 9.1(a) and Section 7.3 quote the second paper's bounds for classes of any shape: (41/64)d² + O(d^(3/2)) for
  two classes, where this paper had (3/4)d² + O(d), and a deficit of order M^(−1/2) for M classes. Problem 9.1(c)
  quotes its exact value for the lifts of a partition, and Problem 9.2 is said to be about linear decoders.
- The new Section 6.7 records which linearity Theorem TP needs: the code must be a subspace, the decoders may be
  arbitrary maps, and for sets that are not subspaces one decoder for all rows is correct on a fraction 1/(2d) of all
  matrices (all from the second paper). It adds Proposition 6.21 (above) and a remark on marker rows: a set of
  matrices with one decoding function for all rows can exceed the value (d² + d)/2 of subspaces by a multiple of d
  that grows with the window. One sentence of Section 6.5 and one of Section 7.2, which said that Theorem TP needs
  linear decoders, are corrected, and a sentence is added to Section 6.5.
- Section 7.4 and Problem 9.4 are restated. The earlier text took the form of its question from a count for affine
  rules, and for decoders that are not affine and see the whole matrix there is no such count. Problem 9.4(b) is new:
  it asks whether shared decoders of bounded window bound a set of matrices. Section 7.4 also cites the second
  paper's bound for two hops and notes that a perfect shuffle of the columns has d − 1 classes; Section 7.1 notes
  what Proposition 6.21 gives for synchronous access.
- Sections 3.6, 4.1 and 4.2 cite the first paper: on the machine's own runs it proves a statement of the form that
  Section 3.6 reported as open, and it gives the function of Section 4.1 a form on those runs.

**The revision after 3911d87** is about Problem 9.4(b), which that revision asked for every window. It adds
Propositions 6.22 and 6.23 (above) at the end of Section 6.7, with a paragraph on what the acyclic-subgraph bound
does not reach; restricts Problem 9.4(b) to windows of at least three and rewrites the list of what is proved in
its commentary; and adds two rows to the table of Section 7.1, a sentence each to Sections 7.1 and 7.4, a paragraph
to the introduction, a sentence to the abstract, two items to the appendix on verification and a sentence to the
statement of contributions. The two
propositions are proved in the text and are not formalized. No earlier result or number changes.

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

The computations of the numerical remarks and of the section on small sizes ([`tools/README.md`](tools/README.md) has
the full list and the record of the solver runs):

```sh
python3 tools/exhaustive_flag_checks.py          # needs numpy; about 90 s
python3 tools/exhaustive_pigeonhole_checks.py    # needs numpy; about 45 s
python3 tools/three_term_example.py              # the three-term examples
python3 tools/digit_and_composition_checks.py    # the digit corollary and the composition remark on small instances
python3 tools/entry_form_check.py                # Proposition 6.15 on small instances
python3 tools/two_class_family.py                # Proposition 6.17 and Corollary 6.19 over small fields
python3 tools/set_bounds_check.py                # Proposition 6.21 on small instances; about 20 s
python3 tools/order_bounds_check.py              # Propositions 6.22 and 6.23: lemmas and small instances; about 15 s
python3 tools/acyclic_set_search.py pairing 60 9 2 9 3 9 5   # needs OR-tools; the searches of Section 6.7 (see tools/README.md)
python3 tools/small_sizes.py table               # the table of small sizes; re-verifies every saved code
python3 tools/verify_class_uniform_code.py tools/data/*.json
python3 tools/analyse_code.py                    # the code of dimension 25 and its translates
python3 tools/small_sizes.py controls            # needs pycryptosat; the solver answers quoted in the paper, about three minutes
python3 tools/class_uniform_sat.py 6 "0,1,3|2,4,5" 25 --rref   # needs pycryptosat; about three minutes
```

The paper is built with `latexmk -pdf main.tex` in `paper/`.
