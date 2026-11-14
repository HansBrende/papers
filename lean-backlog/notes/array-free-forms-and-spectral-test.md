# Array-free forms of the whole-row rate, and a test of spectral bounds

Status: the equivalent forms are relabellings or standard facts. The tests are finite computations
(floating-point linear programs and one exhaustive search); the two closed formulas are observed,
not proved. No bound on the whole-row rate follows. Front X32 of the [roadmap](../wall.md).

## 1. Equivalent forms

Fix d, an alphabet of q symbols, and helper sets ρ(j) ⊆ {0, …, d−1} with at most w elements.

- **Positions.** Number the d² cells n = i·d + j. *Block* i is the set of d consecutive positions
  i·d, …, i·d + d − 1 (row i). *Class* j is the set of positions n ≡ j (mod d) (column j). A
  whole-row code is a set C of words of length d² such that, for every j, the symbols at class j
  are determined by the symbols in the blocks ρ(j). Transposition is the exchange of the two
  base-d digits of n.
- **Integers.** A word is an integer below q^(d²). Its base-q^d digits are the rows; column j is
  the j-th base-q digit of every such digit.
- **Differences (no recovery functions).** Give the alphabet any abelian group structure. Let F be
  the set of words z such that, for some j, z vanishes on all blocks of ρ(j) but not on class j.
  Then C is a whole-row code for ρ exactly when no difference of two words of C lies in F: two
  words that agree on the helper blocks must agree on the class. So the largest code is the largest
  set with no forbidden difference, an independent set in the confusion graph of index coding
  (Alon, Hassidim, Lubetzky, Stav and Weinstein 2008), also called the guessing graph (Gadouleau
  and Riis 2011).
- **Fixed points.** C is a code exactly when it is contained in the fixed-point set of a map whose
  output at class j reads only the blocks ρ(j).
- **Entropy.** The largest rate is the largest H(X)/(d² log q) over random words X with
  H(class j | blocks ρ(j)) = 0 for all j. Shannon's inequalities give a linear-programming
  relaxation.
- **Linear codes.** The dimension is d² minus the rank of the swap minus a row-local operator
  (Paper 17).

All of these keep the same structure: two partitions of the d² positions into d parts of size d,
every part of one meeting every part of the other in one position.

## 2. The Delsarte bound on the difference form

The difference form admits Delsarte's linear-programming bound. For a graph host (vertex v is a
function of its neighbours) the scheme is the product of trivial schemes, with one relation per
support S. The allowed supports are those in which every vertex has a neighbour, and

  maximise Σ_S A_S subject to A_∅ = 1, A_S ≥ 0, Σ_S A_S (−1/(q−1))^|S∩T| ≥ 0 for all T

bounds the size of every code over q symbols. Splitting a symbol into sub-symbols does not refine
it: the invertible linear maps of one symbol preserve the forbidden set and are transitive on the
nonzero values, so the finer programme symmetrises to the same one. The indicator of "z vanishes
on the complement of a maximum acyclic set" is dual feasible, so the bound is never worse than the
order bound.

Exponents log_q(LP value) from [`delsarte_lp.py`](../tools/host-probe/delsarte_lp.py):

| host | capacity | order bound | q = 2 | q = 4 | q = 16 | q = 64 |
|---|---|---|---|---|---|---|
| 5-cycle | 2.5 | 3 | 2.585 | 2.661 | 2.772 | 2.837 |
| 7-cycle | 3.5 | 4 | 3.515 | 3.554 | 3.658 | 3.746 |
| 9-cycle | 4.5 | 5 | 4.503 | 4.518 | 4.594 | 4.684 |
| Petersen | 5 | 6 | 5.222 | 5.483 | 5.697 | (solver failed) |
| K₃,₃, cube | 3, 4 | 3, 4 | exact | exact | exact | exact |

At every tested q the value is q²(q+1)/2 on the 5-cycle and q⁴(q+3)/(3q+1) on the 7-cycle. On the
9-cycle the ratio to q⁵ falls from 0.71 at q = 2 to 0.27 at q = 64, and on the Petersen graph the
ratio to q⁶ falls from 0.58 to 0.43 at q = 16. So on these hosts the bound improves on the order
bound by a bounded factor in the number of codewords, which is O(1/log q) symbols. As an upper
bound on capacity (all alphabets) it returns the order bound there.

## 3. A rank bound on the binary pentagon

If P vanishes on the nonzero allowed differences and P(0) ≠ 0, the matrix P(x − y) restricted to a
code is diagonal and invertible, so the code has at most rank-many words. The indicator above has
rank q^(order bound). Over F₂ on the binary 5-cycle, all 2¹⁵ admissible P were tried
([`rank_bound_pentagon.py`](../tools/host-probe/rank_bound_pentagon.py)): the minimum rank is 8,
the order bound, while the largest code has 5 words and the Delsarte value is 6. General matrices
that are not translation invariant were not tried.

## 4. Reading

In the whole-row question the alphabet has d symbols and grows with the array. A common deficit
is a saving of a constant fraction of whole symbols. A bound that saves a bounded factor of
codewords, or a bounded number of bits per position, saves nothing in the limit. The arguments in
the series that do save whole symbols are closure and order arguments, Shannon inequalities, rank
arguments for linear codes, and the fibre counts of the two-sided reduction.

Not tested: semidefinite strengthenings of the Delsarte programme, and rank bounds from general
matrices. Nothing here is a theorem about every host.
