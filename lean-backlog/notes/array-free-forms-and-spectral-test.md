# Array-free forms of the whole-row rate, and a test of spectral bounds

Status: the equivalent forms are relabellings or standard facts. The tests are finite computations
(floating-point linear programs and one exhaustive search); the two closed formulas are observed,
not proved. No bound on the whole-row rate follows. Front X32 of the [roadmap](../wall.md).

## 1. Equivalent forms

Fix d, an alphabet of q≥2 symbols, and helper sets ρ(j) ⊆ {0, …, d−1} with at most w elements.

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

bounds the size of every code over q symbols. For the prime-power alphabets tested,
splitting a symbol into sub-symbols does not refine the complete automorphism-invariant
Fourier programme: the invertible linear maps of one symbol preserve the forbidden set and
are transitive on its nonzero values, so that programme symmetrises to the same one.
This is not a claim about every hierarchy or additional sub-symbol constraint.
The indicator of "z vanishes
on the complement of a maximum acyclic set" is dual feasible, so the bound is never worse than the
order bound.

Exponents log_q(LP value) from [`delsarte_lp.py`](../tools/host-probe/delsarte_lp.py):

| host | capacity | order bound | q = 2 | q = 4 | q = 16 | q = 64 |
|---|---|---|---|---|---|---|
| 5-cycle | 2.5 | 3 | 2.585 | 2.661 | 2.772 | 2.837 |
| 7-cycle | 3.5 | 4 | 3.515 | 3.553 | 3.658 | 3.746 |
| 9-cycle | 4.5 | 5 | 4.503 | 4.518 | 4.594 | 4.684 |
| Petersen | 5 | 6 | 5.222 | 5.483 | 5.697 | (solver failed) |
| K₃,₃, cube | 3, 4 | 3, 4 | exact | exact | exact | exact |

At each tested q the floating-point outputs agree numerically with q²(q+1)/2 on the 5-cycle
and q⁴(q+3)/(3q+1) on the 7-cycle. No all-q formula is proved. If these identities held for all q,
their exponents would approach the order bounds with O(1/log q) savings. On the 9-cycle the
sampled ratio to q⁵ falls from 0.71 at q = 2 to 0.27 at q = 64, and on Petersen the sampled
ratio to q⁶ falls from 0.58 to 0.43 at q = 16. Those finite samples establish no limit.

A separate bounded replay reproduced C5 at q=2,4,16; C7 at q=2,4;
K₃,₃ at q=2,4; and the cube at q=2. These remain floating-point values,
not exact dual certificates. No larger-host or asymptotic test was added.

"Capacity" in the table is the exponent attained in the limit of alphabets (on odd cycles, at
square q). The largest code at one q can be smaller: 5 words on the binary 5-cycle.

**Countercontrol (from review).** For two symbols that determine each other the confusion graph is
the Hamming graph H(2, q), with eigenvalues 2(q−1), q−2 and −2. The eigenvalue bound gives
|C| ≤ q, one whole symbol saved at every q. This is the order bound for that host. The programme
always saves at least what the order bound saves; the observation above concerns only its excess
over the order bound, and only these hosts.

## 3. A rank bound on the binary pentagon

If P vanishes on the nonzero allowed differences and P(0) ≠ 0, the matrix P(x − y) restricted to a
code is diagonal and invertible, so the code has at most rank-many words. The indicator above has
rank q^(order bound). Over F₂ on the binary 5-cycle, all 2¹⁵ admissible P were tried
([`rank_bound_pentagon.py`](../tools/host-probe/rank_bound_pentagon.py)): the minimum rank is 8,
the order bound, while the largest code has 5 words and the Delsarte value is 6. General matrices
that are not translation invariant were not tried.

The exhaustive script also replays independently: its rank histogram is
8:50, 10:30, 12:432, 16:15872, 32:16384, totaling 2¹⁵ functions. Its
separate exact clique enumeration confirms the binary code size 5. These
are exact finite Python computations, not Lean proofs or general rank bounds.

## 4. Reading

In the canonical whole-row question the alphabet size q(d) grows with d, so a common
deficit is a saving of a constant fraction of whole symbols. These tests keep the coordinate
host fixed; they establish neither an all-q bounded-factor result nor a bound uniform in a
growing host size. Even the conjectured fixed-host limits would not decide the joint d,q(d)
regime. The tests justify a bounded experimental stopping decision, not an asymptotic
exclusion of this programme. They also say nothing against Fourier, rank or semidefinite
methods as families: the programme itself saves whole symbols wherever the order bound does.

Not tested: semidefinite strengthenings of the Delsarte programme, rank bounds from general
matrices, and hosts other than those in the table. No barrier follows.
