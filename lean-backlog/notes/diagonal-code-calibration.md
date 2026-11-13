# Diagonal codes and window-dependent excess

Hans Brende, Claude Fable 5.2 and GPT-6 Astra, 13 November 2026.

**Fronts D1/D9.** Fable's displacement-diagonal construction disproves the
proposed near-cell bound with a constant independent of the helper window.
The folded-cube calculation below strengthens this to every fixed incidence
radius, and forces an exponentially growing coefficient in any uniform
additive bound. A separate general-group argument proves limiting half
rate when each diagonal is recovered using only its own mutual helpers,
even with arbitrary correlations and a paid common advice value. One-way
helpers and cross-diagonal recovery remain open.

The placement lemma is Lean-verified. The folded-cube, hypercube and general-group arguments
are written proofs, independently reviewed, with exact finite controls.
The finite capacity results use explicit code and order certificates; those
certificates and the bounded enumeration are not checked in Lean. No novelty
claim is made for the folded-cube rank formula or the reused order bound.

## 1. Placement does not require a permutation

Let a whole-row relation be $\rho:[d]\to 2^{[d]}$: column $c$ may read every
entry in rows $\rho(c)$. For any function $f:[d]\to[d]$, put a word $x$ in
the cells $(i,f(i))$ and a fixed symbol elsewhere.

**Placement lemma (Lean-verified).** Every finite storage code with helpers
$i\mapsto\rho(f(i))$ embeds this way as a whole-row code for $\rho$, with
unchanged cardinality. Neither $f$ nor the code needs to be linear, and $f$
need not be injective.

*Outline of the formal proof.* Different coordinates occupy different
rows, so the placement is injective even if columns repeat. To recover the
entry at $(i,f(i))$, read the placed coordinates in rows $\rho(f(i))$ and
use the original recovery rule. Other entries are constant.
[`placedCode_isWholeRow`](../FarClebsch.lean) and `card_placedCode` prove
these claims. The previous diagonal theorem is their identity-placement
corollary. All printed endpoints use only the standard Lean axioms. ∎

For a group $G$ of order $d$ and $\rho(c)=cT$, take $f_g(i)=ig$.
The displacement-$g$ diagonal carries the directed Cayley relation
$i\to igT$. These $d$ diagonals partition the full array. Independent codes
on them can therefore be combined, with cardinalities multiplied. This is
a construction, not a decomposition theorem for arbitrary whole-row codes.

Ordinary transposed-cell pairing needs its own helper-access check. The
mate of $(i,c)$ is in row $c$, which is readable only when $c\in\rho(c)$.
Thus inverse diagonals carry that pairing when self-row access is supplied,
for example $e\in T$; it is not automatic for arbitrary $T$. Even then,
the raw diagonal-capacity sum can underestimate the array capacity: on
$\mathbb Z/3$ with $T=\{0\}$ it is $3+1+1=5$, while symmetric matrices
give dimension six. This is the inverse-diagonal pairing exception, not
evidence of a further coupling mechanism.

## 2. A binary code on every odd folded cube

For $j=2m+1$, let $F_j$ be the Cayley graph on $\mathbb F_2^{2m}$ with
generators $e_1,\ldots,e_{2m},e_1+\cdots+e_{2m}$. For $m=0$ this means
one vertex with a loop. Let $A_j$ be its adjacency matrix over $\mathbb F_2$.

**Folded-cube rank (written proof).**

$$\operatorname{rank}(I+A_j)=\frac{4^m-2^m}{2},\qquad
\dim\ker(I+A_j)=\frac{4^m+2^m}{2}.$$

The kernel is a storage code of rate $1/2+2^{-(j+1)/2}$.

*Proof.* Identify the regular representation with

$$R_m=\mathbb F_2[x_1,\ldots,x_{2m}]/(x_1^2,\ldots,x_{2m}^2),
\qquad a_i=1+x_i.$$

The fitting operator is multiplication by
$f_m=1+\sum_i a_i+\prod_i a_i$. For $m\ge1$, write $R=R_{m-1}$,
$c=\prod_{i\le2m-2}a_i$, and $x,y$ for the last two variables. Since
$c^2=1$,

$$f_m=f_{m-1}+(1+c)(x+y)+cxy.$$

The invertible $R$-algebra substitution $u=x+1+c$, $v=y+1+c$, $U=cu$
turns this into $f_{m-1}+Uv$, with $U^2=v^2=0$.
Let $D$ be multiplication by $f_{m-1}$ on $R$, of dimension
$n=4^{m-1}$ and rank $r_{m-1}$. Each $a_i^2=1$ and the number of terms
in $f_{m-1}$ is even, so $D^2=0$. In the basis
$1,U,v,Uv$, two blocks are $D$ and the other block is

$$\begin{pmatrix}D&0\\I&D\end{pmatrix}.$$

Its kernel is $\{(Db,b):b\in R\}$, so its rank is $n$. Consequently
$r_m=4^{m-1}+2r_{m-1}$, with $r_0=0$. Solving the recurrence gives the
displayed formula. The equation $(I+A_j)x=0$ supplies the storage-code
recovery rules. ∎

The cases $j=1,3,5$ are a free loop, $K_4$ and the Clebsch code. Exact
binary elimination at $j=1,3,5,7,9$ gives ranks $0,1,6,28,120$.
The written proof, not this finite check, supplies all $j$.

## 3. The full hypercube construction and its scope

Let $1\le w\le k$, $d=2^k$, and let $T\subset\mathbb F_2^k$ consist of
$w$ linearly independent vectors. Set $\rho(c)=c+T$. Forward and reverse
windows are both $w$.

**Hypercube bounds (written proof).** There is a binary whole-row code with

$$\log_2|C|=d^2/2+dS(w),\qquad
S(w)=\sum_{\substack{1\le j\le w\\ j\text{ odd}}}
\binom wj 2^{-(j+1)/2}
=\frac{(1+1/\sqrt2)^w-(1-1/\sqrt2)^w}{2\sqrt2}.$$

Every whole-row code over an alphabet of size $q\ge2$ satisfies

$$\log_q|C|\le d^2/2+2^{w-2}d.$$

*Proof of the construction.* On displacement $g$ which is the sum of an
odd number $j$ of distinct elements of $T$, select those $j$ generators
from $g+T$. They have a single relation, their sum is zero, and they span
a space of dimension $j-1$. Their cosets give disjoint copies of $F_j$.
Use the preceding binary kernel code on each copy and ignore the other
helpers. The full diagonal graph may have additional edges between copies;
the construction does not require those edges to be absent. Every remaining
diagonal admits a perfect matching along a nonzero generator and hence a
half-rate code. Independent diagonal products give the formula. ∎

*Proof of the upper bound.* Choose $t_0\in T$ and put
$H=\operatorname{span}\{t+t_0:t\in T\}$. Independence gives
$\dim H=w-1$, and every $\rho(c)$ lies in the coset $c+t_0+H$.
Paper 17's [whole-row order bound, Proposition `rows`(a,c)](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/symmetry.tex)
applies to this fixed row partition into blocks of size $2^{w-1}$.
It gives $(d^2+2^{w-1}d)/2$, improving the initial span-$T$ estimate
by a factor two in its additive term. ∎

For any fixed integer incidence radius $r\ge1$, the number of near cells is

$$N_r=d\sum_{\substack{1\le j\le\min(r,w)\\ j\text{ odd}}}\binom wj.$$

Indeed, an odd-length incidence walk to displacement $g$ sums its labels
from $T$. Independence makes the shortest possible odd length the odd
Hamming weight of $g$. Even-weight displacements and those outside
$\operatorname{span}T$ are disconnected in the incidence double.

**No window-independent finite-radius allowance (written consequence).**
For every fixed $r\ge1$ and every constant $C_r\ge0$, some whole-row code
violates $\log_q|C|\le d^2/2+C_rN_r$. The construction already works with
$q=2$: $S(w)$ grows exponentially in $w$, whereas $N_r/d$ is a polynomial
in $w$ of degree at most $r$. Choose $w$ large enough and then any $k\ge w$.
Thus counterexamples exist at arbitrarily large dimensions for that fixed
chosen window.

This disproves the absolute-constant conjecture in §10 of the
[row-spread note](row-spread-of-cones.md). It does **not** disprove a bound
$d^2/2+F(w,w')d$, or limiting half rate for every fixed window. In the
former bound, one necessarily has $F(w,w)\ge S(w)$. The displayed code's
excess divided by $d^2$ is $S(w)/d$, which tends to zero at every fixed $w$.
No new native-machine exclusion or construction follows.

## 4. The finite diagonal-coupling test

For $\rho(c)=c+T$ on $\mathbb F_2^4$, the exact controls give:

| Helper set $T$ | Binary diagonal product dimension | Whole-array upper bound | Conclusion |
|---|---:|---:|---|
| $\{1,2,4,8\}$ | 176 | 176 | Exact capacity $q^{176}$ for every finite alphabet |
| $\{1,2,4,8,15\}$ | 210 | 211 | Binary capacity lies between $2^{210}$ and $2^{211}$ |

For the basis host, four diagonal relations have loops and contribute
16 each; four have spanning disjoint $K_4$ graphs and contribute 12 each;
the other eight are bipartite with perfect matchings and contribute eight
each. Independent-set upper certificates match these numbers. The
construction uses sum-zero codes over a cyclic group of order $q$, so its
dimension 176 is attained over every finite alphabet. An explicit row order
gives an 80-cell induced acyclic set in the full array, proving the upper
bound even for nonlinear or vector codes. The corresponding smaller basis
hosts have exact capacities $q^{12}$ at $d=4$ and $q^{46}$ at $d=8$.

For the Clebsch host, five loop diagonals contribute 80, the zero
displacement contributes ten, and ten other diagonals contribute 12 each.
The ten-dimensional diagonal upper bound is Paper 4's
[Corollary H4](../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/codes.tex).
Its binary attainment does not assert attainment over every alphabet.
The full-array fitting matrix has binary rank 46. An explicit 45-cell
acyclic set gives the all-alphabet upper bound $q^{211}$.

The exact subset dynamic program evaluates the best row order. If $S$ is
the set of rows placed first, define $a(S)=\#\{c:\rho(c)\subseteq S\}$.
With $D(\varnothing)=0$,

$$D(S)=\max_{i\in S}\bigl(D(S\setminus\{i\})+a(S\setminus\{i\})\bigr).$$

Adding row $i$ places exactly $a(S\setminus\{i\})$ new cells in the
acyclic set. Paper 17's Proposition `rows`(b) proves that every cell DAG
is contained in some row-order DAG. Thus the computed maximum 45 for
Clebsch is the exact maximum acyclic-set size, not merely an order-search
heuristic. A stronger upper bound there must go beyond this order method.

### The bounded covariant test

Over $\mathbb F_2$, there is no Fourier decomposition into 16 characters
of $\mathbb F_2^4$: every multiplicative character is trivial. Good-
characteristic Fourier arguments do not apply to this binary test.
Covariance itself is an additional restriction on a decoder, even over a
field where Fourier analysis is available.

For a simultaneous-translation-covariant decoder, write a cell as
$x_g(c)=X_{c+g,c}$. Its fitting block from sector $h$ to sector $g$ is

$$H_{g,h}=\delta_{g,h}I+\sum_{t\in T}\kappa_t(g,h)P_{t+h},$$

where $P_v$ translates the column index by $v$. On the eleven nonloop
Clebsch sectors there are 605 binary coefficients. This is an exact
group-ring description, not a character reduction.

We exhaustively checked the much smaller family coupling just two such
sectors, leaving all other sectors independent. Permuting the five
Clebsch generators gives three pair types: $(0,3)$, $(3,5)$ and $(3,12)$.
Each has four five-bit coefficients, hence $2^{20}$ fitting matrices of
size $32\times32$. Exact binary elimination found minimum ranks
$10,8,8$, respectively, exactly their independent-sector baselines.
This covers $3\cdot2^{20}$ matrices and excludes improvement only within
that stated family. It does not exclude three-sector coupling, general
covariant coupling, noncovariant decoders or vector/nonlinear gains.

The bounded test stops here. The remaining scalar Clebsch question is
whether an unrestricted fitting matrix of rank 45 exists. Failure of the
restricted search supplies no answer, and this finite one-dimensional gap
does not by itself decide the fixed-window asymptotic problem.

## 5. Most translated mutual-helper graphs are bipartite

The proposed construction side asked for a positive fraction of displacement
diagonals that are both undirected and non-bipartite. The following written
theorem rules this out at fixed window, in every finite group. Its
mutual-helper extension also applies when the full diagonals are directed.
These are independently reviewed written proofs, not Lean formalizations.

**Symmetric-translate theorem.** Fix $w\ge1$. Uniformly over finite groups
$G$ of order $d\to\infty$ and subsets $T\subset G$ of size $w$, the number
$B$ of $g\in G$ for which $gT$ is inverse-closed and
$\operatorname{Cay}(G,gT)$ is non-bipartite is $O_w(d/\log d)$.
Loops count as non-bipartite. The set $T$ need not generate $G$.

*Proof.* Choose $t_0\in T$, put $U=t_0^{-1}T$, $H=\langle U\rangle$ and
$h=gt_0$. Then $1\in U$, $gT=hU$, and $H$ has at most $r=w-1$ generators.
If $hU$ is inverse-closed, then

$$hUh=U^{-1},\qquad a=h^2\in U^{-1},\qquad
hUh^{-1}=U^{-1}a^{-1}\subset H.$$

The last inclusion makes $h$ normalize the finite group $H$. If $h\notin H$,
the subgroup generated by $H,h$ has quotient of order two over $H$, and
every generator in $hU$ crosses its two cosets. Each Cayley component is
therefore bipartite. Thus every translate counted by $B$ has $h\in H$.

There are at most $w$ choices of $a$. For a fixed $a$, conjugation by $h$
maps $U$ bijectively onto $U^{-1}a^{-1}$, giving at most $w!$ possibilities.
Two elements of $H$ with the same square and the same conjugation action on
$U$ differ by an element of

$$E=Z(H)[2]=\{z\in Z(H):z^2=1\}.$$

Indeed, $U$ generates $H$, so equality of those conjugations makes their
quotient central, and equality of the squares makes its square one.
Consequently $B\le ww!|E|$, and also $B\le|H|$.

Here is an elementary bound on $E$ needing no structure theorem for $H$.
Let $m=[H:E]$ and choose quotient representatives, with representative one
for $E$. For each representative $v$ and each of at most $2r$ generators
or inverses $s$, form $vs\overline{vs}^{-1}\in E$. These at most $2rm$
elements generate $E$: following the successive representatives in a word
for an element of $E$ gives the assertion by telescoping. Since $E$ is
central of exponent two, $|E|\le2^{2rm}$. Hence

$$|H|=m|E|\le2^{(2r+1)m}.$$

For $d>1$, if $|H|\le\sqrt d$ use $B\le|H|$. Otherwise
$m\ge\log_2(d)/(2(2r+1))$ and $|E|=|H|/m\le d/m$. Together these give

$$\frac Bd\le\max\left\{d^{-1/2},
\frac{2ww!(2r+1)}{\log_2d}\right\}.$$

This tends to zero with $w$ fixed. When $w=1$, exactly one symmetric
translate is non-bipartite: the single loop generator. ∎

**Mutual-helper corollary (written proof).** Let
$V_g=gT\cap(gT)^{-1}$ be the full mutual-helper set of a displacement
diagonal. Only $O_w(d/\log d)$ of the Cayley graphs with generators $V_g$
are non-bipartite. Therefore, over every finite alphabet of size $q\ge2$, any code whose
decoders use only mutual helpers within the target's own diagonal satisfies

$$\log_q|C|\le d^2/2+O_w(d^2/\log d).$$

*Proof.* Write $V_g=gT'_g$ for a subset $T'_g\subseteq T$.
For each nonempty fixed subset $T'\subseteq T$, the preceding theorem
counts the displacements for which $gT'$ is inverse-closed and non-bipartite.
Taking the union over at most $2^w-1$ subsets gives the first claim.
Empty mutual graphs have only constant storage codes. Every other bipartite
mutual graph is a nonempty regular undirected Cayley graph. Its two sides
have equal size within each component, and recording one side determines
the other, bounding its code by $q^{d/2}$. The projection of the full code
to each diagonal is a storage code for its mutual-helper graph: extensions
to full codewords cannot change a recovery rule that reads only that
diagonal. The full code injects into the product of its projections.
Bound each exceptional projection trivially by $q^d$ and multiply.
No product structure or independence of the original code is required. ∎

More generally, if each decoder also receives the same advice value with
at most $M$ possibilities, condition on that value and apply the corollary
to every fibre. The cardinality bound is multiplied by $M$, or its
base-$q$ logarithm increases by $\log_q M$. If $\log_q M=o(d^2)$,
limiting half rate is preserved in this class, including growing alphabets.

This is a restriction on a construction architecture, not a whole-row
capacity bound. At fixed window, a positive rate excess beyond the paid
common advice must use one-way helpers or cross-diagonal recovery. Both remain open;
the argument does not remove one-way dependencies without paying for them,
and it does not assume that arbitrary whole-row codes split into diagonals.

## 6. Reproduction

[Commands and exact certificates](../tools/diagonal-calibration/README.md)
check the folded-cube ranks, diagonal fitting matrices, helper support,
independent sets, row orders, subset dynamic programs and the three
two-sector enumerations. The existing command
`lake env python3 ../../lean-backlog/check.py FarClebsch`, run from the
Paper 15 `lean` directory, verifies the generalized placement lemma and
its old diagonal corollaries.
