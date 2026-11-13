# Closed words, one-sided certificates, and distant helper loops

Hans Brende and GPT-6 Astra, 13 November 2026.

**Fronts D0 and D8.** These are written results and exact finite checks, not
Lean proofs. They review and extend Claude Fable's Propositions 6–8 in
[the twisted-swap note](twisted-swap.md#9-the-group-model-is-not-the-generic-model-re-evaluation-13-november-2026).
They do not exclude a new class of transposers. They identify a substantial
loss in one proposed reduction and a misleading success criterion for the
next search. The generic-matrix work is parked; its theorems remain valid.

Let $G$ be a finite group of order $d$, let $\pi$ be a representation of
dimension $n$, and put

$$
(\tau_\pi v)(g)=\pi(g)v(g^{-1}),\qquad
K=\sum_{s\in\Sigma}\kappa_s\otimes\pi(s).
$$

The matrices $\kappa_s$ are indexed by $G\times G$. A sector is one choice
of $\pi$. A decoder of the whole array uses the **same** $\kappa_s$ in
all sectors. Separate sector maxima need not be simultaneously attainable.
Right multiplication by the inversion permutation turns the residual into
$\operatorname{diag}_g\pi(g)-K'$, with the same allowed block space.
For the scalar baselines and their use inside the helper-valued problem,
assume $e\in\Sigma$, so $I_n$ is an allowed block. All finite examples
below satisfy this assumption; the Lean conjectures do not require it.

## 1. Distinct-site cycles and a stronger packing bound

For pairwise distinct sites $h_1,\ldots,h_k$ with invertible matrices
$U_{h_j}$, set $\kappa[h_j,h_{j+1}]=1$, cyclically. Then

$$
\dim\ker(\operatorname{diag}U-\kappa\otimes I)
 =\dim\operatorname{Fix}(U_{h_k}\cdots U_{h_1})
$$

on these sites: every coordinate is determined by the first, which must be
fixed after one circuit. Disjoint cycles can be combined. For
$U_h=\pi(h)^{-1}$ and $abc=e$, the ordered sites $(a,b,c)$ therefore
carry kernel $n$, in every characteristic and with one common decoder for
all representations. Repeated letters are not distinct sites. Length-one
cycles and forced inverse cancellations must be separated from claims about
generic tuples having no relations.

Let $m>0$ be a lower bound for the dimensions of all nontrivial complex
irreducible representations of $G$. We use the counting estimate

$$
\left|\#\{(a,b)\in A\times B:ab\in C\}
 -\frac{|A||B||C|}{d}\right|
 \le\sqrt{\frac{d|A||B||C|}{m}}. \tag{1}
$$

This is the estimate in the proof of Theorem 3.3 of
[W. T. Gowers, *Quasirandom Groups*, arXiv:0710.3877v1, pp. 11–12](https://arxiv.org/pdf/0710.3877v1).
The journal version is *Combinatorics, Probability and Computing* 17 (2008),
363–387, [doi:10.1017/S0963548307008826](https://doi.org/10.1017/S0963548307008826).

**Packing bound.** Define

$$
r_0=\left\lceil\max\left((4/m)^{1/3}d,\sqrt{6d}\right)\right\rceil.
$$

Every subset $A\subseteq G$ contains at least
$\max(0,(|A|-r_0)/3)$ disjoint triples of distinct elements with product
$e$, where a nonintegral lower bound has its usual integer interpretation.

*Proof.* If a remaining subset $R$ has size $t>r_0$, (1) with
$A=B=R,C=R^{-1}$ gives more than $t^3/(2d)>3t$ ordered product-one
triples. At most $3t$ have a repeated entry: specify which equality holds
and its common value; the third entry is determined. Thus a distinct-entry
triple remains. An inclusion-maximal disjoint packing leaves at most $r_0$
vertices, proving the assertion. No inverse-free assumption is needed. ∎

This strengthens the coarse constant in Fable's Proposition 7. Its bound
$d/243-1$ is also correct when $m\ge108$, $A\cap A^{-1}=\varnothing$,
and $|A|\ge d/3$: (1) gives at least $d^2/54-3d$ distinct-entry
ordered triples, and each selected triple meets at most $9d/2$ of them.

**Consequence for the one-sided certificate.** Choose one element from
each nontrivial inverse pair, giving a maximal inverse-free set $A$.
Write $i=\#\{g:g^2=e\}$, so $|A|=(d-i)/2$. Set
$W=\operatorname{span}\pi(\Sigma)$, and let $F_W(A,\pi)$ be the largest
unpaired kernel on $A$, with $U_h=\pi(h)^{-1}$ and arbitrary $W$-valued
decoder blocks. The expression that pays for every coordinate outside
$A$ and then uses this unrestricted unpaired maximum is

$$
\mathcal B_W(A,\pi)=n(d-|A|)+F_W(A,\pi).
$$

To see the upper-bound step, project a paired code onto the coordinates
outside $A$. In the kernel of this projection, only $x_h$ for $h\in A$
can be nonzero. The equations at rows $h^{-1}$ give
$\pi(h)^{-1}x_h=\sum_{t\in A}K[h^{-1},t]x_t$, an unpaired system with
$W$-valued blocks. Rank-nullity gives the bound by $\mathcal B_W$;
the remaining paired equations are discarded.

The scalar cycle construction is admissible because $I_n\in W$. It proves,
uniformly over the choice of $A$,

$$
F_W(A,\pi)\ge\frac{|A|-r_0}{3}n,\qquad
\mathcal B_W(A,\pi)\ge\frac{2d+i-r_0}{3}n. \tag{2}
$$

The same bounds already hold for the scalar space $W=\mathbb C I_n$.
Along nontrivial group families with $m\to\infty$, (2) gives
$\mathcal B_W(A,\pi)\ge(2/3-o(1))dn$. Indeed, $r_0=o(d)$. Also
$i=o(d)$: if $k$ is the number of conjugacy classes, then
$i^2\le dk$ and $k\le1+(d-1)/m^2$. For the first bound, involutions
$x,y$ with $xy=g$ require $xgx^{-1}=g^{-1}$, giving at most
$|C_G(g)|$ choices; summing gives $dk$. The second follows from the
sum of squared irreducible dimensions. The same triples work in every
representation, so in characteristic zero the summed certificate has a
$(2/3-o(1))d^2$ floor as well.

**This is a lower bound on an upper-bound expression, not a lower bound
on the paired code.** Equations discarded by the reduction may remove
all the extra freedoms. The result rules out deriving a half-rate theorem
by paying for an entire half and applying the unrestricted unpaired bound
to the remainder. A method retaining the discarded compatibility equations
is not ruled out. It also does not rule out using a weaker upper bound if
D4's quantitative requirements permit one. The generic statement (U) has
not been disproved; its proposed uniform extension to representation tuples
has.

## 2. What the ordered-group argument actually proves

In this section $G$ may be infinite. Suppose it has a bi-invariant total
order. For finite $\Sigma$ and
sites $S$ lying above every element of $\Sigma\cup\{e\}$, the map

$$
(y_g)_{g\in S}\longmapsto
\left(g y_g-\sum_{s\in\Sigma,h\in S}s\,\kappa_s[g,h]y_h\right)_{g\in S}
$$

is injective over $F[G]$, for every field. Take the largest support element
$\mu$ of a nonzero input and a coordinate $g$ containing it. The term
$g\mu$ cannot cancel: every right-hand support element is
$su\le s\mu<g\mu$.

For the covariant residual the target is $g x_{g^{-1}}$, so this argument
uses the coordinates $y_g=x_{g^{-1}}$. Let $S_0=S_0^{-1}$ be a finite
displacement set, $a=\max(\Sigma\cup\{e\})$, and restrict every
group-algebra coordinate to a common finite support set $B\subset G$.
Projection to $y$-coordinates $g\le a$ is injective on the code. Thus

$$
\dim_F C\le\frac{|B|}{2}
 \left(|S_0|+|S_0\cap[a^{-1},a]|\right). \tag{3}
$$

Inversion reverses the order, so each inverse pair outside the interval
contributes one determining coordinate and every site inside contributes
one. This proves the displayed count, including the identity.

A half-rate limit requires the interval term to be $o(|S_0|)$. This does
not follow from bi-orderability: in lexicographically ordered $\mathbb Z^2$,
take $a=(1,0)$ and $S_0=\{(0,j):1\le|j|\le N\}$; the entire set is
inside the interval. Nor does injectivity automatically descend to finite
quotients: $t-1$ is injective on $F[t,t^{-1}]$, but kills
$1+t+\cdots+t^{N-1}$ in $F[C_N]$. Hence Proposition 8 supplies an
ordered-support certificate, not an unconditional half-rate theorem on
ordered covers or finite quotients.

## 3. An exact baseline for scalar monomial decoders

Work over $\mathbb C$, and let $m_g$ be the largest eigenvalue
multiplicity of $\pi(g)$. In the diagonal-target coordinates, restrict
$K'$ to a scalar matrix times $I_n$ whose scalar matrix is monomial:
one nonzero entry in every row and column, with arbitrary nonzero weights.
The exact maximum kernel in this class on the full displacement set is

$$
M_\pi=\sum_{g\in G}\max(n/2,m_g). \tag{4}
$$

*Proof.* A cycle of length at least two contributes at most $n$, whereas
the right side pays at least $n/2$ per site. A singleton contributes at
most $m_g$. For attainment, $m_g=m_{g^{-1}}$. On each nontrivial inverse
pair use the unweighted two-cycle if $m_g\le n/2$, and two optimal
weighted singletons otherwise. For $g^2=e$, one has $m_g\ge n/2$,
so an optimal singleton suffices. ∎

This is not an upper bound for arbitrary dense scalar matrices, nor for
helper-valued blocks. Weighted singletons include eigenvalue loops, not
just group words equal to the identity. For the previously tested $A_5$
sectors of dimensions four and five, (4) gives 122 and 160 respectively.
The attained helper-valued dimensions 126 and 172 from
[the exact controls](twisted-swap-controls.md) therefore exceed this
specific baseline; they are not proved global maxima.

## 4. Helper-relative loops far from the helpers

Let $a,t\in G$ be involutions, $g=at\ne g^{-1}$, and assume
$a\in\Sigma$. Write $A=\pi(a)$, $T=\pi(t)$. In the original
twisted coordinates choose, on $\{g,g^{-1}\}$,

$$
K_{\rm pair}=\begin{pmatrix}0&A\\A&0\end{pmatrix}.
$$

The residual's two off-diagonal blocks are
$\pi(g)-A=A(T-I)$ and $\pi(g^{-1})-A=(T-I)A$. Consequently its
kernel has dimension $2\dim\operatorname{Fix}(T)$, in every field.
Over $\mathbb C$ this is $n+\chi_\pi(t)$.

**An exact $A_7$ instance.** Take $a=(1\,2)(3\,4)$,
$b=(1\,2\,3\,4\,5\,6\,7)$, $\Sigma=\{e,a,b\}$, and the standard
six-dimensional representation. Set $t=(1\,6)(2\,3)$, so
$g=(1\,6\,2\,4\,3)$. Both residual blocks have rank two: the pair has
kernel eight, versus the scalar-monomial optimum six on that pair.
Exact breadth-first enumeration gives distance fourteen from the identity
and thirteen from $\Sigma$ for both $g$ and $g^{-1}$, using the
symmetric alphabet $\{a,b,b^{-1}\}$. The Cayley diameter is fifteen.

On the full sector, (4) is 7738. Replacing this pair gives 7740. Replacing
all 42 disjoint improving inverse pairs from double transpositions gives
7822. These are attained lower bounds; 7738 is a proved optimum only
within the scalar-monomial class. No unrestricted sector optimum is claimed.

**Unbounded distance in simple groups.** For odd $m\ge7$, take
$G=A_m$, $a=(1\,2)(3\,4)$, $b=(1\,2\,\cdots\,m)$, and the standard
representation of dimension $n=m-1$. These helpers generate $A_m$:
$c=b^3ab^{-3}=(4\,5)(6\,7)$, and $(ac)^2$ is a three-cycle on
$\{3,4,5\}$; its conjugates by $b$ include the consecutive three-cycles,
which generate $A_m$.

Choose distinct $j,k\in\{5,\ldots,m\}$ and set $t=(1\,j)(2\,k)$. Then
$g=at$ has cycle type $(4)(2)$. The helper-pair kernel is $2n-4$.
The largest eigenvalue multiplicity of $\pi(g)$ is
$\max(n-4,2)$, so its scalar-monomial pair optimum is
$\max(n,2n-8)$. The gain is $\min(n-4,4)>0$.

There are $(m-4)(m-5)$ distinct choices of $g$. A ball of any fixed
radius in the three-letter symmetric alphabet has size bounded independently
of $m$. Thus, as $m\to\infty$, some such $g$, and also $g^{-1}$,
lie outside any fixed neighborhood of the helpers. This uses a faithful
irreducible sector, not an invisible central factor. No expansion bound
for this generating family is asserted.

**Meaning of the examples.** In diagonal-target coordinates these patches
are just two helper-relative loops. They require no multi-helper linear
combination; the earlier $I+B+B^2$ example is a different mechanism.
They refute distance from the helpers as a sufficient test for novelty
against the scalar closed-word baseline. They do not refute a baseline
that already includes all helper-relative loops.

More decisively, for the regular representation any nonidentity involution
$t$ has fixed-space dimension $d/2$, in every characteristic. Thus this
same helper patch has kernel $d$, exactly ordinary pairing on the two
sites. Over $\mathbb C$, sector gains and losses relative to ordinary
pairing cancel in the weighted sum because the regular character at
$t\ne e$ is zero. A distant gain in
one sector is therefore not evidence for a gain on the full array.

## 5. Reproduction, formal status, and the next test

From the repository root, run the exact standard-library computation:

~~~sh
python3 lean-backlog/tools/covariant_word_controls.py
~~~

It reuses the existing $A_5$ representations, checks rational residual
ranks, and enumerates the $A_7$ Cayley graph. Use
<code>--output receipt.json</code> to save the full matrices and shortest-word
certificates. The infinite family and packing bounds are written proofs,
not extrapolations from these finite checks.

[StatementsWholeRow.lean](../StatementsWholeRow.lean) now defines the open
linear D1 and D8 targets as propositions, with no asserted conjecture or
new axiom. D1 reuses <code>LeanMachine.WholeRow.rowCode</code>. D8 is the
ordinary field rank of the action of

$$
\mathcal A[g,h]=1_{h=g^{-1}}[g]
  -\sum_{s\in\Sigma}\kappa_s[g,h][s]
$$

on $F[G]^G$; it does not use an undefined vector-space rank over the
nondivision ring $F[G]$. Fixed-field and uniform-in-field versions are
separate. The file proves covariance, the coefficient orientation,
ambient dimension $d^2$, rank-nullity, and quantifier specialization.
The full change-of-coordinates equivalence with the whole-row code is
written and index-checked, not yet a Lean theorem. None of Sections 1–4
is Lean-verified by that file.

The next useful D8 computation must use one shared family $\kappa_s$,
measure the full regular-representation kernel, and name the baseline
class it exceeds. A sector-only gain, including a far one, is insufficient.
For impossibility, retain compatibility across the two halves instead of
applying (U) to an unrestricted remainder. Fable's D4 audit determines how
much deficit the machine argument actually needs; neither a half-rate
target nor a particular numerical threshold should be imposed without
that quantitative connection.
