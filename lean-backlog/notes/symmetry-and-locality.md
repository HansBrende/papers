# Symmetry and locality barriers for whole-row decoders

Claude Fable 5.2 and GPT-6 Astra, 14 November 2026. Front D1.

This note audits and strengthens §14 of [the row-spread note](row-spread-of-cones.md).
The results have independently reviewed written proofs, not Lean formalizations.
The finite tables are exact computations with reproducible certificates.
No unrestricted whole-row bound or native transposer exclusion follows.

The symmetry bound improves to a cubic moment in good characteristic,
and a filtration argument gives a uniform half-rate limit over every field.
A separate argument repairs the local-rule claim: agreement outside
few output coordinates is false, but agreement up to rank $O(d)$ holds under
a precise locality hypothesis. We also identify exactly what a universal
zero-corner argument can prove, and screen the proposed sector profiles.

## 1. A sharp bound for twisted symmetry

Let $V=F^d$, and let $K:V\otimes V\to V\otimes V$ be linear.
A code using $K$ as its decoder is a subspace of $\operatorname{Fix}K$;
it need not equal that full space. The full fixed space is itself a code
for the same decoder.

**Swapped blocks.** If $V=\bigoplus_i E_i$ and

\[
K(E_i\otimes E_j)\subseteq E_j\otimes E_i,
\]

then, over every field,

\[
\dim\operatorname{Fix}K\le\frac{d^2}{2}
  +\frac12\sum_i(\dim E_i)^2.                 \tag{1}
\]

Indeed, on an off-diagonal pair a fixed vector $a+b$ satisfies $b=Ka$,
so its dimension is at most that of either summand. A diagonal block is
bounded by its full dimension. This proves Fable's Proposition 14.1 without
an invertibility or characteristic hypothesis.

**Cubic symmetry bound.** Let a finite group $H$ act on $V$, with

\[
V=\bigoplus_\sigma V_\sigma\otimes M_\sigma,
\qquad n_\sigma=\dim V_\sigma,\quad a_\sigma=\dim M_\sigma,
\]

over a splitting field of characteristic not dividing $|H|$. The
$V_\sigma$ are pairwise nonisomorphic irreducible $H$-modules and
$M_\sigma$ are multiplicity spaces with trivial $H$-action. Suppose

\[
K(L(h_1)\otimes L(h_2))=(L(h_2)\otimes L(h_1))K.
                                                               \tag{2}
\]

Then

\[
\boxed{\dim\operatorname{Fix}K\le\frac{d^2}{2}
             +\frac12\sum_\sigma n_\sigma a_\sigma^2.}          \tag{3}
\]

*Proof.* The operator $\tau K$ commutes with $H\times H$. Schur's
lemma exchanges unequal isotypic pairs as in (1). On an equal-type block,
reorder the factors as

\[
(V_\sigma\otimes V_\sigma)\otimes(M_\sigma\otimes M_\sigma).
\]

There $K=\operatorname{flip}_{V_\sigma}\otimes D_\sigma$ for an arbitrary
endomorphism $D_\sigma$ of the multiplicity tensor square. With $n=n_\sigma$
and $a=a_\sigma$, its fixed dimension is exactly

\[
n\dim\ker(I-D_\sigma)+\binom n2\dim\ker(I-D_\sigma^2)
\le \frac{n(n+1)}2a^2.                       \tag{4}
\]

To see this, each diagonal basis tensor carries $D_\sigma$, and each
unordered pair of distinct basis tensors has equations $x=D_\sigma y$,
$y=D_\sigma x$. This proof works in characteristic two as well; it does
not diagonalize the flip into positive and negative eigenspaces. Summing
the half contributions from unequal types and (4) proves (3). ∎

The bound is sharp among all split twisted intertwiners: take
$D_\sigma=I$, and use the ordinary tensor swap between unequal types.
This need not respect a prescribed sparse helper relation, so it is not
an attaining whole-row construction for arbitrary $T$.

For $H\le G$, $|G|=d$, $|H|=h$, let $V=F[G]$ with left translation.
Its multiplicities are $a_\sigma=(d/h)n_\sigma$, giving

\[
\dim\operatorname{Fix}K\le\frac{d^2}{2}
 +\frac{d^2}{2h^2}\sum_\sigma n_\sigma^3
 \le\frac{d^2}{2}+\frac{d^2}{2\sqrt h}.        \tag{5}
\]

The last step uses $\sum n_\sigma^2=h$ and $\max n_\sigma\le\sqrt h$.
Thus growing symmetry alone suffices in good characteristic; no
quasirandomness assumption is needed. The upper bound extends to any
base field of characteristic not dividing $h$ by scalar extension,
which preserves rank. Sharpness over a nonsplitting base field is not
asserted. Semisimplicity remains essential to this proof.

For the whole-row relation $\rho(r)=rT$, write coefficients as

\[
K(X)_{c,r}=\sum_{t\in T,\ x\in G}k(c,r;rt,x)X_{rt,x}.
\]

Condition (2) is precisely

\[
k(c,r;i,x)=k(h_2c,h_1r;h_1i,h_2x).             \tag{6}
\]

For $H=G$, these are the constant templates

\[
K_0(X)_{c,r}=\sum_{t\in T,\ y\in G}\phi(t,y)X_{rt,cy}.       \tag{7}
\]

One-way helpers and arbitrarily many terms are allowed. Twisted covariance
of the decoder is not ordinary $H\times H$ invariance of its fixed code:
only the diagonal subgroup automatically preserves that code. A nonlinear
extension must specify which of these different hypotheses it assumes.

### The uniform bound holds in every characteristic

**Common-algebra bound.** Over any field, let
$\mathcal A\subseteq\operatorname{End}(V)$ be a unital algebra of dimension
$c$. If $\tau K\in\mathcal A\otimes\mathcal A$, then

\[
\boxed{\dim\operatorname{Fix}K\le\frac{d^2+d\sqrt c}{2}.}       \tag{5a}
\]

*Proof.* Extend scalars to an algebraic closure; all relevant dimensions
are unchanged. Choose an $\mathcal A$-composition flag
$0=V_0\subset V_1\subset\cdots\subset V_s=V$, with successive dimensions
$a_i=\dim(V_i/V_{i-1})$. The density theorem makes the action on each simple quotient
surjective onto its full endomorphism algebra, so $a_i^2\le c$.
This is [Etingof et al., *Introduction to representation theory*,
Theorem 3.2.2](https://math.mit.edu/~etingof/reprbook.pdf); it does not
require characteristic zero or a semisimple algebra.

Since each tensor factor preserves the flag,
$K(V_i\otimes V_j)\subseteq V_j\otimes V_i$.
Filter $V\otimes V$ by total index:
$U_t=\sum_{i+j\le t}V_i\otimes V_j$. On its associated graded space,
$K$ exchanges the $(i,j)$ and $(j,i)$ blocks. An adapted vector-space
basis proves this directly: each factor index can only decrease, so
preserving their sum permits only the swapped pair. The paired-block
argument therefore bounds the graded fixed dimension by
$(d^2+\sum_i a_i^2)/2$. Finally
$(\operatorname{Fix}K\cap U_t)/(\operatorname{Fix}K\cap U_{t-1})$
injects into $\ker(I-\operatorname{gr}_t K)$. Summing and using
$\sum_i a_i=d$ gives
$\dim\operatorname{Fix}K\le(d^2+\sum_i a_i^2)/2
\le(d^2+d\sqrt c)/2$. ∎

**All-field symmetry bound.** Under (6), for any $H\le G$ and any field,

\[
\boxed{\dim\operatorname{Fix}K\le
          \frac{d^2}{2}+\frac{d^2}{2\sqrt{|H|}}.}              \tag{5b}
\]

Indeed, let $\mathcal A=\operatorname{End}_H(F[G])$. The operator $\tau K$
commutes with the independent $H$-actions, hence lies in
$(\mathcal A\otimes\operatorname{End}V)\cap
(\operatorname{End}V\otimes\mathcal A)=\mathcal A\otimes\mathcal A$.
Both equalities follow by expanding in a basis of $\operatorname{End}V$
extending one of $\mathcal A$; no semisimplicity is involved.
A commuting matrix is constant on diagonal $H$-orbits of $G\times G$.
That action is free, so $\dim\mathcal A=d^2/|H|$. Now apply (5a).

This removes the field restriction for the uniform bound. Formula (5)'s
sharper cubic expression and its stated sharpness still have their
good-characteristic hypotheses. More generally, any common factor
algebra of dimension $o(d^2)$ gives half rate plus $o(1)$ by (5a).

## 2. Universal zero corners give exactly independent sets

Let $R\subseteq[N]\times[N]$ be any support relation, and let
$\mathcal K_R$ consist of all matrices with arbitrary entries on $R$
and zero elsewhere. Let $\alpha(R)$ be the largest size of a set $S$
with no allowed ordered pair in $S\times S$; loops exclude their vertices.
Over every field,

\[
\boxed{\max\{\operatorname{rank}P:P^2=P,\ PKP=0
                      \text{ for every }K\in\mathcal K_R\}=\alpha(R).} \tag{8}
\]

*Proof.* Let $U$ and $V$ be the indices of nonzero rows and nonzero
columns of $P$, respectively. For an allowed matrix unit $E_{yx}$,
$PE_{yx}P$ is the outer product of column $y$ and row $x$. Hence there
is no allowed edge with $y\in V,x\in U$. In particular $S=U\cap V$
is independent. Idempotence gives $P=P I_S P$, since every other
summand in $P^2=\sum_i P e_i e_i^\top P$ vanishes. Therefore
$\operatorname{rank}P\le|S|\le\alpha(R)$. Conversely, projection onto
any independent coordinate set satisfies the required identities. ∎

For the regular mutual graph $M(X)=A X^\top A$, let $s_2$ be the second
singular value of $A/w$, $d\ge2$, and $N=d^2$. Its normalized least
eigenvalue is $-s_2$, as in [the two-token controls](two-token-and-oriented-controls.md).
The usual independent-set bound gives

\[
\operatorname{rank}P\le\alpha(M)\le \frac{Ns_2}{1+s_2}.       \tag{9}
\]

For completeness, if $z=1_S$ and $a=|S|/N$, independence and the least
eigenvalue imply $0=z^\top Mz/w^2\ge N(a^2-s_2a(1-a))$, which is (9).
In a fixed-space certificate, $PKP=0$ makes projection to the complement
of $\operatorname{im}P$ injective. Thus arbitrary changes of basis do not
improve the best such **universal free-coefficient** certificate at all.
This is not a restriction on one fixed decoder, whose coefficients may
cancel, nor on all possible capacity proofs. The earlier bound for deletion
to a bipartite graph concerns a different optimization.

## 3. A precise local rule is a low-rank perturbation

Use the coloured incidence graph with row ports $A_i$, column ports $B_j$,
and an edge labelled $t\in T$ from $B_j$ to $A_{jt}$. It has maximum
degree $w=|T|$. Fix a radius $R\ge0$.

**Locality hypothesis.** The coefficient $k(c,r;rt,x)$ depends only on the
isomorphism type of the induced union of radius-$R$ balls around the four
ordered ports

\[
(A_c,B_r,A_{rt},B_x).
\]

Isomorphisms preserve port roles, colours and generator labels. They do not
retain global vertex names or additional labels. The coefficient function
may depend on $G$; its values need not be bounded.

Then, over every field, there is a constant template $K_0$ as in (7) with

\[
K=K_0+L+E,\qquad \operatorname{rank}L\le d,\qquad
\operatorname{rank}E\le d\sum_{j=0}^{4R+3}w^j.                \tag{10}
\]

*Proof.* Put $Q=2R+1$ and define

\[
Y=\{y:\operatorname{dist}(A_e,B_y)\le Q\},\quad
V_t=\{v:\min(\operatorname{dist}(B_e,B_v),
                    \operatorname{dist}(A_t,B_v))\le Q\}.
\]

Call $(c,r)$ good if $\operatorname{dist}(A_c,B_r)>2Q+1$, allowing
infinite distance. Its $c$-ball and its $(r,rt)$-cluster have no common
vertex or connecting edge. The $x$-ball can attach to at most one of
them; otherwise the distance would be at most $Q+Q+1$. Thus $cY$ and
$rV_t$ are disjoint. Independent left translations of the disconnected
clusters show that the coefficient is respectively

- $\alpha_{t,y}$ when $x=cy$, $y\in Y$;
- $\beta_{t,v}$ when $x=rv$, $v\in V_t$;
- $a_t$ when neither occurs.

These values depend on the displayed relative parameters, not on $c,r$.
Internal cycles are preserved by translation, so no girth assumption is
needed. Extend the coefficient function arbitrarily to any unrealized
disjoint templates; these do not change a realized good coefficient.

Take $\phi(t,y)=1_Y(y)(\alpha_{t,y}-a_t)$ in (7), and set

\[
L(X)_{c,r}=\sum_{t\in T}\left[
 a_t\sum_xX_{rt,x}
 +\sum_{v\in V_t}(\beta_{t,v}-a_t)X_{rt,rv}\right].           \tag{11}
\]

On good outputs $K_0+L$ has exactly the three coefficients above. The
output of $L$ is independent of $c$, so its rank is at most $d$.
The residual $E$ has nonzero rows only at output cells whose two ports
are at distance at most $4R+3$; their number is bounded as in (10). ∎

Consequently $\dim\operatorname{Fix}K\le\dim\operatorname{Fix}K_0+O_{w,R}(d)$.
Apply (5b) with $H=G$: on **every** growing finite-group family, over
**every** field, such rules have rate at most
$1/2+1/(2\sqrt d)+O_{w,R}(1/d)$.

The earlier claim of agreement outside $O(d)$ output cells was false:
with $e\in T$, the radius-one rule $K(X)_{c,r}=X_{r,r}$ is local in the
four-port sense. Its template at sector $g=c^{-1}r$ is supported only at
$(t,y)=(e,g)$. No constant template matches it on more than $d$ output
rows. Its rank is at most $d$, however, so (10) handles it directly.

## 4. Amenable sources: all alphabets, not only linear codes

Suppose a fixed marked finitely generated amenable group $(\Gamma,S)$
maps onto each $(G_i,T_i)$, preserving the specified generators, with
fixed generator budget. These bounded-degree Cayley graphs are uniformly
hyperfinite: after deleting an arbitrarily small fixed fraction of edges,
all remaining components have uniformly bounded size.

Here is the uniformity argument. Every marked convergent subsequence has
a limit that is a quotient of $\Gamma$, hence amenable. For an infinite
limit, the convergent finite Cayley sequence is its sofic approximation
and is hyperfinite by Elek–Szabó, Proposition 4.1. For a finite marked
limit, the generated Cayley components eventually have its bounded size,
so hyperfiniteness is immediate. If the whole family were not
uniformly hyperfinite, a sequence failing a fixed deletion budget at
component thresholds tending to infinity would have such a convergent
subsequence, a contradiction. This is also consistent with Schramm's
Theorem 1.1 on hyperfinite graph limits; amenability-to-hyperfiniteness is
an additional input, not the statement of that theorem alone.

For incidence graphs, delete both port copies of endpoints of removed
Cayley edges. This changes the deletion fraction by a constant and bounds
component sizes by twice the original bound. The
[row-separator bound](window-pages-and-input-attachments.md#2-a-sufficient-row-separator-bound)
then gives rate $1/2+o(1)$ for every whole-row code, uniformly over finite
alphabets and with no linearity assumption. It also applies to disjoint
cosets if $T_i$ generates only a subgroup. Fixed derived length and a fixed
generator budget fit by taking a fixed free solvable source group.

The marking condition matters: abstract quotient isomorphisms with unrelated
generating sets are not this hypothesis. Positive limiting gain requires a
non-hyperfinite family. This does not establish expansion as necessary.

Sources: G. Elek and E. Szabó, *Sofic representations of amenable groups*,
Proc. AMS **139** (2011), 4285–4291,
[Proposition 4.1](https://arxiv.org/html/1010.3424v2#S4);
O. Schramm, *Hyperfinite graph limits*, ERA **15** (2008), 17–23,
[Theorem 1.1](https://arxiv.org/abs/0711.3808).

## 5. The SL₂ calibration

Let $p\ge5$ be prime, $G=\mathrm{SL}_2(\mathbb F_p)$, $d=p(p^2-1)$, and

\[
T=\{I,A,B\},\quad A=\begin{pmatrix}1&2\\0&1\end{pmatrix},\quad
B=\begin{pmatrix}1&0\\2&1\end{pmatrix}.
\]

The integral generators are free; their reductions generate $G$ and
give an expanding family. The incidence graphs have girth $\Omega(\log p)$
and local limit the three-regular tree. Freeness prevents a reduced walk
from closing over the integers, and matrix-entry growth gives the stated
girth bound modulo $p$. Expansion follows from Bourgain–Gamburd's theorem:
for $P=(I+R_A+R_B)/3$, its singular gap is controlled by the Dirichlet
gap of the symmetric generator set. See their
[*Uniform expansion bounds for Cayley graphs of SL₂(Fp)*](https://annals.math.princeton.edu/2008/167-2/p07),
Annals **167** (2008), 625–642, Theorem 1 and the example on p. 626.

There are $p+4$ ordinary irreducibles, with degrees and multiplicities

\[
1\ (1),\quad p\ (1),\quad p+1\ ((p-3)/2),\quad p-1\ ((p-1)/2),
\quad (p+1)/2\ (2),\quad (p-1)/2\ (2).
\]

See Böhmler–Farrell–Lassueur, *Trivial Source Character Tables of SL₂(q)*,
OWP 2022-02, [§2.5 and Table 1](https://publications.mfo.de/bitstream/handle/mfo/3916/OWP2022_02.pdf?isAllowed=y&sequence=1),
or Braun–Nebe, [*The orthogonal character table of SL₂(q)*, Theorem 4.1](https://arxiv.org/abs/1609.08852).
Writing $S_j=\sum_\pi n_\pi^j$, one obtains

\[
S_3=(2p^4-p^3-9p)/2,\qquad
S_4=(4p^5-3p^4+8p^3-42p^2-12p-3)/4.
\]

Define $X_m=T(T^{-1}T)^{m-1}$ and
$E_m=\{g:gX_mg\cap X_m^{-1}\ne\varnothing\}$, as in
[bounded sector coupling](bounded-sector-coupling.md). Exact enumeration gives:

| $p$ | $d$ | $\lvert E_1\rvert$ | $\lvert E_2\rvert$ | $\lvert E_3\rvert$ | Largest $m$ with $\lvert E_m\rvert<d/4$ | $S_4/d^2$ | $S_3/d^2$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| 5 | 120 | 10 | 62 | — | 1 | .182500000 | .037500000 |
| 7 | 336 | 10 | 88 | — | 1 | .134247449 | .019469246 |
| 11 | 1320 | 10 | 92 | 872 | 2 | .086907713 | .007992424 |
| 13 | 2184 | 10 | 104 | 954 | 2 | .073891539 | .005745247 |

Nestedness of $E_m$ certifies the maximum after the first failed gate.
For fixed mutual recovery support whose connected components each meet at
most $m$ sectors, the ceiling is $r_E=(d+|E_m|)/(2d)$.
The good-characteristic symmetry
ceiling is $r_3=1/2+S_3/(2d^2)$. At these chosen $m$, the maxima of the
two are respectively .541667, .514881, .534848 and .523810. These are
ceilings for **different restricted architectures**, not upper bounds on
all decoders. Exceeding both would rule out those two explanations for a
finite gain; falling below either does not classify a general decoder.
The ordinary pairing code has rate $(d+1)/(2d)$.

The old quartic allowance is 9.125 percentage points at $p=5$ and 6.712
at $p=7$, so it is not uniformly only a few percentage points. Optional
checks at $p=17,19,23$ give $E_1=10$, $E_2=94,86,94$; no maximal
passing $m$ is certified for those optional rows.

The full-group ordinary-character bounds do not directly apply over GF(2)
or GF(3), since both characteristics divide $d$. The universal bound (5b)
does apply there. Even before that upgrade, there was an all-field
bound for **actual** full-group or Borel twisted covariance: use the
abelian unipotent subgroup of order $p$ in characteristic different from
$p$, and the split torus of order $p-1$ in characteristic $p$. After
scalar extension, (1) already gives rate at most

\[
\frac12+\frac1{2(p-1)}.                       \tag{12}
\]

Thus Borel invariance was already asymptotically excluded. Its direct cubic
bound improves the finite formula in good characteristic, not a previously
open Borel asymptotic region. The Borel ordinary degrees are $p-1$ linear
characters and four of degree $(p-1)/2$: the nontrivial characters of its
normal $C_p$ form two torus orbits, each with stabilizer $\{\pm I\}$,
giving two extensions per orbit. The squared degrees exhaust its order.
See also Lafferty–Rockmore, *Fast Fourier Analysis for SL₂ over a Finite Field
and Related Numerical Experiments*, Experimental Mathematics **1** (1992),
[§7, pp. 136–137](https://www.cs.cmu.edu/afs/cs/usr/lafferty/www/pub/sl2.pdf).

Combining (10) and (5b) excludes the precise fixed-radius local-rule class
over every field on this family and on every other growing finite-group
family. Here it gives rate $1/2+O(p^{-3/2})+O_{w,R}(1/d)$.
Finally, $G$ is perfect, but not simple: its centre $\{\pm I\}$ is a
nontrivial normal subgroup. No normal-subgroup-free premise is used here.

## 6. Sector profiles: what survives the audit

Let $H\le G$. Depending on the double coset $H(c^{-1}r)H$ does **not**
imply (6). Under that action, $c^{-1}r$ becomes
$c^{-1}h_2^{-1}h_1r$, not $h_2^{-1}(c^{-1}r)h_1$. By contrast,
$rc^{-1}$ transforms by left and right $H$-multiplication. These are
different normal forms and must not be interchanged.

For the upper triangular Borel $H=\mathcal B$, take $c=r$ equal to the
Weyl matrix and $h_1=A,h_2=e$. The first sector is $e\in\mathcal B$;
the new one is a nontrivial lower unipotent, outside $\mathcal B$.
Thus a nonconstant Bruhat profile can break the stated symmetry.

It is nevertheless excluded by a simpler argument. SL₂ has two Bruhat
double cosets, and $|\mathcal B|/d=1/(p+1)$. A rule

\[
\phi_g(t,y)=a_{t,y}+1_{\mathcal B}(g)b_{t,y},\qquad g=c^{-1}r,
\]

differs from its constant template on only $d|\mathcal B|=d^2/(p+1)$
output coordinates. Rank perturbation and (5b) with $H=G$, over every field, give

\[
\frac{\dim\operatorname{Fix}K}{d^2}
 \le\frac12+\frac1{2\sqrt d}+\frac1{p+1}.      \tag{13}
\]

A more balanced algebraic test is the square class of $\operatorname{tr}(g)^2-4$.
The split regular, nonsplit regular and zero-discriminant proportions are
respectively

\[
\frac{p-3}{2(p-1)},\qquad \frac{p-1}{2(p+1)},\qquad
\frac{2p}{p^2-1}.
\]

Indeed, there are $(p-3)/2$ split regular trace values with $p(p+1)$
elements each, $(p-1)/2$ nonsplit values with $p(p-1)$ each, and $p^2$
elements for each trace $\pm2$. Both regular classes have positive limiting
density, so replacing one by a constant incurs a positive fraction of all
output rows. The sparse-perturbation exclusion does not settle this family.

Nor do two profile values automatically give bounded Kronecker rank. For
a nonconstant central complex function $f$, the diagonal multiplier
$D_f e_{c,r}=f(c^{-1}r)e_{c,r}$ has operator Kronecker rank equal to the
rank of $[f(c^{-1}r)]_{c,r}$. Its central Fourier blocks show that this
rank is at least $(p-1)^2/4$: some nontrivial irreducible block is nonzero.
The example $D_f\tau$ proves only this obstruction to a bounded-repertoire
reduction; its paired support is not a useful construction.

**Stopping screen.** Now take $f$ to be a split/nonsplit indicator with
values in $\{0,1\}$. For mutual-only profiles restrict $y\in T^{-1}$, so

\[
K(X)_{c,r}=\sum_{t\in T,\ y\in T^{-1}}
  [a_{t,y}+f(c^{-1}r)b_{t,y}]X_{rt,cy}.         \tag{14}
\]

This has 18 parameters when $w=3$, but fixed bounded **complex** values
are already excluded by Paper 4, [Theorem A and extension (a)][P4A]. The
mutual support has degree at most $w^2$. First freeze its $O(dw)$ self-loop
cells. For each fixed length $\ell$, the two-token identity bounds the
remaining vertices on odd cycles of length at most $\ell$ by
$O_{w,\ell}(d)$; hence the loopless sequence is locally bipartite. The
same exclusion applies to coefficients bounded in a diagonal gauge outside
$o(d^2)$ rows (and to the stated tight-coefficient extension). Merely
writing visibly growing coefficients is not evidence of escape.

### The balanced profile: exact common algebra and stopping decision

Take the literal $0/1$ split-regular or nonsplit-regular indicator $f$,
with either fixed assignment on zero discriminant. It is nonconstant,
conjugation-invariant, and satisfies $f(-g)=f(g)=f(g^{-1})$.
These values remain distinct in characteristic two; reducing a signed
quadratic character modulo two would be a different profile.

**Proposition.** For the entire 18-parameter family (14), the least unital
common factor algebra satisfying $\tau K\in\mathcal A\otimes\mathcal A$
for every coefficient choice is

$$\mathcal A=\operatorname{End}_Z(F[G]),\qquad
 Z=\{I,-I\},\qquad \dim\mathcal A=d^2/2. \tag{15}$$

This holds over every coefficient field $F$, independently of the prime
$p\ge5$ defining the group. Each decoder in the family satisfies

$$\dim\operatorname{Fix}K\le3d^2/4. \tag{16}$$

*Proof of (15).* Put $(R_sv)(u)=v(us)$ and let $D_f$ multiply tensor
coordinates by $f(c^{-1}r)$. Inversion invariance gives

$$\tau K=\sum_{t,y}(a_{t,y}I+b_{t,y}D_f)(R_t\otimes R_y).$$

The unmasked basis terms force $R_A,R_B$ into every common algebra,
by contracting one tensor factor. They generate all right translations.
The masked term $t=y=e$ forces $D_f$; contracting its second factor
against a diagonal entry forces every diagonal mask
$M_r(c,c)=f(c^{-1}r)$.

The period subgroup $P=\{h:f(hx)=f(x)\text{ for every }x\}$ is normal,
since $f$ is central, contains $Z$, and is proper since $f$ is
nonconstant. Simplicity of $G/Z=\mathrm{PSL}_2(\mathbb F_p)$ gives
$P=Z$; see [Conrad, *Simplicity of PSL_n(F)*, Theorem 3.5](https://kconrad.math.uconn.edu/blurbs/grouptheory/PSLnsimple.pdf).
Consequently the masks $M_r$ distinguish exactly the $Z$-cosets of $c$.
For a chosen coset, multiply all $M_r$ or $I-M_r$ according to that
coset's binary value pattern. The product is its diagonal projector.
This uses no averaging or division.

Every mask and right translation commutes with left translation by
$-I$, giving containment in $\operatorname{End}_Z(F[G])$. Conversely,
for $c,b\in G$, the product $P_{cZ}R_{c^{-1}b}P_{bZ}$ has exactly
the two entries $(c,b)$ and $(-c,-b)$ equal to one. These orbit matrices
form a basis of the centralizer over every field, of dimension $d^2/2$.
Finally, $D_f$ is a linear combination of tensor products of the coset
projectors, so this algebra suffices for the whole family. ∎

*Proof of (16).* Write $J=L_{-I}$, a permutation with $d/2$ disjoint
transpositions. In characteristic different from two, its two
eigenspaces are invariant under every factor and each has dimension
$d/2$. Apply (1). In characteristic two, put $W=\ker(J-I)$, also of
dimension $d/2$. Every factor preserves $0\subset W\subset F[G]$.
On the tensor filtration

$$W\otimes W\ \subset\ W\otimes F[G]+F[G]\otimes W
 \ \subset\ F[G]\otimes F[G],$$

the first and last quotients each contribute at most $(d/2)^2$ fixed
dimensions; the two middle blocks are exchanged and contribute at most
$(d/2)^2$ together. Fixed dimensions are bounded by their associated
graded sum, as in (5a), giving (16). ∎

Equation (15) concerns one algebra for the **whole parameter family**.
An individual coefficient tuple may have a smaller algebra. The
$o(d^2)$ common-algebra criterion therefore does not exclude the family,
but no gain or attainment of (16) is supplied. This completes the one
algebra pass: the profile is parked unless a concrete cancellation
mechanism appears. It adds five restrictions to the wall question
(group relation, linearity, mutual recovery, this group family, this
profile). Enlarging its search without such a mechanism is not the
current direction.

## 7. Exact reproduction and proof status

From the repository root, using only the Python standard library:

```sh
python3 lean-backlog/tools/sl2-symmetry/counts.py --until-quarter
python3 lean-backlog/tools/sl2-symmetry/counts.py 17 19 23 --output sl2-optional.json
```

The first command regenerates the compact committed receipt. It scans all
$g,x$ and independently unions square-root fibres of $z^{-1}x$ over
unordered $x,z\in X_m$, asserting exact equality. Every exceptional $g$
has an explicit witness $gxgz=e$. Group orders, inverses, generation,
class counts, nestedness and character-degree arithmetic are also checked.
The degree classification itself comes from the cited sources, not from
the numerical identities. No optimizer or floating-point rank test is used.

All new capacity and normal-form arguments in this note are written proofs.
No new Lean result, unproved axiom or modification of the native frontier
is claimed. The elementary group identities already formalized in
[SectorWalks.lean](../SectorWalks.lean) remain available for later formalization.

[P4A]: ../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/codes-analytic.tex
