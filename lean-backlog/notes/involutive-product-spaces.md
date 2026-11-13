# Involutive three-term decoders: paired cuts and product spaces

Hans Brende and GPT-6 Astra, 13 November 2026.

**Status:** written proofs, independently reviewed; not Lean-verified.
These results restrict the involutive-seed target from the
[three-term seed note](three-term-seed-assemblies.md). They do not settle
general three-term decoders, Problem R, or native tape transposition.

Let $E=F^d$, $d\ge1$, over any field, let $\tau$ exchange the tensor
factors, and write a minimal Kronecker decomposition

$$
K=\sum_{a=1}^r A_a\otimes B_a,\quad
\mathcal A=\operatorname{span}\{A_a\},\quad
\mathcal B=\operatorname{span}\{B_a\}.
$$

Both factor tuples are independent and their spans are intrinsic.
Put $K^\sigma=\tau K\tau$, $T=\tau K$,
$D(K)=\dim\ker(I-T)$, and $f(d)=d(d+1)/2$. The seed condition is
$T^2=I$, equivalently $K^\sigma K=I$. Except where stated otherwise,
assume this condition. Here an **involutive decoder** means $T^2=I$;
it need not satisfy $K^2=I$. Products of matrix spaces below
mean the **linear span** of all products, not their generated algebra.

The main conclusions are:

- A paired cut on one factor side forces the reverse cut on the other.
  The diagonal children remain involutive. Any above-pairing involutive
  counterexample therefore has a core that strictly expands every proper
  subspace on all four factor sides.
- $\dim(\mathcal B\mathcal A)+\dim(\mathcal A\mathcal B)\le r^2+1$.
  For three terms the sum is at most 10.
- For at most three terms, a single factor space contained in a unital
  space $W$ with $\dim W\le3$ and $\dim W^2\le5$ already gives
  $D(K)\le f(d)$, without involutivity. Consequently an involutive
  three-term decoder whose two factor spaces coincide and contain $I$
  cannot exceed pairing. All these statements include characteristic two.

## Paired cuts preserve the involutive target

Suppose $U,Z\le E$ have equal dimension $s$, with
$B_a(U)\subseteq Z$ for every $a$. Then

$$
A_a(Z)\subseteq U\quad\text{for every }a. \tag{1}
$$

Indeed, $K(E\otimes U)\subseteq E\otimes Z$. Since $K$ is invertible
and both spaces have dimension $ds$, this is equality. Applying
$K^{-1}=K^\sigma$ and then swapping gives
$K(Z\otimes E)=U\otimes E$. Quotient the first output factor by $U$:
$\sum_a(\pi_U A_a|_Z)\otimes B_a=0$. Independence of the $B_a$ proves
(1). A redundant presentation must first be replaced by a minimal one;
the conclusion concerns the intrinsic factor spaces.

Take paired bases adapted to $U,Z$. The change

$$
A'_a=Q^{-1}A_aP,\qquad B'_a=P^{-1}B_aQ
$$

makes both families upper block triangular with sizes $s,t=d-s$.
Moreover $\tau K'=(P^{-1}\otimes Q^{-1})T(P\otimes Q)$, so it
preserves involutivity and $D$. Let $K_1,K_2$ be the two diagonal
decoders. Each has at most $r$ terms and is involutive, and

$$
D(K)\le D(K_1)+st+D(K_2). \tag{2}
$$

If $\operatorname{char}F\ne2$, equality holds in (2).

To see all assertions at once, $T$ exchanges $Z\otimes E$ and
$E\otimes U$, so it preserves the filtration

$$
0\subseteq Z\otimes U\subseteq
(Z\otimes E)+(E\otimes U)\subseteq E\otimes E.
$$

The first and last graded operators are $\tau_sK_1$ and $\tau_tK_2$,
so their squares are identity. The middle operator exchanges two
$st$-dimensional summands by mutually inverse maps. Its fixed space is
a graph and has dimension $st$. Fixed-space dimension is at most the
sum of fixed-space dimensions on an invariant subspace and its quotient:
restrict the quotient map to fixed vectors. Applying this twice proves
(2). Outside characteristic two, averaging $v\mapsto(v+Tv)/2$ lifts
every fixed quotient vector, proving equality.

Equality can fail in characteristic two: at $d=2$,
$K=I\otimes I+E_{01}\otimes E_{01}$ is involutive, its two scalar
children have dimension 1, but $D(K)=2<1+1+1$.

**Core reduction.** Fix a field and a term bound $r$. A smallest
involutive decoder with $D(K)>f(d)$, if one exists, satisfies

$$
\dim\mathcal B(U)>\dim U
\quad(0\ne U\ne E), \tag{3}
$$

and the same statement holds for $\mathcal A,\mathcal A^T,\mathcal B^T$.
Invertibility already forbids a shrinking joint image: the restriction
of $K$ to $E\otimes U$ is injective and has image in
$E\otimes\mathcal B(U)$. If equality of dimensions holds, (1)--(2)
give smaller involutive children. Minimality and
$f(s)+st+f(t)=f(d)$ contradict $D(K)>f(d)$. Exchanging factors gives
the other side. Transposing $K$ preserves $D$ and involutivity, since
$\tau K^T=\tau T^T\tau$, giving the two transposed sides.

Equivalently, successive cuts of any counterexample retain an
above-pairing child until such a core remains. Minimality over $F$
gives expansion for $F$-subspaces. For expansion over an algebraic
closure, first extend a counterexample and choose a smallest one there.
This reduction concerns involutive decoders above $f(d)$; it does not
assert the earlier $f(d)+3$ reduction for arbitrary decoders.

## The two product spaces must be small together

Set $p=\dim(\mathcal B\mathcal A)$ and
$q=\dim(\mathcal A\mathcal B)$. Involutivity gives

$$
\sum_{a,b}B_aA_b\otimes A_aB_b=I\otimes I.
$$

Let $X,Y$ have columns $\operatorname{vec}(B_aA_b)$ and
$\operatorname{vec}(A_aB_b)$, indexed by $(a,b)$. Realignment gives
$XY^T=\operatorname{vec}(I)\operatorname{vec}(I)^T$, of rank one.
Since $\operatorname{rank}X=p$, $\operatorname{rank}Y=q$, the rank
inequality for a product yields

$$
p+q\le r^2+1. \tag{4}
$$

Slicing the tensor identity by a functional taking $I$ to 1 shows that
$I$ lies in both product spaces. No division by $d$ or use of trace is
needed. These conditions are invariant under recombination and paired
base changes, which conjugate the two product spaces.

The identity also retains information discarded by (4):
$\dim(\operatorname{im}Y^T\cap\ker X)=q-1$ and
$\dim(\operatorname{im}X^T\cap\ker Y)=p-1$. A dimension profile alone
is not sufficient for involutivity.

For $r=3$, suppose one factor space contains an invertible matrix $G$.
After exchanging sides if necessary, use $Q=G,P=I$ to make
$\mathcal A'=G^{-1}\mathcal A$ contain $I$, with
$\mathcal B'=\mathcal B G$. Both product spaces contain
$\mathcal B'$, so $p,q\ge3$. If either dimension equals 3, that
product space equals $\mathcal B'$ and contains $I$. Therefore
$\mathcal A'\subseteq\mathcal B'$, and equality of dimensions makes
them the same three-dimensional unital algebra. Over an algebraic
closure it has only one-dimensional simple modules: a simple module
of dimension $n$ gives a full matrix-algebra image, so $n^2\le3$.
This is the density step from the earlier
[factor-algebra bound](finite-field-expansion.md).
The common scalar flag and Paper 17's flag theorem give $D(K)\le f(d)$.
Thus an above-pairing candidate in this nonsingular branch must have,
up to exchanging the sides,

$$
(p,q)\in\{(4,4),(4,5),(4,6),(5,5)\}. \tag{5}
$$

The same conclusion holds if a factor space acquires an invertible
element after scalar extension. This is a finite list of dimension
profiles, not a finite list of operators. The branch where both factor
spaces remain entirely singular is separate.

### A small product span need not generate a small algebra

For any $d\ge3$ and any field, take $C e_i=e_{i+1\bmod d}$,
$A=E_{00}$, and

$$
\mathcal U=\operatorname{span}\{I,A,C\},\qquad
\mathcal V=\operatorname{span}\{I,A,AC\}.
$$

Inspecting entries gives

$$
\mathcal V\mathcal U=\operatorname{span}\{I,A,C,AC,AC^2\},
\quad\dim(\mathcal V\mathcal U)=5,
$$
$$
\mathcal U\mathcal V=\operatorname{span}\{I,A,C,AC,CA,CAC\},
\quad\dim(\mathcal U\mathcal V)=6.
$$

The five-dimensional space contains $A,C$, which generate every matrix
unit via $C^iAC^{-j}$. Its generated algebra is all $\operatorname{Mat}_d(F)$.
Thus a bound on just one mixed product space does not bound the generated
algebra or its simple constituents. The pair fails (4) by exactly one,
so no choice of a minimal three-term coupling between these factor
spaces can be involutive.

## A one-sided quadratic-growth exclusion

**Lemma.** Let $W\subseteq\operatorname{End}_F(E)$ contain $I$, with
$\dim W\le3$ and $\dim W^2\le5$. Over an algebraic closure, every
simple constituent of the algebra generated by $W$ on $E$ has dimension
at most 2.

**Proof.** Work over an algebraic closure. Dimensions and relations
survive extension. Dimension at most 2 for $W$ gives a one-generator
algebra, whose simple constituents have dimension 1. Otherwise write
$W=\operatorname{span}\{I,x,y\}$. There are at least two independent
quadratic relations modulo $W$, since the four products
$x^2,xy,yx,y^2$ span a space of dimension at most 2 modulo $W$.
Choose a two-dimensional pencil $R$ of their $2\times2$ coefficient
matrices. Work on a finite-dimensional simple constituent. If the
images of $I,x,y$ become dependent, it again has dimension 1.

If $R$ contains a rank-one matrix whose two factor lines differ, change
generators to obtain $xy=ax+by+cI$. Then
$(x-bI)(y-aI)=(c+ab)I$. If the scalar is nonzero, the generators
commute. If it is zero, $\ker(x-bI)$ is invariant under both generators,
so simplicity forces one shifted generator to vanish. Either way the
simple constituent has dimension 1.

We may therefore assume every rank-one point of $R$ is a scalar square
of a linear form. The determinant polynomial on the pencil cannot
vanish identically: two independent such squares have independent
factor lines, and their sum has rank two. Its roots are either two
distinct projective points or one double point.

If there are two distinct roots, change generators so the relations are
$x^2=ax+by+cI$ and $y^2=ex+fy+gI$. If $b$ or $e$ is nonzero, one
generator is polynomial in the other. Otherwise both satisfy scalar
quadratics. For such generators, say
$x^2=ax+cI$, $y^2=fy+gI$, the element
$z=xy+yx-ay-fx$ commutes with both. An eigenspace of $z$ is invariant,
so $z$ is scalar on a simple constituent. For an eigenvector $v$ of
$x$, the nonzero space $\operatorname{span}\{v,yv\}$ is invariant
under both generators, and is the whole constituent. Its dimension is
at most 2. This argument uses no division by 2.

For a double root, take its square to be $x^2$ and subtract its
multiple from the other relation. The determinant pencil then shows
that the relations have the form

$$
x^2=\alpha x+\beta y+\gamma I,\qquad
bxy+cyx=ux+vy+wI,\qquad b,c\ne0.
$$

If $\beta\ne0$, one generator is polynomial in the other. Otherwise
$x$ satisfies a scalar quadratic. If $b=c$, divide the second relation
by $b$ and rename $u,v,w$. The element $y^2-uy$ is central, because
$[x,y^2]=u[x,y]$. It is scalar on the simple constituent, so both
generators satisfy scalar quadratics and the preceding argument applies.

Finally let $b\ne c$. If the quadratic for $x$ has distinct roots
$\lambda,\mu$, the two off-diagonal blocks of $y$ have coefficients
$b\lambda+c\mu-v$ and $b\mu+c\lambda-v$. These cannot both vanish.
If both eigenspaces occur, one is a nonzero proper invariant subspace,
contradicting simplicity. Otherwise $x$ is scalar.

If the root is repeated, write $x=\lambda I+N$, $N^2=0$. A scalar
$x$ is already settled. The other relation becomes
$bNy+cyN=u'N+v'y+w'I$. If $v'\ne0$, the operator
$L(Z)=bNZ+cZN$ satisfies $L^3=0$; hence $L-v'I$ is invertible with
polynomial inverse preserving $\operatorname{span}\{I,N\}$. This
forces $y$ into that span. If $v'=0$, multiply the relation by $N$
on its two sides: $cNyN=w'N=bNyN$. Thus $NyN=0$ and $w'=0$.
The relation now makes $\ker N$ invariant under $y$, contradicting
simplicity when $N\ne0$. This exhausts the cases, including
characteristic two. ∎

**Three-term consequence.** Suppose $K$ has at most three terms and
one factor space lies in such a $W$. Then

$$
D(K)\le f(d). \tag{6}
$$

Indeed, after scalar extension the lemma gives a composition series
with block sizes $s_i\in\{1,2\}$ on that factor side. Paper 18's
unequal-block-defect theorem applies to this one-sided flag and gives

$$
D(K)\le\sum_{i<j}s_i s_j+\sum_iD(K_i).
$$

Each actual diagonal compression still has at most three terms. Its
dimension is at most 1 in size 1, and at most 3 in size 2: dimension 4
would require $K_i=\tau_2$, whose Kronecker rank is 4. Thus
$D(K_i)\le f(s_i)$ and the displayed sum is $f(d)$. Neither
involutivity nor equality of the two factor spaces is needed for (6).

In particular, if an involutive minimal three-term decoder has
$\mathcal A=\mathcal B=W$ with $I\in W$, (4) gives
$2\dim W^2\le10$, and (6) excludes positive excess. The same holds
if a permitted paired change makes the factor spaces coincide and
contain $I$. The generated algebra need not have bounded total
dimension; only its simple constituents were bounded.

## What remains for the seed target

Fable's [two-term equality theorem](two-term-equality.md) now closes the
dimension-three gap: a three-term code there has dimension at most 6
or exactly 8. In the latter case $K=\tau-uv^T$ is the classified
codimension-one operator, with $u=\operatorname{vec}(G)$ and
$v=\operatorname{vec}(G^{-1})$. Thus $v^T\tau u=d=3$.
Putting $Q=\tau uv^T$ gives
$Q^2=3Q$ and $(\tau K)^2=I+Q\ne I$ over every field.
Sizes 1 and 2 also cannot give an above-pairing involutive three-term
seed. Consequently any core from (3) has dimension at least 4.

The remaining core must combine the paired relation constraint with
strict expansion, escape the common-unital-space case, and, over
$\mathbb C$, also escape the
[local-unitary obstruction](three-term-seed-assemblies.md).
The profiles (5) for spaces not admitting the common-unital normalization,
and entirely singular factor spaces, are still open. Equal spaces need
not contain $I$; that further case was not excluded. No lower bound on native transposers or
density statement about all possible transposers follows from these
restrictions on the algebraic seed target.

## Sources, checks and formal status

- Paper 17's flag theorem and two-term bound; Fable's new equality
  theorem and its codimension-one classification at `3556a3b`.
- [Paper 18, Unequal block defects](../../Capacity-and-Composition-of-Shared-Transposition-Decoders/paper/sections/appendix-block-defects.tex),
  with Lean coordinate theorem `ConstructionBlockDefects.finrank_upperBlockAgreement_le`.
- The scalar-quadratic-generator subcase is classical; see Vesselin
  Drensky, Jenő Szigeti and Leon van Wyk,
  [*Algebras generated by two quadratic elements*](https://arxiv.org/abs/0911.5431v1).
  The elementary proof needed here is included above. No novelty claim
  is made for that subcase or for the product-rank inequality.

The new paired-cut and quadratic-growth arguments are written proofs,
not Lean formalizations. The primary external source and repository
sources were checked at `2eec0d4`. Exact finite diagnostics are in
[product_space_controls.py](../tools/product_space_controls.py):

```sh
python3 lean-backlog/tools/product_space_controls.py
```

These controls are not used as proofs. The published quick checks of
the two-term equality note were also rerun successfully; the large
Rust enumerations were not repeated.
