# Three-term seed assemblies and the constant-excess question

Hans Brende and GPT-6 Astra, 13 November 2026.

**Status:** written proofs, independently reviewed; not Lean-verified.
The conjecture under discussion is

$$
D(K)=\dim\ker(\tau_d-K)\le f(d)+3,\qquad
f(d)=d(d+1)/2,\qquad K=\sum_{a=1}^3 A_a\otimes B_a.
$$

The convention is $(A\otimes B)X=AXB^T$. This note proves the conjectured
bound for assemblies of the known seed, with arbitrary term recombinations
and compatible upper-block extensions. It also excludes complex three-term
decoders locally equivalent to a unitary, using an existing classification,
and corrects an inference about minimal counterexamples. The unrestricted
conjecture remains open; no classification of all three-term decoders is claimed.

## What surgery does and does not give

Put $E(K)=D(K)-f(d)$. The
[joint-image surgery lemma](finite-field-expansion.md) says, for $s+t=d$,

$$
E(K)\le E(K_1)+E(K_2)+dh,\qquad
h=\max\left(0,\dim\sum_aB_a(U)-s\right).
$$

Minimality of a counterexample to $E\le3$ only bounds the right side by
$6+dh$. It therefore does not force $h>0$. The earlier expansion reduction
used a linear error $Cd$, which is additive across a split; a constant
error 3 has a different accounting rule.

A partial expansion statement survives. In dimensions 1 and 2, three
terms have $E\le0$. For dimension 2, $D=4$ would require $K=\tau_2$,
whose Kronecker rank is 4: its two tensor-factor flattening is a rank-4
permutation matrix. Consequently a least-dimensional counterexample to
the +3 bound expands every nonzero proper subspace whose dimension or
codimension is at most 2, on all four sides $A,B,A^T,B^T$. A nonexpanding
such split would give $E\le0+3$. The first split not covered by this
argument is $3+3$ at dimension 6.

## A bound for all assemblies of the standard seed

Let $S_1=E_{01}-E_{10}$, $S_2=E_{02}-E_{20}$, and
$S_3=E_{12}-E_{21}$. The standard seed is

$$
K_*=-\sum_{a=1}^3 S_a\otimes S_a=\tau_3-\Pi,
\qquad \Pi(X)=\operatorname{tr}(X)I_3.
$$

Its agreement dimension is 8 over every field. Consider a common ordered
block partition consisting of $m$ blocks of dimension 3 and $s$ scalar
blocks, so $d=3m+s\ge1$. Suppose, in compatible independent bases for the
two factor spaces, both $A_a$ and $B_a$ are upper block triangular. Each
3-dimensional diagonal decoder is required to be equivalent to $K_*$
under a transpose-compatible change of bases. Its three-term decomposition
may be arbitrary. No restriction is placed on the scalar diagonal factors.
Then

$$
D(K)\le4m(m+1)+\frac{s(s+1)}2+2ms, \tag{1}
$$

and hence

$$
E(K)\le\frac{m(5-m)}2-ms\le3. \tag{2}
$$

The numerical bound (1) is attained by the standard identity lift and
scalar padding. The result includes characteristic two and finite fields.

### Aligning the three term bases

First assume the six factors are block diagonal. Kernel dimensions do not
change after scalar extension, so work temporarily over an algebraic
closure. Normalize each seed decoder to $K_*$. Its tensor rank is 3 and
both factor spaces are the alternating $3\times3$ matrices, with basis
$S_1,S_2,S_3$. Thus every minimal decomposition has the form

$$
A_a=\sum_i C_{ia}S_i,\qquad
B_a=-\sum_i(C^{-T})_{ia}S_i
$$

for some $C\in GL_3$. This follows by comparing coefficients of
$S_i\otimes S_j$.

Congruence $S\mapsto RSR^T$ acts on this space by the exterior-square
matrix $M(R)$. It satisfies $M(R^{-T})=M(R)^{-T}$. The map $R\mapsto
M(R)$ is onto over an algebraic closure in every characteristic: in the
usual signed dual basis it is $R\mapsto\det(R)R^{-T}$; for a target $C$
in those coordinates choose $\lambda^2=\det C$ and
$R=\lambda C^{-T}$. This argument also works in characteristic two.

Choose $M(R)=C$. The two tuples are then
$A_a=RS_aR^T$ and $B_a=-R^{-T}S_aR^{-1}$. These arise from the standard
tuple by the permitted change

$$
A_a\mapsto Q^{-1}A_aP,\qquad B_a\mapsto P^{-1}B_aQ,
\qquad P=R^T,\ Q=R^{-1}.
$$

Taking block sums of the inverse changes aligns every seed tuple at once
and preserves $D(K)$. Thus independent recombinations of the three terms
on different seed blocks do not create a new cross-block mechanism. The
argument descends to the original field because kernel dimensions were
unchanged; no square root is required in that field.

### Counting the cross-block loss

For diagonal blocks $i,j$, define
$L_{ij}(U)=\sum_a A_a^{(i)}U(B_a^{(j)})^T$. The equations on an unordered
pair of blocks, with $U=X_{ij}$ and $V=X_{ji}$, are

$$
V^T=L_{ij}(U),\qquad U^T=L_{ji}(V).
$$

Their contribution is exactly
$\dim\ker(I-\tau L_{ji}\tau L_{ij})$; the rectangular transposes have
the corresponding sizes. This is at most the full cross-block dimension,
but its deficit cannot be ignored.

- Each seed diagonal contributes 8.
- Each seed-seed pair contributes 8, rather than 9. After alignment,
  $\tau K_*=I-\Pi$ and $\Pi^2=3\Pi$, so
  $(\tau K_*)^2=I+\Pi$. The compatible cross blocks therefore form
  $\ker\Pi$, of dimension 8, in every characteristic.
- Each seed-scalar pair contributes at most 2. Its first cross map is a
  linear combination of the $S_a$, an alternating $3\times3$ matrix of
  rank at most 2. A composition can act as identity only on a space of
  dimension at most the rank of that first map.
- Each scalar diagonal and each scalar-scalar pair contributes at most 1.

Adding gives
$8m+8\binom m2+2ms+s+\binom s2$, which is (1). Subtracting $f(3m+s)$
gives (2), since the integer function $m(5-m)/2$ has maximum 3.
For equality in (1), put $A_3=B_3=1$ on each scalar block and zero there
in the other two terms. Each seed-scalar pair then has dimension 2.

### Upper-block extensions

For an upper-block family, introduce an indeterminate $t$ and scale block
$i$ by $t^i$. Using this same scaling in both factor bases replaces each
$(i,j)$ block by $t^{j-i}$ times that block. All exponents are nonnegative.
Over $F(t)$ the change preserves agreement dimension; specialization at
$t=0$ deletes the strict upper blocks. Rank cannot increase under
specialization, so the original agreement dimension is at most that of
the block-diagonal family. This proves (1) for the stated extensions too.

Both families must have the compatible upper-block form. One-sided surgery
does not ensure this: lower blocks in the other family would acquire
negative powers of $t$. Thus the degeneration does not restore the invalid
general expansion inference above. ∎

## A precise way a different seed could refute +3

Let $K_0$ act on $\operatorname{Mat}_s(F)$, put $T=\tau_sK_0$, and form
its identity lift $K_n$ in dimension $sn$. After shuffling factors, the
agreement space is isomorphic to the kernel of
$I\otimes\tau_n-T\otimes I$.

In characteristic other than two, let
$a=\dim\ker(T-I)$ and $b=\dim\ker(T+I)$. Symmetric and skew-symmetric
matrices in the second factor give

$$
D(K_n)=a\frac{n(n+1)}2+b\frac{n(n-1)}2. \tag{3}
$$

In characteristic two, let $u=\dim\ker(T-I)$ and
$v=\dim\ker((T-I)^2)$. The transpose on $\operatorname{Mat}_n$ has
$n$ size-one Jordan blocks and $n(n-1)/2$ size-two blocks at eigenvalue 1.
Solving along each block gives

$$
D(K_n)=nu+\frac{n(n-1)}2v. \tag{4}
$$

In every characteristic, if $T^2=I$, these formulas reduce to

$$
D(K_n)-f(sn)=n\bigl(D(K_0)-f(s)\bigr). \tag{5}
$$

Thus a three-term seed with $(\tau_sK_0)^2=I$ and agreement dimension
above $f(s)$ would refute +3 by producing unbounded linear excess. It
would still not refute Problem R, which permits a linear error. The known
seed fails this test: $(\tau_3K_*)^2=I+\Pi\ne I$ over every field.
No other seed satisfying the test is supplied here.

## An obstruction from the classification of three-term unitaries

Work over $\mathbb C$ in this section, with $K$ acting on
$\mathbb C^s\otimes\mathbb C^s$ and $s\ge1$. The **operator Schmidt rank** of
$K$ is the least number of Kronecker terms needed to express it. For a
minimal decomposition, the spans of its first and second factors are
intrinsic: they are the images of contraction against linear functionals
on the opposite matrix space.

**Proposition.** Suppose $K$ has operator Schmidt rank at most 3 and there
are invertible $L_1,L_2,R_1,R_2$ for which

$$
U=(L_1\otimes L_2)K(R_1\otimes R_2)
$$

is unitary. Then $D(K)\le f(s)$, without any involutivity assumption.

**Proof.** For rank at most 2, apply Paper 17's two-term theorem. For
rank 3, [Chen and Yu, Theorem 11](https://arxiv.org/html/1407.5464v2)
states that a bipartite unitary of operator Schmidt rank 3 is locally
equivalent, by product unitaries on the left and right, to a controlled
unitary. Its controlling side is therefore contained in the diagonal
matrices in suitable left and right bases. This holds for either possible
controlling side.

Consequently one factor space of $K$ has a simultaneous left/right
diagonalization. For example, if invertible $L,R$ make every $LA_aR$
diagonal, choose $Q=L^{-1},P=R$ in the transpose-compatible change

$$
A'_a=Q^{-1}A_aP,\qquad B'_a=P^{-1}B_aQ.
$$

It preserves $D(K)$ and makes the first factors diagonal. Paper 17's
flag bound now gives $D(K)\le\sum_{i=1}^s i=f(s)$. Exchange factors
if the second side is controlling. Notice that arbitrary four-factor
local equivalence need not preserve $D$: the proof transfers the
diagonalizable factor space, then uses the paired change that does. ∎

This is a consequence of an established unitary classification and the
existing flag theorem, not a new classification. Its useful consequences
for the seed search are as follows.

1. If $T=\tau_sK$ is a Hermitian involution, it is unitary, so $K$ is
   unitary and $D(K)\le f(s)$. A normal complex involution is Hermitian.
   Thus an above-pairing involutive three-term seed must be **non-normal**.
   This does not mean non-diagonalizable: every complex involution is
   diagonalizable.
2. More generally, no positive definite Hermitian matrices $H_1,H_2$
   can satisfy

   $$
   T^*(H_1\otimes H_2)T=H_1\otimes H_2
   $$

   for an above-pairing seed. Indeed, writing $H_1=P^*P,H_2=Q^*Q$ makes
   $T'=(P\otimes Q)T(P^{-1}\otimes Q^{-1})$ unitary. Then
   $\tau_sT'=(Q\otimes P)K(P^{-1}\otimes Q^{-1})$ is unitary, so the
   proposition applies. Every complex involution has some invariant
   positive definite metric, for example $I+T^*T$; the obstruction is
   specifically to a **product** metric.
3. Consider $K=\sum_{a=1}^3 c_aP_a\otimes P_a^{-1}$ with unitary $P_a$
   and real $c_a$. Each $\tau_s(P_a\otimes P_a^{-1})$ is Hermitian,
   so $T$ is Hermitian. If $T^2=I$, then

   $$
   s\sum_a c_a=\operatorname{tr}T=2D(K)-s^2\le s,
   $$

   giving $\sum_a c_a\le1$. This rules out the inverse-unitary paired
   family in every complex dimension.

The conclusions also apply to real matrices by scalar extension. They
do not extend to finite fields by replacing adjoints with transposes:
the positive-definite and complex-unitary hypotheses are essential to
the cited argument.

### The obstruction leaves a genuine non-normal region

For $s=2$, let $A=E_{01}$, $B=E_{00}$ and $g=I+A\otimes B$.
Since $A^2=AB=0$,

$$
K=g^\sigma g^{-1}=I+B\otimes A-A\otimes B,\qquad
T=\tau_2K=g\tau_2g^{-1},\qquad g^\sigma=\tau_2g\tau_2.
$$

Thus $T^2=I$ and $D(K)=3=f(2)$ over every field. Over $\mathbb C$,
$K$ is not locally equivalent to a unitary through four invertible
product factors. Its two intrinsic factor spaces are both
$\operatorname{span}\{I,A,B\}$ and have dimension 3. Neither can be
made diagonal by left/right equivalence: if $LR$ and $LAR$ were diagonal,
then $R^{-1}AR=(LR)^{-1}(LAR)$ would be diagonal, impossible for a
nonzero nilpotent $A$. Chen--Yu's theorem would require such a
diagonalization on one side. Therefore $T$ also has no invariant positive
product metric, although it has zero excess.

For comparison, four terms already give involutive positive excess over
every field. At $s=2m$, set

$$
K=\sum_{i,j=0}^1(E_{ij}\otimes I_m)\otimes(E_{ji}\otimes I_m).
$$

After shuffling, $T=I_4\otimes\tau_m$, so
$D(K)=2m(m+1)=f(2m)+m$. Its operator Schmidt rank is exactly 4.
This known partial-swap construction makes the three-versus-four-term
question sharp within the involutive target, but does not decide the
three-term case.

### Checks and characteristic restrictions

The standard-library [control script](../tools/involutive_seed_controls.py)
checks the conjugate family, the four-term partial swap, and the standard
three-dimensional seed over $\mathbb F_2,\mathbb F_3,\mathbb F_5,
\mathbb F_7,\mathbb F_{101}$. Run from the repository root:

```sh
python3 lean-backlog/tools/involutive_seed_controls.py
```

These are exact finite diagnostics, not substitutes for the proofs.
They check actual kernel dimensions and the matrix identity $T^2=I$.
Although $\operatorname{tr}T=\sum_a\operatorname{tr}(A_aB_a)$ holds
over every field, the inequality $\operatorname{tr}T\ge s+2$ is a
criterion for positive excess only when the involution's trace can be
interpreted as the characteristic-zero integer $2D-s^2$. In odd
characteristic it gives a congruence; in characteristic two the trace
does not determine the fixed-space dimension. Use $s^2-\operatorname{rank}(I-T)$
directly for finite-field searches.

## Sources and next step

The basic seed, its identity lifts, and its padding are proved in
[Paper 20](../../Ramsey-Free-Bounds-for-Two-Stage-Shared-Decoder-Composition/paper/sections/swapcodes.tex),
with the lift dimensions and the stated $d=4,5,7$ padding cases
Lean-verified there.
The independent term alignment, compatible extension argument, and assembled
screens here are written proofs. Repository sources were checked at `bc05257`,
and the involutive-search additions at `96fa441`.

The unitary classification is Lin Chen and Li Yu, *On the Schmidt-rank-three
bipartite and multipartite unitary operator*, Annals of Physics 351 (2014),
[doi:10.1016/j.aop.2014.09.026](https://doi.org/10.1016/j.aop.2014.09.026),
[arXiv:1407.5464v2](https://arxiv.org/abs/1407.5464v2), Theorem 11.
The application above is written, not Lean-verified; formalizing the cited
classification is outside this note's scope.

The next proof must control cross constraints in a genuinely different
three-term family, or handle one-sided surgery without assuming a compatible
flag on the other side. Repeating, padding, recombining, or compatibly
extending the standard seed cannot produce a counterexample. The involution
test (5) is one sharp target for a different construction, not an assertion
that every counterexample must have that form. Over complex numbers its
positive-excess examples, if any, must also escape the local-unitary class
above. No completeness claim is made for searches over small dimensions
or any chosen parameterization.

The subsequent [paired-cut and product-space note](involutive-product-spaces.md)
uses involutivity to preserve the target under block cuts, and supplies
a characteristic-free exclusion when the two factor spaces coincide and
contain the identity. It also incorporates the now-proved two-term
equality classification, closing the dimension-three seed case.
