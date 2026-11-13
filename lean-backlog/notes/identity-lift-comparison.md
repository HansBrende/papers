# Linear comparison kernels for fixed-seed identity lifts

Hans Brende and GPT-6 Astra, 12 November 2026.

**Status:** written proofs, independently reviewed; not Lean-verified. The
finite instances below have reproducible exact-arithmetic certificates.
This note applies standard nilpotent Jordan theory to Problem S in
[item D](../D-comparison.md). It settles one family and its changes of bases
and low-rank perturbations, not arbitrary fixed-term decoders.

## The comparison bound depends on characteristic

Write $D(K)=\dim\{X:X^T=KX\}$ on $d\times d$ matrices and, for invertible
$G$, write $\kappa_G(K)=\dim\ker(K+G\otimes G^{-1})$. The tensor
convention is $(A\otimes B)X=AXB^T$.

The exact pairing comparison gives

$$
D(K)\le
\begin{cases}
d(d+1)/2+\kappa_G(K),&\operatorname{char}F\ne2,\\
d(d-1)/2+\kappa_G(K),&\operatorname{char}F=2.
\end{cases} \tag{1}
$$

**Proof.** Multiplication $X\mapsto GX$ identifies the code of
$-G\otimes G^{-1}$ with $\{Y:Y^T=-Y\}$. Its dimension is $d(d-1)/2$
in odd or zero characteristic, and $d(d+1)/2$ in characteristic two.
For two code subspaces, their intersection lies in the kernel of the
difference of their decoders, and their dimensions sum to at most the
ambient dimension plus the intersection dimension. Apply this with
$-G\otimes G^{-1}$. ∎

Item D's all-field inequality D2 remains true; its characteristic-two form
loses a further $d$ in the undoubled bound. Finite tests in characteristic
two must use the stronger baseline in (1).

## A uniform witness for every fixed seed

Let $s,n\ge1$, $d=sn$, and let $K_0$ be any linear operator on
$\operatorname{Mat}_s(F)$. Its identity lift $K_n$ is the operator which,
after grouping the two $s$-indices and the two $n$-indices, is
$K_0\otimes I_{n^2}$. In particular, a representation
$K_0=\sum_a A_a\otimes B_a$ lifts to

$$
K_n=\sum_a(A_a\otimes I_n)\otimes(B_a\otimes I_n),
$$

with the same number of terms. Put

$$
H=J_n(1),\qquad G=I_s\otimes H,\qquad
A=K_0+I_{s^2},\qquad t=\dim\ker A^{s^2}.
$$

Here $J_n(1)$ is the single Jordan block with diagonal and superdiagonal
entries one. Then, over the original field, without any extension,

$$
\boxed{\quad\kappa_G(K_n)\le tn\le s^2n=sd.\quad} \tag{2}
$$

**Proof.** The same grouping of tensor factors sends the comparison operator
to

$$
A\otimes I_{n^2}+I_{s^2}\otimes N,
\qquad N=H\otimes H^{-1}-I_{n^2}.
$$

The matrix $N$ is nilpotent because $H\otimes H^{-1}$ is upper triangular
with diagonal one. Moreover

$$
\ker N\cong\{Y:HY=YH^T\}\cong\{Z:HZ=ZH\}.
$$

For the second identification use $Z=YR$, where $R$ reverses coordinates
and $H^T=RHR$. A commuting map is determined by the image of a cyclic
vector for $H$; every image is realized by a unique polynomial of degree
less than $n$ in $H$. Consequently this centralizer has dimension $n$.
The nilpotent Jordan form of $N$, available over $F$ itself, therefore
has exactly $n$ blocks, of lengths $\ell_1,\ldots,\ell_n$.

On a block of length $\ell$, the equations for
$A\otimes I_\ell+I\otimes J_\ell(0)$ recursively determine all coordinates
from one vector, with final condition $A^\ell x=0$. Thus

$$
\kappa_G(K_n)=\sum_{j=1}^n\dim\ker A^{\ell_j}\le nt.
$$

The final inequality uses stabilization of the kernels of powers by exponent
$s^2=\dim\operatorname{Mat}_s(F)$. ∎

This construction proves the linear comparison-kernel condition for every
fixed seed and every multiplicity. The constant depends on the seed size;
allowing that size to grow does not establish Problem S.

**Changes of bases and perturbations.** If $P,Q$ are invertible and

$$
K'=(Q\otimes P)K_n(P^{-1}\otimes Q^{-1})+E,
$$

then $G'=QGP^{-1}$ is an invertible witness with

$$
\kappa_{G'}(K')\le tn+\operatorname{rank}E. \tag{3}
$$

Indeed the same invertible left and right transformations carry
$G\otimes G^{-1}$ to $G'\otimes(G')^{-1}$, preserving nullity, and
adding $E$ increases nullity by at most its rank. In particular, rank
$O(d)$ perturbations of a fixed-seed lift still have an $O(d)$ comparison
kernel, even after independent changes of bases.

## The three-term seed

Take $s=3$, $K_0=\tau_3-\Pi_3$, where $\Pi_3(X)=\operatorname{tr}(X)I_3$.
The seed is the three-term example in [Paper 17](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/order.tex),
and its lift is studied in [Paper 20](../../Ramsey-Free-Bounds-for-Two-Stage-Shared-Decoder-Composition/paper/sections/swapcodes.tex).
For the explicit witness $G=I_3\otimes J_n(1)$, (2) sharpens to

$$
\kappa_G(K_n)=
\begin{cases}
3n=d,&\operatorname{char}F\ne2,\\
8n-3(n\bmod2),&\operatorname{char}F=2.
\end{cases} \tag{4}
$$

These are values of this prescribed witness, not minima over all $G$.

**Proof.** In characteristic other than two, $A=K_0+I$ vanishes on the
three-dimensional skew-symmetric subspace and is invertible on the symmetric
subspace. For the latter assertion, $2X=\operatorname{tr}(X)I_3$ implies
$2\operatorname{tr}X=3\operatorname{tr}X$, hence $X=0$. This also covers
characteristic three. Thus every positive power of $A$ has nullity three,
and the sum in (2) is exactly $3n$.

In characteristic two, $\Pi_3$ is a rank-one idempotent. On its image $A$
acts as identity. On its kernel $A=\tau_3+I$ is square-zero with rank three,
so its nilpotent blocks have lengths $2,2,2,1,1$. Interchanging the two
factors in the same block calculation gives
$\kappa_G=3\dim\ker N^2+2n$. In this characteristic,
$N^2=H^2\otimes H^{-2}-I$, whose kernel is isomorphic, via the same
coordinate reversal, to the centralizer of $H^2$.
Writing $H=I+J$, we have $H^2=I+J^2$. The two parity chains of $J^2$
have lengths $a=\lceil n/2\rceil,b=\lfloor n/2\rfloor$, omitting a
zero-length chain. Intertwiners between blocks of lengths $u,v$ form a
space of dimension $\min(u,v)$, so

$$
\dim\ker N^2=a+b+2\min(a,b)=2n-(n\bmod2).
$$

Substitution proves (4). ∎

The agreement dimension of the lift is $D(K_n)=4n(n+1)$ in every field.
One direct proof writes $X$ as nine $n\times n$ blocks. Off-diagonal
blocks must be symmetric. With $T=\sum_iX_{ii}$, the diagonal equations
are $X_{ii}^T=X_{ii}-T$. Transposing one gives $T^T=-T$, while summing
gives $T^T=-2T$. Hence $T=0$, and there are eight free symmetric blocks.
Equation (1) therefore gives the universal lower bounds

$$
\kappa_G(K_n)\ge
\begin{cases}
\max(0,n(5-n)/2),&\operatorname{char}F\ne2,\\
\max(0,n(11-n)/2),&\operatorname{char}F=2.
\end{cases} \tag{5}
$$

## Exact finite minima and reproduction

A bounded search found invertible matrices attaining (5) in every tested
case. The saved matrices and exact ranks, combined with (5), certify the
finite minima in this table; a failure to attain the bound would only have
given a search upper bound.

| Field | Dimension $d$ | $D(K_n)$ | Minimum comparison kernel | Prescribed Jordan-twist kernel |
|---|---:|---:|---:|---:|
| GF(2) | 3 | 8 | 5 | 5 |
| GF(2) | 6 | 24 | 9 | 16 |
| GF(2) | 9 | 48 | 12 | 21 |
| GF(3) | 3 | 8 | 2 | 3 |
| GF(3) | 6 | 24 | 3 | 6 |
| GF(3) | 9 | 48 | 3 | 9 |
| GF(101) | 3 | 8 | 2 | 3 |
| GF(101) | 6 | 24 | 3 | 6 |
| GF(101) | 9 | 48 | 3 | 9 |

From the repository root, with the Python standard library:

```sh
python3 lean-backlog/tools/pairing_comparison.py --repo . --verify lean-backlog/certificates/identity-lift-comparison.json
python3 lean-backlog/tools/pairing_comparison.py --repo . --output lean-backlog/certificates/identity-lift-comparison.json
```

The script imports Paper 17's `three_term_example.py`, using its tensor
convention and modular rank routine. Each case has a deterministic seed and
a budget of 64 matrix draws, skipping singular matrices and stopping when (5)
is attained. The saved certificates include explicit $G$, not only rank summaries.

## Consequence for the next attack

The identity-lift experiment cannot produce a quadratic obstruction to
Problem S: (2) settles it uniformly, even without extending the field.
These lifts were already easy for Problem R through their bounded factor
algebras. Their code rate tends to $4/9$, and for $n>1$ the factor tuples
preserve $F^3\otimes L$ for every subspace $L\le F^n$; they are not the
strictly expanding cores in the [companion note](finite-field-expansion.md).

The remaining question is whether a linear comparison kernel exists for
arbitrary fixed-length tuples with growing, genuinely coupled expansion
cores. The present theorem supplies a screen for fixed-seed lifts, their
changes of bases and low-rank perturbations. It gives no answer for that
remaining class or for arbitrary tape transposers.

Two corrections to the informal discussion of item D are also worth keeping
explicit. The general order estimate includes $+d/2$, giving
$D\le(1-1/(2M))d^2+d/2$ for positive $M$; without it the identity decoder
at $M=1$ is a counterexample. And Paper 17's padded three-term example
already attains dimension 11 at $d=4$ over GF(2) and GF(3). Thus 10 is not
a candidate maximum there; no upper bound of 11 is asserted here.

The repository sources above were checked at revision `b5d6db2`. The new
comparison applications and the characteristic-two sharpening have written
proofs here. No new Lean verification or literature-novelty claim is made.
