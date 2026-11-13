# Scalar blocks in the unpaired model

Hans Brende and GPT-6 Astra, 2026-11-13.

This continues Sections 7–8 of [the twisted-swap note](twisted-swap.md)
at revision `58e05f9`. The results below have written proofs and independent
reviews, but are not Lean-formalized. Numerical observations are separated from
theorems. No claim of literature novelty is made.

The main result settles the generic scalar-block problem at two and three
sites, and in a larger range of internal dimensions. The proof controls all
decoder coefficients, including unbounded ones. It does not prove the whole
unpaired conjecture or apply automatically to representation matrices.

## 1. A partial solution of the unpaired w = 1 problem

Let F be algebraically closed, d,n positive integers, and

\[
 M(U,\kappa)=\operatorname{diag}(U_1,\ldots,U_d)-\kappa\otimes I_n,
 \qquad U_g\in M_n(F),\quad\kappa\in M_d(F).
\]

**Theorem.** If n <= 2, or n >= (d-1)(d-2)-1, there is a nonempty
Zariski-open set of tuples U such that

\[
 \max_\kappa\dim\ker M(U,\kappa)=d.
\]

The open set is independent of kappa and may be restricted to invertible U_g.
In the range n >= (d-1)(d-2)-1, the same tuples satisfy the stronger
bound d-h for every kappa with h non-singleton strongly connected components
in its directed off-diagonal support graph. This refinement is not inferred
from the separate n <= 2 argument when it lies outside that range.

Thus every n is covered when d <= 3, and the first remaining cases are
d = 4, n = 3,4. The theorem is geometric in every characteristic. Over a
subfield the upper bound remains valid for tuples in this open set, but
attainment can fail if the needed eigenvalues are absent. A geometric open
set need not contain points over a given finite field.

### 1.1 A deficient-support incidence

Fix q sites and a t-plane R, 1 <= t < q. Choose q nonzero projective vectors
[v_g] in R spanning R, and require U_g v_g in R. The choices have dimension
t(n-t)+q(t-1); each of the q independent matrix constraints has codimension
n-t. Hence the locus of these data has dimension at most d n^2-delta, where

\[
 \delta=(q-t)n-2qt+t^2+q
        =a n-q(q-1)+a^2,\qquad a=q-t.
\]

If n >= q(q-1), then delta > 0. Projection to the U-tuples has a proper
Zariski closure. Excluding the finitely many choices of support and t shows
that, for n >= (d-1)(d-2), generic U admit no such configuration on fewer
than d sites. This is a dimension bound for the full incidence, not an
inference from one good specialization.

Now suppose kappa is strongly connected and a nonzero kernel vector x has
proper support S. There is an edge from S to its complement. The corresponding
zero-coordinate equation gives a nontrivial scalar relation among the x_g,
g in S. Their span R therefore has dimension t < |S|, while the other
equations give U_g x_g in R. This is precisely the excluded configuration.
Consequently every coordinate projection of the kernel is injective.

### 1.2 Full-projection incidence and the support graph

On r sites, let C be a D-plane with all block projections p_g:C -> F^n
injective. For fixed C and kappa, the equations

\[
 U_g p_g=\sum_h\kappa_{gh}p_h
\]

prescribe U_g on a D-dimensional subspace and leave n(n-D) free parameters.
The incidence dimension is therefore

\[
 D(rn-D)+r^2+rn(n-D)=rn^2+r^2-D^2.
\]

For strongly connected kappa, diagonal conjugation by L acts as
kappa -> L kappa L^{-1}, C -> (L tensor I)C, and fixes U. The stabilizer
on kappa consists exactly of scalar diagonal matrices. Each fiber over U
therefore contains an orbit of dimension r-1. The image dimension is at most
rn^2+r^2-D^2-r+1. At D = r and r >= 2 this is smaller than rn^2.
Thus generic U admit no such injective r-plane. If r > n, its existence
is already impossible by injectivity.

Combine this with Section 1.1 for every subset of sites: every nontrivial
strongly connected component of size r has nullity at most r-1. Singletons
have nullity at most one after imposing simple spectrum. Reorder arbitrary
kappa by its strongly connected components. The residual is block triangular,
and its nullity is at most the sum of its diagonal-block nullities: for two
blocks, projection of the kernel to the second block has kernel ker(A) and
image contained in ker(C). Induction gives the bound d-h.

Only finitely many exceptional closed sets are excluded, so their complement
is nonempty. The incidence projection includes every affine kappa; no bound
on its entries or compactness assumption is used.

### 1.3 The additional endpoint

Let d >= 4, m = d-1, and n = m(m-1)-1. In Section 1.1 every deficient-support
incidence still has positive codimension except q = m, t = m-1, where its
dimension equals that of the matrix parameter space. After excluding a proper
closed subset, the fibers of this last incidence are finite or empty. This
follows from the generic fiber-dimension theorem; finite-type zero-dimensional
fibers have finitely many points. No properness assertion is needed.

The q projective vectors in a surviving configuration may also be assumed to
form a minimal circuit: every q-1 are independent. Failure of that condition
is a proper closed sublocus of the configuration space, while the matrix
constraints retain the same codimension, so its incidence has smaller
dimension and can be excluded.

Fix a strongly connected kappa and a coordinate i. A nonzero kernel vector
with x_i = 0 must have all other m coordinates nonzero. Their projective
directions are in the finite list above. For one such list choose v_j; its
unique relation sum r_j v_j = 0 has every r_j nonzero. The i-th equation,
sum kappa_ij lambda_j v_j = 0, either has no solution with all lambda_j
nonzero, or forces lambda_j = c r_j/kappa_ij for a common nonzero c.
Strong connectivity supplies a nonzero coefficient, and the minimal relation
then forces all these kappa_ij to be nonzero. Thus each
configuration gives at most one projective kernel vector. The kernel of
each coordinate projection consequently has dimension at most one.

If the full kernel had dimension at least d+1, a d-plane inside it could
avoid these finitely many lines. Its coordinate projections would all be
injective, contradicting Section 1.2. Hence the full nullity is at most d.
Proper strongly connected components satisfy the stronger previous range,
so block triangular decomposition handles all kappa at this endpoint too.

The strict connected bound also extends to the endpoint. Suppose a strongly
connected kernel has dimension d. Its coordinate projections have ranks d or
d-1; let k of them be deficient. Their kernel lines are distinct, since a
vector with two zero coordinates has already been excluded. If k = 0,
Section 1.2 applies. Otherwise parameterize the d maps from a common
d-dimensional code space, modulo change of its basis. Their rank stratum
has dimension d(dn-d)-k(n-d+1). In each deficient row, the return vectors
form a minimal circuit, leaving two choices of scalar coefficients: the
diagonal entry and the multiple of the unique relation. Thus kappa has at
most d^2-k(d-2) parameters. Extending the U_g contributes dn(n-d)+kn.
These counts sum to dn^2+k before charging for a return dependence.

Fix one deficient row and all the deficient kernel lines. Evaluation of
each other projection on that row's kernel line is an independent nonzero
n-vector: the kernel lines are distinct. Requiring their n-by-(d-1) matrix
to have rank d-2 costs n-d+2 dimensions. This condition was not included
in the projection-rank count. Charging only this one dependence and then
the free (d-1)-dimensional diagonal-conjugation orbit bounds the image
dimension by dn^2+k-n-1. At the endpoint d >= 4, n >= d and k <= d,
so this is strictly below dn^2. This excludes dimension d in the connected
case and proves the d-h refinement at the endpoint as well.

The fiber-dimension fact used here is standard; see
[Stacks Project, Section 37.30](https://stacks.math.columbia.edu/tag/05F6).

### 1.4 Small n and attainment

For n = 1 the assertion is immediate. For n = 2, require the (1,2) entry
of every U_g to be nonzero. Reordering internal coordinates displays an
invertible off-diagonal d-by-d submatrix in every residual, independently
of kappa. Its rank is at least d, hence its nullity at most d. This proves
the generic upper bound for all d in this case.

Over F, choose an eigenvalue lambda_g of each U_g and take kappa diagonal
with these entries. For simple spectra the resulting kernel has dimension
exactly d. This proves attainment in all the stated ranges. Over R, even
d = 1, n = 2 can have maximum zero if U_1 has no real eigenvalue.

## 2. Review and strengthening of the commuting-space theorem

Theorem 4 of the twisted-swap note is correct. Its odd-dimensional test is
generic even with inverse pairing. For two distinct cuts, choose one index
in each set difference and the shared distinguished coordinate, put a
generic invertible 3-by-3 block there, and pair the remaining coordinates
across both cuts with 2-by-2 swaps. The relevant cut ranks and nonzero
coordinates hold on a nonempty open set. For the 3-by-3 core, the cyclic
defect satisfies

\[
 \delta(U^{-1})=-\delta(U)/(\det U)^2,
\]

as follows by substituting cofactors. This also verifies compatibility with
inverse pairing. Even dimension uses an invertible half-size cut. These
observations supply a proof of genericity, beyond the original random checks.

**Quantitative extension.** Retain Theorem 4(b)'s cut-rank and nonzero-coordinate
hypotheses, but allow its difference gamma_g to vanish at z sites. Then

\[
 D\le dn/2+z/2.
\]

Indeed the two coordinate subspaces V,V' in its proof intersect in a space
of dimension at most z, because their intersection lies in ker(diag gamma).
Thus 2(D-kd) <= dim V+dim V' <= d+z. This proof works over every field.

Zero cyclic defect alone does not imply a kernel of dimension 2d. Even for
the full diagonal block space, take every unpaired target equal to
U = [[1,0,1],[0,1,1],[1,1,3]]. It is invertible and has zero defect, but
every residual contains the invertible submatrix [[0,I],[I,*]], so has rank
at least 2d. Zeroing its internal diagonal attains rank 2d. The maximum
kernel is d. The original statement that 2d *can* occur is an existence
warning, not a sufficiency criterion for zero defect.

## 3. Splitting with inversion fixed points

Proposition 5 is correct for the fixed-point-free model and is instance
dependent. For group inversion, let i be the number of fixed points, including
the identity. Reveal all fixed positions and one point of each nontrivial pair.
Dropping the other equations gives the safe bound

\[
 D_\pi\le n_\pi(d+i)/2+
 D_{\rm unp}\bigl((\pi(h^{-1}))_{h\in G_-};W_\pi\bigr),
 \qquad |G_-|=(d-i)/2.
\]

This includes the fixed-point cost omitted by a literal reuse of dn/2.
It is nevertheless asymptotically harmless when the number k of conjugacy
classes is o(d). An elementary count gives i^2 <= dk: classify ordered pairs
of involutions (a,b) by g = ab. Then a conjugates g to g^{-1}, so for each
g there are at most |C_G(g)| possibilities for a. Sum over g and use
sum_g |C_G(g)| = dk.

If an unpaired bound c_w |G_-| is established for these **actual representation
tuples**, summing with irreducible multiplicities in characteristic zero gives

\[
 D_{\rm total}\le d^2/2+di/2+
     c_w(d-i)\sum_\pi n_\pi/2
 \le d^2/2+\frac{1+c_w}{2}d\sqrt{dk}.
\]

Here sum_pi n_pi <= sqrt(dk). Thus this conditional route still reaches
half rate when k = o(d). Independent generic U_g do not establish its
structured premise. A5 alone, with only finitely many representation
dimensions, cannot establish uniformity as dimensions grow.

## 4. What the calibrated search establishes

The new [rank-completion tool](../tools/twisted_rank_search.py) minimizes a
Schur-complement residual with analytic derivatives. It checks derivatives
against finite differences, uses bounded coefficients, starts away from
pairing, and exports the instance and decoder. It recovered the exact
two-dimensional positive control and the previous paired n=3,w=3,d=8
numerical nullity 13 before the new tests.

For independent real Gaussian targets and a Frobenius-orthonormal basis of
a space W with I in W, seed 20261113, the following candidates were found:

| n | w | d | Numerical nullity | Maximum coefficient |
|---|---:|---:|---:|---:|
| 3 | 2 | 8 | 10 | 3.51 |
| 3 | 3 | 8 | 13 | 5.62 |
| 4 | 3 | 8 | 13 | 3.92 |
| 5 | 3 | 8 | 13 | 4.46 |
| 4 | 3 | 12 | 20 | 5.69 |

These are floating-point observations with complete saved witnesses, not
exact algebraic certificates or maxima. Rank tolerance is 1e-9 times the
larger of one and the matrix spectral norm. Reproduction and independent
Kronecker/SVD checks are described below.

No target-5 candidate was found in the d=4,w=1 tests at n=3,4,5,6. Several
w=2 target-11 searches reached the coefficient cap without convergence;
limited larger-cap and complex checks did not resolve them. These failures
yield no upper bound. The successful w=3 tests reproduce the earlier counts;
they do not prove the square-root heuristic.

In fact floor(d sqrt(w)) is not a universal exact value: generic n=2,w=2
has maximum d over C, and generic n=2,w=3 has maximum floor(3d/2) by the
[hyperplane theorem](twisted-swap-controls.md). For the former, diagonalize W;
an invertible fixed off-diagonal block gives the rank-d lower bound, and
rank-one completions at the individual sites attain it. Real and complex attainment
also differ. This distinction is standard in matrix-completion geometry;
see [Bernstein, Blekherman and Sinn, *Typical and Generic Ranks in Matrix
Completion*](https://arxiv.org/abs/1802.09513). These examples do not contradict
the proposed sqrt(w) upper bound.

## 5. What remains useful for the main problem

This is a partial proof of the unpaired scalar-block target and a method
for dealing with unbounded decoder coefficients. It does not improve the
paired commuting-space conclusion already supplied by Theorem 4. Its value
is identifying which kernel configurations a more general proof must control.

For d=4,n=3,4, eliminating every vector with a zero coordinate is too strong.
The next precise task is to control how several such vectors coexist in a
putative five-dimensional kernel, using the ranks and intersections of its
coordinate projections. A single projection defect is not a counterexample.

The generic proof also does not transfer to U_g=pi(g). In a full group
instance n_pi^2 <= d, whereas the sufficient large-n range grows as d^2.
A useful bridge still needs a uniform small-n argument or explicit group
structure. No new region of the transposer frontier is ruled out here.

## Reproduction

The real experiments used NumPy 2.0.2 and SciPy 1.13.1. From the repository
root, with NumPy and SciPy installed:

```sh
python3 lean-backlog/tools/twisted_rank_search.py 2 3 2 3 --mode control --output control
python3 lean-backlog/tools/twisted_rank_search.py 3 3 8 13 --mode paired --output paired-control
python3 lean-backlog/tools/twisted_rank_search.py 3 3 8 13 --output unpaired-control
python3 lean-backlog/tools/twisted_rank_search.py --verify lean-backlog/tools/twisted-unpaired-witnesses/n3-w3-d8.npz
```

Use `--verify` on the other bundled witnesses as well. It reconstructs the
decoder by explicit Kronecker products and recomputes singular values; it does
not rely on the optimizer's Schur residual. Coefficient caps depend on the
displayed basis of W and are experimental constraints, not theorem hypotheses.
