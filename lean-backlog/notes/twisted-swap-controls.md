# Twisted swap: exact block completions and corrected baselines

Hans Brende and GPT-6 Astra, 2026-11-13.

This reviews [Fable's twisted-swap note](twisted-swap.md) at revision `d357e6f`
and records exact controls for its proposed experiments. The proofs below are
written proofs, not Lean formalizations. The finite checks use exact arithmetic;
no numerical rank tolerance is used. No literature-novelty claim is made.

The covariant reduction is correct. The two-dimensional model admits a stronger
exact formula, and the common-subspace method is stronger than the proposed
flag barrier. The suggested A5 baseline is exceeded by elementary helper-cycle
constructions, even in dimensions four and five. These constructions give only
an additive correction; they do not breach the asymptotic half-rate barrier.

## 1. Exact completion for a block hyperplane

Let F be any field, let phi be a nonzero linear functional on M_n(F), and write
phi(X) = tr(B^T X), with s = rank(B). Put W = ker(phi). For an arbitrary
dn-by-dn matrix T, viewed as d-by-d blocks T_gh of size n, form the d-by-d matrix
Q with Q_gh = phi(T_gh). Then

\[
 \min_{K\in M_d(F)\otimes W}\operatorname{rank}(T-K)
   =\left\lceil\frac{\operatorname{rank}Q}{s}\right\rceil.
\]

**Proof.** Independent invertible changes in the internal row and column bases
reduce phi to the sum of the first s diagonal coordinates. Such changes preserve
the rank being minimized and carry W to the corresponding hyperplane. If a
residual R has rank r, factor R = XY with r intermediate coordinates. Applying
phi blockwise gives Q as a sum of s products of a d-by-r matrix and an r-by-d
matrix. Thus rank(Q) <= sr.

Conversely, put r = ceil(rank(Q)/s). Split a rank factorization of Q into s
groups of at most r columns, padding with zeros, so Q = sum_i X_i Y_i with
X_i of size d-by-r and Y_i of size r-by-d. Define the global factors X and Y
by X[(g,i),:] = X_i[g,:] and Y[:,(h,i)] = Y_i[:,h] for i <= s, and zero in
the other internal coordinates. The matrix R = XY has rank at most r and
phi(R_gh) = Q_gh. Therefore K = T-R is allowed. The construction also covers
Q = 0. This proves equality. ∎

For n = 2 and W = Sym_2(F), take phi(X) = X_12-X_21. Its coefficient matrix
has rank two in every characteristic. Reorder T by the internal coordinate
and write its d-by-d blocks as T_ij. The formula becomes

\[
 \max_K\dim\ker(T-K)
  =2d-\left\lceil\frac{\operatorname{rank}(T_{12}-T_{21})}{2}\right\rceil.
\]

This strengthens Proposition 3: it does not require an involution, invertibility,
or characteristic different from two. For the twisted swap, the quotient is a
weighted permutation matrix, with weights (U_g)_12-(U_g)_21. If all weights are
nonzero and d is even, the maximum is exactly 3d/2, as in the original result.

More generally, every three-dimensional W in M_2 is such a hyperplane. If it
contains I and all phi(U_g) are nonzero, the coefficient rank s is either one
or two, and the maximum is respectively d or 3d/2. Thus the formula also
distinguishes the degenerate hyperplanes from the symmetric-block case.

## 2. The common-subspace certificate is not an optimal flag barrier

Proposition 2's compression argument is correct. If R has dimension t and
U_g R meets WR trivially for every g, restricting inputs to R and quotienting
outputs by WR kills every decoder block and leaves rank dt. Thus
dim ker(tau-K) <= d(n-t). This works for any permutation of the outer indices;
inverse pairing and fixed-point-freeness are unnecessary for this inequality.

The original generic choice t = floor(n/(w+1)) is valid, but is not a ceiling
on this method. Over C, fix any W containing I, of dimension w >= 2. Choose a
non-scalar B in W and a B-invariant subspace R of dimension t = floor(n/w).
Such invariant subspaces exist in every dimension over C. Extend I,B to a basis
of W. Since both preserve R,

\[
 \dim WR\le (w-1)t,\qquad \dim R+\dim WR\le wt\le n.
\]

For generic U, both UR and U^{-1}R meet WR trivially: each condition is a
nonempty Zariski-open condition on GL_n(C), and their intersection is nonempty.
One can see nonemptiness directly by interchanging R with a t-plane disjoint
from WR and fixing a complement. Apply this to finitely many independently
chosen inverse pairs. The same compression certificate therefore gives

\[
 D\le d\bigl(n-\lfloor n/w\rfloor\bigr).
\]

In the fixed-point-free model, for w = 2 and even n, pairing is optimal for
generic complex inverse-paired U, for each fixed W and d. The case n = 3, w = 2 remains open
here: this certificate gives 2d, while pairing gives 3d/2. A proposed ceiling
for all flag certificates would need a precisely defined class and a new proof.

The sentence about w = 1 also needs qualification: the displayed compression
bound gives d ceil(n/2), not dn/2 when n is odd. In the extreme n = w = 1,
all outer matrices are allowed and K = tau gives D = d.

## 3. A5: a common decoder above pairing and loop copying

Use G = A5, d = 60, a = (1 2)(3 4), b = (1 3 5), and Sigma = {e,a,b}.
These generators generate A5. For an irreducible representation pi of
dimension n, put A = pi(a), B = pi(b), W = span{I,A,B}. Use K = I outside
displacements {a,b,b^{-1}}. At a set K_aa = A. On the ordered pair (b,b^{-1})
set

\[
 \tau_{\rm pair}=\begin{pmatrix}0&B\\B^{-1}&0\end{pmatrix},\qquad
 K_{\rm pair}=\begin{pmatrix}0&B\\-I-B&0\end{pmatrix}.
\]

The sole nonzero residual block is I+B+B^2. In characteristic zero it has
rank dim Fix(B), since B^3 = I. The pair contributes
2n-dim Fix(B), rather than the ordinary pairing contribution n. Every scalar
coefficient is 0, 1, or -1, and the same coefficient matrices serve every pi.

The exact rational representation checks give the following attained dimensions.
The last column permits separate choices in the two sectors; it is not an
assertion about a common optimum.

| Representation dimension | K = I, including fixed points | Also copy at a | Also use the b-pair | Further local search |
|---|---:|---:|---:|---:|
| 4 | 122 | 124 | 126 | 126 |
| 5 | 160 | 162 | 166 | 172 |

The representations are the sum-zero modules of the actions on five points
and six Sylow-5 subgroups. Their characters at orders 1,2,3,5 are
(4,0,1,-1) and (5,1,-1,0). Inversion has 22 pairs and 16 fixed points.
These facts give the first column; copying a gains two in each sector, and
the b-pair gains two and four respectively.

The final six-dimensional gain in the five-dimensional sector is also local.
On six additional inverse pairs, choose a helper separately in each off-diagonal
block so that the relative group elements are involutions. Each residual then
has nullity three, so the pair contributes six instead of five. The reproduction
tool exports the six pairs, all sparse coefficient matrices, and exact ranks.
These are lower bounds, not certified maxima. On the full regular representation
the same six patches give no extra gain: an involution fixes exactly d/2
dimensions, so the two blocks together contribute d. Sector gains cannot be
summed without checking their shared coefficients and effects on other sectors.

### Direct all-field count, without Fourier decomposition

The simpler shared decoder, without those six additional patches, has

\[
 D=1900=\frac{60\cdot61}{2}+30+40
\]

over **every field**. In displacement coordinates the swap sends
(r,g) to (rg,g^{-1}). Outside {a,b,b^{-1}}, there are 60 fixed coordinates
and 1680 two-element orbits. The identity decoder has one free scalar on each,
giving 1740 dimensions. The copied a block contributes 60. On the b-pair,
I+R_b+R_b^2 is a direct sum of twenty all-ones 3-by-3 matrices, each of rank
one even in characteristics two and three. Its 120 coordinates therefore
contribute 100. The total is 1740+60+100 = 1900.

More generally, in any finite group of order d with helpers e, a nonidentity
involution a, and an element b of order three, this construction gives

\[
 D=\frac{d(d+1)}2+\frac d2+\frac{2d}3.
\]

This is a matching and a collection of helper triangles. Its gain over ordinary
pairing is only 7d/6. It refutes the literal prediction of no excess in the
four- and five-dimensional A5 sectors, even after copying the helper loop.
It does not refute a uniform sector bound dn/2+C_w d, nor yield a positive
asymptotic rate gain. Future searches must include these elementary corrections
in their baselines and distinguish local gains from interactions between orbits.

## 4. Structured controls above the generic threshold

Here is an exact small control in every characteristic. Take d = 2, n = 2,
W = Sym_2, U = [[1,1],[0,1]], and the other swap block U^{-1}. Choose

\[
 K_{00}=-E_{11},\quad K_{01}=I,\quad
 K_{10}=I-E_{12}-E_{21},\quad K_{11}=-E_{22}.
\]

Then tau-K = vv^T with v = (1,0,0,1), so its kernel has dimension three.
Tensor each internal block with I_m. This preserves w = 3, changes n to 2m,
and gives dimension 3dn/4 after repeating independent outer pairs. At n = 4
this exceeds pairing although n > 2 sqrt(w). It is a structured tensor lift,
not a counterexample for generic data.

An exact GF(2) control also has d = 2, n = 4, w = 3, with W generating all
of M_4. The verifier supplies U of order seven, independent I,A,B, and
K_00 = K_11 = 0, K_01 = I+A, K_10 = B. The two off-diagonal residuals have
ranks two and one, giving total rank three and nullity five, above pairing four.
This came from a bounded exact search; it proves no generic real-field claim.

Full generated algebra is not itself a safeguard against such examples. Given
an invertible U and low-rank E,F, the space
W = span{I,U-E,U^{-1}-F} allows residual blocks E,F. Thus low-rank interpolation
can be built into the instance. Generic-instance tests and structured controls
must be reported separately.

## 5. Remaining scope and next experiment

The coordinate and Fourier formulas in Proposition 1 check. A covariant decoder
has **up to** d different blocks per helper; special covariant decoders can still
have bounded repertoire. Also, group inversion has fixed points, so the group
case requires the extension of the abstract fixed-point-free model. Restricting
an experiment to inversion-closed subsets gives valid constructions, but is
not an upper bound on decoders that couple those subsets.

The dimension count is a heuristic for a sufficiently general affine family.
The inverse-paired family is constrained, and representation matrices have
additional relations. A generic-model theorem would not by itself prove the
representation bound. The claim about small representations forcing small
Cayley separators needs a quantitative theorem and is not used here. Numerical
singular values below a tolerance are evidence, not exact kernel certificates.

The useful uniform target remains D_pi <= d n_pi/2 + C_w d. If proved, summing
with multiplicities gives d^2/2+C_w d sum_pi n_pi. With k conjugacy classes,
sum_pi n_pi <= sqrt(kd), so k = o(d) gives the desired o(d^2) error. This
summation is valid; the uniform sector inequality is the missing step.

Next: a bounded real-field search using analytic derivatives, first recovering
known positive controls. Search away from K = I as well: in the real or complex
fixed-point-free model, the negative-eigenspace block of tau-K remains invertible
near I, forcing rank at least dn/2 in that neighborhood. With inversion fixed
points, the corresponding statement is rank >= dn-D_0, where
D_0 = dim ker(tau-I). Thus a sufficiently small neighborhood cannot improve
the identity decoder's own baseline. Store complete witnesses and coefficient norms. Compare
A5 searches to the explicit local constructions, not merely to K = I.

## Reproduction

Run from the repository root; all commands use only the Python standard library:

```sh
python3 lean-backlog/tools/twisted_quotient_controls.py
python3 lean-backlog/tools/twisted_a5_controls.py --output twisted-a5-receipt.json
python3 lean-backlog/tools/twisted_gf2_control.py
```

The first checks 324 exact symmetric-block completions over GF(2), GF(3), and
GF(5), including all possible quotient ranks at d <= 8, plus nine tensor
controls. The second checks all multiplication identities in the two A5
representations, exports sparse witnesses, and counts the actual coordinate
orbits of the common decoder. Its optional NumPy instance helper is not used
by these checks. The third verifies the GF(2) witness, a five-vector kernel
basis, and dimension sixteen of the generated algebra.
