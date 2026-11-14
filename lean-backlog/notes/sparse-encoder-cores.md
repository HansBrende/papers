# Sparse encoders: nonlinear core reduction and the majority-tower test

14 November 2026. Fable asked whether the Boolean two-source bound survives
nonlinear encoding; Astra extended the core argument to every common finite
alphabet. **Status: written proofs, not Lean-verified.** No literature novelty
claim is made. Front D1 gains a source class without a linearity assumption;
the final comparison is a bounded test of G0, not a presentability decision.

## 1. The source premise

Let Q be a finite alphabet of size q≥2 and let

  E: Q^K → Q^V

be injective, with N=|V|>0. The source is the **entire Cartesian product**:
all K symbols vary independently. Sources and coordinates have the same
alphabet. The image is a whole-row storage code. Coordinates have row and
column labels, and a target in column r is recoverable by an arbitrary
function of the retained coordinates in rows ρ(r). Write H_r for that helper
union. The coordinate set V may be a mask of the original grid.

For coordinate x let f_x be its encoder function and τ(x) its *essential
support*: u∈τ(x) precisely when two source assignments differing only at u
can give different f_x values. This is a fixed semantic dependency set,
not the number of adaptive queries used to evaluate f_x. Set

  deg(u)=#{x:u∈τ(x)},        I=Σ_x |τ(x)|=Σ_u deg(u).

A coordinate is a loop if its row belongs to ρ of its column. It is *far*
if its row and column have neither a length-one nor a length-three walk
between them in the bipartite row-helper graph. Assume first that every
nonconstant coordinate is far. Constant coordinates remain in V throughout;
their values need not be zero.

The rate of this code is exactly K/N. A large arbitrary correctness set is
not automatically supplied with such a sparse, independent-source encoder.

## 2. The permutation forced by a low source

Every source occurs somewhere by injectivity. A source occurring once would
force its sole coordinate to be a loop: without that coordinate the helpers
do not depend on the source. Thus every source has degree at least two.
Call degree-two sources *low*, and the others *high*.

Suppose low source u occurs at x and y. Both coordinates are nonloops.
Fix every other source. Recovery of x makes f_x(u) a function of f_y(u),
and recovery of y gives the converse; every other helper is independent of
u. Injectivity of E makes u↦(f_x(u),f_y(u)) injective. Consequently each
component is injective Q→Q, hence a permutation. This holds for every
assignment of the other sources. For bits the two functions have the form
u xor a and u xor b; no group operation is needed for general Q.

**Low pairs are disjoint.** Suppose a cell e contains low sources u and v,
with other occurrences p and z. Recovery of e requires both mates among
its helpers. If p=z, fix all other sources: e is a function of p, so the
full encoder has at most q outputs while u,v have q² choices. This
contradicts injectivity. Thus the mates are distinct; p does not depend on
v, and z does not depend on u.

At fixed other sources, e is a permutation in either variable separately.
Change u, and choose the unique new v keeping e unchanged. The value at p
changes because it is a permutation in u. Unless z is a helper of p,
all of p's helpers stay unchanged: their only possible dependence on u or
v is through e, and p is not its own helper. This contradicts recovery.
Also e helps p, and z helps e. Hence

  row(e) — column(p) — row(z) — column(e)

is a length-three walk, contradicting farness. No coordinate contains two
low sources, so their pairs are disjoint.

**A helper union contains at most one occurrence of each low source.** If
both x and y belonged to H_r, recovery of x would also require y∈H_col(x).
Then row(x)—r—row(y)—column(x) is a forbidden length-three walk.
These arguments use only the actual incidences and survive coordinate masks.

## 3. Exact core reduction by relative permutations

Let H be the set of high sources, n₂ the number of low sources, and V₀ the
coordinates with no low source in their support, including all constants.
For a low pair x_u,y_u and a high assignment h, denote its two permutations
of u by A_{u,h} and B_{u,h}. They depend on no other low source.

Recover x_u as follows in the proof. Prescribe y_u=t, for any symbol t,
by choosing u=B_{u,h}^{−1}(t). Set each other low-bearing helper to a
fixed symbol q₀ by choosing its own low source. These choices are independent
and simultaneously possible: no helper union contains two occurrences of
one low source, and no cell contains two lows. The full Cartesian source
premise ensures these assignments are allowed. The old decoder now expresses

  A_{u,h} B_{u,h}^{−1}(t)

as a function of t and the actual pure-high helper values. Thus the relative
permutation is determined by those values. For a pure-high target, the same
operation fixes all nuisance low-bearing helpers without changing the target.
Substituting their fixed values in its decoder gives recovery using only
coordinates in V₀.

The encoder restricted to V₀ is injective on Q^H. Indeed, if h and h′ give
the same V₀ word, each low pair has the same relative permutation under
the two assignments. Choose its low value separately on each side to make
y_u=q₀. Both x_u values then agree as well. Doing this for all disjoint
pairs makes the complete original outputs agree. Injectivity of E forces
h=h′.

We have proved a whole-row code on the inherited mask V₀, with its original
high sources and no increase in essential supports, and the exact identities

  N−|V₀|=2n₂,          K=n₂+|H|,
  K=(N−|V₀|)/2+log_q |E₀(Q^H)|.                       (1)

Recompute degrees and repeat. Injection and recovery exclude degree one
at each step; a nontrivial step removes sources and their disjoint pairs.
The process terminates at a masked code with K_* independent sources,
N_* retained coordinates and minimum source occurrence at least three:

  K=(N−N_*)/2+K_*.                                    (2)

The terminal mask need not be balanced. Initial constants remain, removed
coordinates are never counted again, and no change of source coordinates
has occurred. This proves the nonlinear version of the exact core in
[row-spread §28](row-spread-of-cones.md#28-arbitrary-coefficient-source-bounds-and-exact-core-reduction).

## 4. Paid bounds and their quantifiers

If each encoder coordinate depends on at most two sources, incidence counting
in the terminal core gives 3K_*≤2N_*. Equation (2) gives K≤2N/3 in the clean
case. For arbitrary supports, already the first core is injective, so
|V₀|≥|H|. Consequently

  N≥2n₂+|H|,         I≥2n₂+3|H|,         4K≤N+I.       (3)

To obtain a clean code, fix all sources touched by loop or distance-three
coordinates. More generally one may first fix the sources touched by
designated heavy helper rows, make those rows constant and hard-code their
values before removing them from the helper relation. If t distinct sources
are fixed, the restricted encoder is still injective on exactly Q^{K−t}.
Every recovery function survives. Recompute essential supports: restriction
can remove additional dependencies. If I′ is the new incidence count and
J=I−I′, then J≥t. The clean results yield

  K=t+(N−N_*)/2+K_*,
  K≤2N/3+t                         (support at most two),
  4K≤N+I+4t−J≤N+I+3t.                                (4)

On a balanced d×d grid with b coordinates per cell, N=d²b, suppose
|ρ(r)|≤w and every coordinate has essential support at most a≥2. For any
integer R≥1, the same geometric payment as in §28 gives

  t/N≤aw/(R+1)+aw/d+aw(w−1)(R−1)/d =: E_{a,w,d}(R).   (5)

Here is the count. At most wd/(R+1) rows have reverse degree greater than
R; the sources they touch number at most a·db times the number of these rows. After
fixing those sources and trimming those helper rows, there are at most
wdb loop coordinates and db·w(w−1)(R−1) distance-three coordinates.
The latter count follows a length-three walk from a column, through one
of at most w helper rows, another incident column, and another helper row.
Fixing all sources at these coordinates makes them constant. Constants are
retained in N, so no uncharged coordinate deletion is used.

For I/N≤μ this proves

  K/N≤2/3+E_{2,w,d}(R)                (support at most two),
  K/N≤(1+μ)/4+(3/4)E_{a,w,d}(R).                       (6)

At fixed a,w, take R=⌈√d⌉. Thus the asymptotic two-source rate is at most
2/3, and mean support below three by a fixed margin gives a common positive
deficit. These conclusions are uniform in q, b and all encoding/recovery
functions. For fixed a they also hold whenever w³=o(d), by taking
R=⌈√(d/(w−1))⌉ for w≥2; (5) is then at most
2aw√((w−1)/d)+aw/d. Use R=d for w=1.

These are bounds on **independent-source representations**. They do not
identify a native fibre with a full cube, or turn a bounded recovery view
into a sparse encoder. In particular they do not decide the unrestricted
whole-row deficit. The original linear results follow by taking Q to be
a finite field; their infinite-field versions remain separate.

## 5. The defining sources of the majority construction

The suggested test of Paper 15 needs three different objects separated.
At seed level j write U≤F_q^n, h=dim U, and choose a basis of U extended
by any complementary basis of F_q^n. For odd amplification order m and
t=(m+1)/2, the proof of
[Paper 15, Theorem M](../../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/paper/sections/amplification.tex)
exhibits the subspace C_good spanned by tensor basis vectors with at least
t factors from U. Its dimension is

  K_good=Σ_{k=t}^m binom(m,k)h^k(n−h)^{m−k}.           (7)

It lies in ker H_m; the paper does not assert equality. Its final **binary
syndrome fibres**, formed by embedding bits in an odd-characteristic field,
need not be binary linear spaces and have no supplied independent-source
generator. The following formulas are for the exhibited tensor basis only.
Write ρ_seed=810/1613 for the concrete lower bound h/n≥ρ_seed; this is
distinct from the helper-row relation ρ(r).

Let a_x count nonzero U-basis entries at seed coordinate x, and b_x the
nonzero complementary-basis entries. Put ā=(Σ_x a_x)/n and b̄=(Σ_x b_x)/n.
At tuple x=(x₁,…,x_m) the exact coordinate support is

  s_m(x)=Σ_{S⊆[m], |S|≥t} ∏_{i∈S}a_{x_i}∏_{i∉S}b_{x_i}.

Hence the exact mean and maximum are

  μ_m=Σ_{k=t}^m binom(m,k)ā^k b̄^{m−k},
  a_m=max_{x∈[n]^m} s_m(x).                            (8)

Each tensor-generator entry is a single product, so this support count has
no cancellations. For example μ₁=ā, μ₃=ā³+3ā²b̄, and
μ₅=ā⁵+5ā⁴b̄+10ā³b̄². The paper chooses no canonical extended seed basis;
these are not numerical functions of m alone. Always
μ_m≤a_m≤min(K_good,(max_x(a_x+b_x))^m) and a_m≥(max_x a_x)^m.

The concrete seed makes the test decisive in the other direction. It is
the twisted Tanner code on Paper 13's graph X_j. By that paper's
[local Reed–Solomon lemma](../../Storage-Codes-above-Half-Rate-under-Paired-Distance-Separation/paper/sections/preliminaries.tex),
a nonzero local word has at least two nonzero edges; by its
[girth lemma and Tanner identification](../../Storage-Codes-above-Half-Rate-under-Paired-Distance-Separation/paper/sections/arithmetic.tex),
girth(X_j)→∞. The support graph of a nonzero global word has minimum
degree at least two on its incident vertices, hence contains a cycle.
Thus its minimum Hamming distance δ_j satisfies δ_j≥girth(X_j)→∞.

Every U-basis vector has weight at least δ_j, so ā≥(h/n)δ_j≥ρ_seed δ_j.
The all-U term of (8) gives, for every fixed odd m,

  μ_{j,m}≥(ρ_seed δ_j)^m→∞.                            (9)

Both mean and maximum therefore escape the sparse-source hypotheses in
the construction's defining tensor basis.

## 6. Changing the encoder does not fix this displayed subspace

There is also a basis-independent argument. Let π:F_q^n→F_q^n/U be the
quotient. Every good tensor has a U-factor, so C_good⊆ker(π^{⊗m}). Suppose
a nonzero member had support of size less than δ_j. Project its support
onto the m coordinate axes, obtaining sets S_i of size less than δ_j.
The map π is injective on the coordinate span F_q^{S_i}, since its kernel
there would be a nonzero U-word of weight less than δ_j. Tensor products
of these injections are injective over a field. The proposed word lies
in their tensor-product domain, contradicting π^{⊗m} killing it. Hence

  minimum distance(C_good)≥δ_j.                        (10)

For any code of minimum distance δ, an injective encoder from Q^K has
every source in at least δ essential coordinate supports: hold all other
sources fixed and change that source. The two distinct codewords differ
in at least δ coordinates, all depending on the changed source. Thus

  I≥δK                                                  (11)

even for nonlinear encoders. Applying this to any onto independent-source
parametrization of C_good gives mean at least δ_j K_good/n^m, which tends
to infinity at fixed m because K_good/n^m≥ρ_seed^m>0. Coordinate rearrangement
does not affect this conclusion. The same distance bound applies to every
subset; an independently encoded subcode of mean at most M can have at
most Mn^m/δ_j sources.

This closes the proposed low-mean test of the **displayed majority-fixed
subspace**, even if one permits a nonlinear reparametrization. It proves
neither presentability nor nonpresentability. It gives no minimum-distance
claim for the potentially larger full kernel ker H_m, and no sparse-source
description of the binary syndrome fibres. G0 remains open for those objects.
