# The twisted swap: covariant whole-row decoders on Cayley relations, and a small model of the wall

Status (2026-11-13, Hans Brende and Claude Fable 5.2): Propositions 1 to 3 have short written proofs, reviewed
by GPT-6 Astra ([twisted-swap-controls.md](twisted-swap-controls.md); its corrections are
in Section 6). Theorem 4 and Proposition 5 were reviewed in
[the unpaired scalar note](unpaired-scalar-decoding.md); Propositions 6–8 are reviewed and qualified in
[the closed-word note](covariant-word-baselines.md). Sections 4 and 8 contain numerics: real field, searches by
a local optimizer, so a value "found" is a verified kernel dimension at tolerance 1e-8 and a value "not found"
proves nothing. The new [D1/D8 Lean file](../StatementsWholeRow.lean) states the open targets and checks
their basic conventions; it does not formalize this note's substantive results.

## 1. Covariant decoders on a Cayley relation

Let G be a finite group, d = |G|, and Σ ⊆ G a set of w elements. Index rows and columns by G and let the row
relation be ρ(r) = rΣ. A linear operator with this row relation is

  (KX)[r][c] = Σ_{s ∈ Σ} Σ_{c′} M_{r,s}[c, c′] · X[rs][c′],

with arbitrary blocks M_{r,s}. Call K *covariant* if it commutes with the simultaneous left translation of rows and
columns, X[c][r] ↦ X[h⁻¹c][h⁻¹r]. This says M_{r,s}[c, c′] = M_s[r⁻¹c, r⁻¹c′] for w matrices M_s. A covariant
decoder uses d different blocks for each generator, so it is outside every bounded-repertoire theorem, and its
row relation expands when the Cayley graph does.

Write X̃[r][g] = X[r][rg] (base point r, displacement g).

**Proposition 1.** In these coordinates

  (swap X)~[r][g] = X̃[rg][g⁻¹],  (KX)~[r][g] = Σ_s Σ_h κ_s[g, h] · X̃[rs][h],  κ_s[g, h] = M_s[g, sh],

and the κ_s are arbitrary d × d matrices. Both operators commute with the left translations of the base point.
If |G| is invertible in F and F is a splitting field, then

  dim ker(swap − K) = Σ_π n_π · dim ker( τ_π − Σ_s κ_s ⊗ π(s) ),

where π runs over the irreducible representations, n_π = dim π, and τ_π acts on F^G ⊗ F^{n_π} by
(τ_π v)(g) = π(g) v(g⁻¹).

*Proof.* (Xᵀ)[r][rg] = X[rg][r] = X̃[rg][g⁻¹]. For K substitute c′ = rsh. As functions of the base point the two
operators are built from right translations f(r) ↦ f(rg), which form the right regular representation; it is the
sum of the π with multiplicity n_π, and the same matrices κ_s occur in every summand. ∎

- The same κ_s serve all π. Dropping that coupling gives an upper bound: the sum of the separate maxima.
- With e ∈ Σ and κ_e = 1 the kernel in the summand π is {v : v(g) = π(g) v(g⁻¹)}, of dimension n(d − i)/2 +
  Σ_{g² = e} dim ker(π(g) − 1), i the number of g with g² = e. This is the symmetric matrices.
- This is not the slice of shared decoders with row factors in a group algebra: there the operator is
  Σ_s (translation by s) ⊗ B_s against the plain swap; here it has the same shape against the twisted swap τ̃,
  which lies in M_d ⊗ F[G].

## 2. The model

Forget the group. Let d be even, ι a fixed-point-free involution of [d], U_g ∈ GL_n(F) with U_{ιg} = U_g⁻¹, and
W ⊆ M_n(F) a subspace of dimension w that contains 1. On F^d ⊗ F^n put (τ v)(g) = U_g v(ιg), and let K range over
M_d ⊗ W: the block (g, h) of K is an arbitrary element of W. The question is the largest D = dim ker(τ − K).
K = 1 gives D = dn/2 (pairing). Section 1 is the case ι(g) = g⁻¹, U_g = π(g), W = span π(Σ).

**Proposition 2 (flags give w/(w+1), not one half).** Over any field, if R ⊆ F^n has dimension t and
U_g R ∩ W R = 0 for every g, then D ≤ d(n − t). For data in general position over an infinite field such an R
exists with t = ⌊n/(w+1)⌋. The relation U_{ιg} = U_g⁻¹ is not used.

*Proof.* Restrict the inputs to F^d ⊗ R and compose the outputs with the functionals that vanish on W R. Every
block of K disappears, and what is left of τ − K is the block-monomial matrix with blocks y U_g x (y ⊥ WR, x ∈ R),
each of rank t because U_g R meets W R trivially. So rank(τ − K) ≥ dt. ∎

A flag in place of the single subspace R does not help: the pieces that a given g contributes along a flag
R_1 ⊂ R_2 ⊂ … must still satisfy U_g J_g ∩ W R_k = 0 at the last step, so they have total dimension at most
n/(w+1). (Sketch; this is the model's version of the order method stopping above one half on expanding
relations.) For w = 1 the bound is dn/2.

**Proposition 3 (rate 3/4 at n = 2, w = 3).** Let the characteristic be different from 2, n = 2, W the symmetric
2 × 2 matrices, and suppose every U_g has a non-zero antisymmetric part z_g J. Then the largest kernel is exactly
3d/2.

*Proof.* Write τ − K in 2 × 2 blocks of size d as [[A, B + P], [B − P, C]] with P = Σ_g z_g E_{g, ιg} and A, B, C
free. The difference of the off-diagonal blocks is 2P, of rank d, so the rank is at least d/2. Conversely split
the columns of P into two halves, P = P_1 + P_2, put B = P_1 − P_2, and take A, C so that
[[A, 2P_1], [−2P_2, C]] = [X; Y]·[Z, V] with X = 2P[:, first half], V = [1 0], Y = −2P[:, second half], Z = [0 1]. The
rank is d/2. (The antisymmetric part of U_g⁻¹ is −z_g/det U_g, so the hypothesis is consistent with
U_{ιg} = U_g⁻¹.) ∎

## 3. A count

The matrices of rank at most dn − D have codimension D², and the family τ − M_d ⊗ W has dimension w d². A family in
general position meets them only if D ≤ d√w. Pairing is a solution outside general position (it exists because
U_{ιg} = U_g⁻¹), with D = dn/2. So the guess is

  largest D ≈ max(dn/2, about d√w):  pairing is beaten exactly when n < 2√w.

Proposition 3 is the case n = 2 < 2√3, and partial transposes are the same phenomenon (a tensor factor small
enough to be served completely).

## 4. Numerical ([twisted_lm.py](../tools/twisted_lm.py), seed 20261113; random real U_g and W)

| n | w | d | pairing dn/2 | largest found | next value | d√w |
|---|---|---|---|---|---|---|
| 2 | 3 | 6 | 6 | 9 (= 3d/2, Proposition 3) | 10 not found | 10.4 |
| 3 | 3 | 6 | 9 | 9 | 10 not found | 10.4 |
| 3 | 3 | 8 | 12 | 13 | 14 not found | 13.9 |
| 3 | 3 | 10 | 15 | 16 | 17 not found | 17.3 |
| 3 | 3 | 12 | 18 | 20 | 21 not found | 20.8 |
| 3 | 2 | 8 | 12 | 12 | 13 not found | 11.3 |
| 4 | 3 | 6 | 12 | 12 | 13 not found | 10.4 |
| 4 | 3 | 8 | 16 | 16 | 17 not found | 13.9 |
| 5 | 3 | 6 | 15 | 15 | 16 not found | 10.4 |
| 3 | 3, diagonal W | 8, 10, 12 | 12, 15, 18 | 12, 15, 18 | 13, 16, 19 not found | (Theorem 4) |
| 5 | 3, diagonal W | 6 | 15 | 15 | 16 not found | (Theorem 4) |

All solutions found have coefficients of size at most 6 (log: [twisted_lm_2026-11-13.txt](../tools/twisted_lm_2026-11-13.txt)). The first optimizer ([twisted_lift.py](../tools/twisted_lift.py), alternating
projections) is too weak and is kept only for its instance generator. At n = 3, w = 3 the excess over pairing
grows with d (0, 1, 1, 2 at d = 6, 8, 10, 12) and follows the count; at n ≥ 4 > 2√3 and at (n, w) = (3, 2) nothing above
pairing was found.

## 5. What this says about the wall

- **A miniature.** For n > 2√w the model has all three features of the wall: the flag method stops at w/(w+1); a
  trace argument needs bounded coefficients; the largest code found is pairing. Each instance is a matrix of size
  dn with w d² unknowns, and n, not d, is the parameter that separates the regimes, so small instances are
  meaningful.
- **Where gains can live.** In the covariant slice a gain over pairing can come only from representations of
  dimension below 2√w (if the count is right). On a quasirandom group there are none, which fits the conjecture
  that expanding relations stay at one half; on groups with many small representations the Cayley graph has small
  separators and the order method already applies.
- **Target (generic).** For data in general position and n > 2√w, the largest kernel is dn/2. The first case is
  (n, w) = (3, 2): after diagonalising W = span{1, W_2}, K is block diagonal with three blocks on a line of M_d, and
  the claim is rank ≥ 3d/2. Upper semicontinuity is not available (κ can go to infinity), so one instance does not
  prove the generic statement.
- **Target (representations).** For U_g = π(g), W = span π(Σ): D ≤ dn/2 + C_w d. Summed over π this gives
  d²/2 + C_w d Σ_π n_π = d²/2 + o(d²) for the covariant slice whenever G has o(d) conjugacy classes, with or
  without the coupling of the κ_s.
- **Not shown.** That the model's answer for generic U_g transfers to the matrices π(g), which satisfy
  π(g)π(h) = π(gh); that non-covariant decoders behave like covariant ones; anything over finite fields (the
  searches are real).

## 6. Corrections after review (GPT-6 Astra, message C13)

- **The flag ceiling of Section 2 is wrong.** The inequality of Proposition 2 is correct, but ⌊n/(w+1)⌋ is the
  dimension of R only for R in general position. Over an algebraically closed field take R an invariant t-plane of
  one non-scalar B ∈ W: then dim WR ≤ (w − 1)t and t = ⌊n/w⌋ is admissible. For w = 2 and even n this already gives
  dn/2. The sentence "a flag does not help" was about general R and is withdrawn.
- **Proposition 3 is one case of a general statement** (Astra): for W the kernel of one functional
  φ(X) = tr(BᵀX) with rank B = s, the least rank of T − K over K ∈ M_d ⊗ W is ⌈rank Q / s⌉, Q[g, h] = φ(T[g, h]).
- **Baselines on a group.** In the covariant slice, "pairing and loops" is not the baseline: short relations among
  the generators give local gains of order d in every representation (Astra's exact values on A₅). A sector
  excess means something only above those.
- **Section 1.** Covariant blocks are up to d distinct; inversion has fixed points; the generic conjecture does not
  imply the bound for representations.
- **Structured data beat pairing at n = 4** (Astra): the n = 2, w = 3 example tensored with 1₂. So the conjecture is
  about data in general position, or about irreducible representations, never about all U_g.

## 7. Commuting W: pairing is optimal, by an argument that is not a flag

Work with M′ = (τ − K)(P ⊗ 1), P the permutation matrix of ι: then M′ = ⊕_g U_g − K′ with K′ ∈ M_d ⊗ W arbitrary. So
the problem is the least rank of a block-diagonal target minus an element of M_d ⊗ W, and the involution enters
only through U_{ιg} = U_g⁻¹. In this section the U_g are arbitrary (no pairs are assumed).

Let W lie in the diagonal matrices (after a change of basis, possibly over an extension field: this covers every
W = span{1, B} with B diagonalisable, hence w = 2 in general position, and every commuting diagonalisable W). Then
K′ = diag(N_1, …, N_n) in the n-index, N_i ∈ M_d, and x = (x_1, …, x_n) ∈ (F^d)^n lies in the kernel C iff
(U_g x(g))_i = (N_i x_i)(g) for all i, g. For S ⊆ [n] put C^S = {x ∈ C : x_i = 0 for i ∈ S}; dim C^S ≥ D − |S| d, and
x ∈ C^S forces (U_g x(g))_i = 0 for i ∈ S.

**Theorem 4.** Let W consist of diagonal matrices and let U_1, …, U_d ∈ M_n(F) be arbitrary, F any field.
(a) If |S| = k and every U_g[S, S^c] (rows S, columns S^c) has rank n − k, then D ≤ kd. With k = ⌈n/2⌉ this is
    D ≤ d⌈n/2⌉.
(b) Let n = 2k + 1, i ∈ [n], and S ≠ S′ two k-subsets of [n] ∖ {i}. Suppose that for every g the matrices
    U_g[S, S^c], U_g[S′, S′^c] have rank k, with kernel vectors v_g, v′_g (extended by zero) whose i-th entries are not
    zero, and that
      γ_g = (U_g v_g)_i / (v_g)_i − (U_g v′_g)_i / (v′_g)_i ≠ 0.
    Then D ≤ kd + d/2 = dn/2.
For n = 3, i = 1, S = {2}, S′ = {3}: γ_g = δ_g / (U_23 U_32) with δ_g = U_12 U_23 U_31 − U_13 U_32 U_21 the cyclic defect of
U_g. When δ_g = 0 for all g the kernel can have dimension 2d (rank d), so the hypothesis is needed.

*Proof.* (a) For x ∈ C^S the vector x(g) is supported on S^c and U_g[S, S^c] x(g) = 0, so x = 0; hence D ≤ kd.
(b) For x ∈ C^S we get x(g) = t_g v_g with a scalar t_g; let T ⊆ F^d be the space of these t, so dim T = dim C^S
≥ D − kd. The i-th coordinates are x_i = A t and (U x)_i = A′ t with the diagonal matrices A = diag((v_g)_i),
A′ = diag((U_g v_g)_i), and the equation for the index i reads N_i A t = A′ t. So N_i acts on V = A T as the diagonal
matrix Γ = A′A⁻¹. In the same way N_i acts on V′ = B T′ (from S′, with B = diag((v′_g)_i) and T′ ≅ C^{S′}) as a diagonal matrix Γ′. On V ∩ V′ the two agree, and Γ − Γ′ =
diag(γ_g) is invertible, so V ∩ V′ = 0 and 2(D − kd) ≤ dim V + dim V′ ≤ d. ∎

- Part (a) is a flag bound (the coordinate subspace is invariant under W). Part (b) is not: it uses that one
  operator N_i serves two different subcodes. In the language of tensors t = Σ_k x_k ⊗ r_k in C ⊗ (F^n)^*: the code
  condition is that every t whose contractions with W vanish at every site has vanishing contraction with U_g
  at every site. Flags use tensors of rank one, (b) uses rank two, and the definition allows every rank.
- With inverse pairs and 1 ∈ W the bound is attained. Checked numerically: for diagonal W of dimension 3 the
  searches find exactly pairing at n = 3, d = 8, 10, 12 and n = 5, d = 6, where W in general position gives 13, 16, 20
  at n = 3 (`twisted_lm.py … toral`; γ ≠ 0 on random matrices for n = 3, 5, 7, 9 by [toral_gamma.py](../tools/toral_gamma.py); log [twisted_lm_modes_2026-11-13.txt](../tools/twisted_lm_modes_2026-11-13.txt)).
- **What it does not reach.** Commuting W has invariant subspaces of every dimension: it is the model's
  non-expanding case, as window two is in the original problem. For W in general position the same argument
  gives D ≤ d(n − t + ½) only for subspaces with t + dim WR = n + 1, so the main term is still limited by the
  expansion of W.

## 8. Reduction of the paired model to the unpaired one

Call the model *unpaired* when the U_g are independent (no relation between them), and write D_unp(d; n, w) for the
largest kernel of ⊕_g U_g − K′ there.

**Proposition 5.** In the paired model, D ≤ dn/2 + D_unp(d/2; n, w), where the unpaired instance has the d/2
matrices U_h⁻¹, one from each pair.

*Proof.* Let G₊ contain one site of each pair, G₋ the others. The codewords that vanish on G₊ form a space of
dimension at least D − dn/2. For such x the equations at the sites of G₊ read
U_{ιh} x(h) = Σ_s W_s Σ_{h′ ∈ G₋} κ_s[ιh, h′] x(h′) for h ∈ G₋, which is the unpaired model on G₋ with the matrices
U_{ιh} = U_h⁻¹ and the decoder κ_s[ιh, h′]. (The equations at G₋ are dropped.) ∎

**Numerical, unpaired** (`twisted_lm.py … unpaired`): largest kernel found 13, 13, 13 at d = 8 for n = 3, 4, 5 and 20 at
d = 12, n = 4, all with w = 3; next value not found. This is ⌊d√3⌋ in each case, **independent of n**, and it is the
count of Section 3.

So for data in general position the model's wall is the following statement, in which the pairing no longer
occurs:

  **(U)** for independent U_g in general position, D_unp(d; n, w) ≤ c_w · d with c_w independent of n.

With (U), Proposition 5 gives D ≤ dn/2 + c_w d/2 in the paired model, i.e. rate ½ + O(1/n).

- (U) is a transversality statement. Let 𝔏 be the space of block matrices whose off-diagonal blocks lie in W
  (diagonal blocks arbitrary); it is the union of the translates Δ + (M_d ⊗ W), Δ block diagonal. A translate in
  general position meets a subvariety of 𝔏 only if the codimension of the subvariety in 𝔏 is at most w d². So (U)
  with c_w = √w follows from: the matrices of corank at least D in 𝔏 have codimension greater than w d² in 𝔏 when
  D² > w d². At a point where 𝔏 is transversal to the rank stratum the codimension is D². It fails to be
  transversal exactly where a non-zero matrix Θ with zero diagonal blocks and off-diagonal blocks orthogonal to W
  has its columns in the left kernel and its rows in the kernel; the dimension of that locus is what has to be
  bounded. (Sketch; not carried out.)
- Flags cannot prove (U): every flag bound is proportional to n.
- For representations the same splitting applies with G₋ a set of group elements without inverse pairs, but the
  matrices π(h) are not independent, and the local relations of Section 6 reappear.

## 9. The group model is not the generic model (re-evaluation, 13 November 2026)

Status: written proofs, reviewed by GPT-6 Astra with the qualifications below and in
[the closed-word note](covariant-word-baselines.md). They concern the case U_g = π(g) of
Section 1, which is a slice of the whole-row problem itself (Proposition 1), and they change what Section 8 is
worth.

**Proposition 6 (closed words).** In the unpaired model with scalar blocks (K′ = κ ⊗ 1), let pairwise distinct sites h_1, …, h_k
satisfy U_{h_k} ⋯ U_{h_1} = 1. Then κ = the cyclic permutation of these sites gives a kernel of dimension n on them:
v(h_{j+1}) = U_{h_j} v(h_j). More generally its kernel is the fixed space of the ordered product.
Cycles of length at least two carry rate at most 1/2; singleton loops must be counted separately.
Independent generic matrices avoid any fixed finite list of such product identities; inverse-paired
tuples also have forced longer cancellation words, not only two-cycles.

**Proposition 7 (every half of a quasirandom group has triples).** Let G be a finite group of order d whose
non-trivial complex irreducible representations have dimension at least m ≥ 108, and let G₋ ⊆ G satisfy G₋ ∩ G₋⁻¹ = ∅
and at least d/3 elements. Then G₋ contains at least d/243 − 1 pairwise disjoint triples (a, b, c) of distinct
elements with abc = e. Hence, for every representation π of dimension n and U_h = π(h)⁻¹, the unpaired model on G₋
has a kernel of dimension at least (d/243 − 1) n already at w = 1.

*Proof.* By the counting estimate in the proof of [Gowers, Theorem 3.3](https://arxiv.org/pdf/0710.3877v1), the number of pairs
(a, b) ∈ A × B with ab ∈ C differs from |A||B||C|/d by at most (|A||B||C| d/m)^{1/2}. With A = B = G₋ and C = G₋⁻¹
this number is at least (|G₋|³/d)(1 − (27/m)^{1/2}) ≥ d²/54, and each such pair is a triple (a, b, c) with c ∈ G₋ and
abc = e. At most 3d of them have two equal entries. A selected three-element triple meets at most 9d/2
ordered triples, so a greedy choice gives (d²/54 − 3d)/(9d/2) disjoint ones. Apply Proposition 6 to each, with
(h_1, h_2, h_3) = (a, b, c): U_c U_b U_a = π(abc)⁻¹ = 1. ∎

**Consequence.** The uniform extension of (U) to representation tuples is false on increasingly quasirandom
groups. For a maximal inverse-free half and i inversion-fixed elements, the unrestricted one-sided
certificate has right-hand side at least (1/2 + 1/243 + i/(2d) − 1/d)dn whenever Proposition 7 applies.
A stronger maximal-packing argument gives a **(2/3 − o(1))dn floor** as the minimum nontrivial complex
representation dimension tends to infinity; see [the proof](covariant-word-baselines.md#1-distinct-site-cycles-and-a-stronger-packing-bound).
This is a limitation of that upper-bound expression, not an achieved paired-code rate. It does not disprove
the generic-matrix statement (U), nor exclude a reduction retaining compatibility with the discarded half.

**Proposition 8 (ordered groups).** Let G have a total order invariant under multiplication on both sides (a free
group has one), Σ ⊆ G finite, and S a finite set of elements greater than every element of Σ ∪ {e}. For any scalar
matrices κ_s indexed by S, the map x ↦ (g x_g − Σ_s s Σ_h κ_s[g, h] x_h)_{g ∈ S} on F[G]^S is injective, over every
field. For a covariant decoder, first change coordinates to y_g = x_{g⁻¹}. On a finite symmetric displacement
set S₀, projection to the y-coordinates g ≤ a = max(Σ ∪ {e}) is injective. If every group-algebra coordinate
has support in the same finite set B, the code dimension is at most
|B| (|S₀| + |S₀ ∩ [a⁻¹,a]|)/2. A half-rate consequence needs the interval term to be o(|S₀|).

*Proof.* Let x ≠ 0, let μ be the largest group element in the supports of the x_h, and let it occur in x_g. The
left side of the equation at g contains gμ. Every element of the right side is s u with u ≤ μ and s ∈ Σ, so it is
at most sμ < gμ. ∎

- Proposition 8 works with unbounded coefficients and over every field, but bi-orderability alone does not
  make the interval term small. It proves no unconditional half-rate theorem on ordered covers or finite
  quotients; [the boundary examples](covariant-word-baselines.md#2-what-the-ordered-group-argument-actually-proves)
  specify both limitations.
- This is the shape of the Lück approximation question, in which the series already has a negative answer in
  positive characteristic for other group-ring matrices, and its codes above one half come from exactly that
  failure ([Lück approximation fails](../../Luck-Approximation-Fails-in-Positive-Characteristic/),
  [Storage codes above half rate](../../Storage-Codes-above-Half-Rate-under-Paired-Distance-Separation/)). The
  matrices here are not of that kind (their size grows with the quotient), so this is an analogy, not a theorem.
- Disjoint closed-word cycles of lengths at least two give at most 1/2. That observation does not classify
  helper-relative loops or general coupled decoders. [Exact distant helper-loop examples](covariant-word-baselines.md#4-helper-relative-loops-far-from-the-helpers)
  beat the scalar-monomial baseline in individual sectors, even in a growing simple-group family; the
  same patches give no gain on the regular representation. Distance and sector gains alone are therefore
  insufficient success criteria for the next construction search.
