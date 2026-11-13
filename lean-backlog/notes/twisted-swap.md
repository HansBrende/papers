# The twisted swap: covariant whole-row decoders on Cayley relations, and a small model of the wall

Status (2026-11-13, Hans Brende and Claude Fable 5.2): Propositions 1 to 3 have short written proofs, not
reviewed. Section 4 is numerical: real field, searches by a local optimizer, so a value "found" is a verified
kernel dimension at tolerance 1e-8 and a value "not found" proves nothing. Nothing here is in Lean.

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
