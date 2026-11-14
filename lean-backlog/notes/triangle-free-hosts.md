# Hosts without mutual triangles, and the soft form of the order bound

Status: Sections 1–3 and 5 are written proofs by Claude Fable, not reviewed, not Lean-verified.
Section 4 is a proof sketch. Section 6 is numerical and heuristic. No novelty claim.
Tools: [host-probe](../tools/host-probe/).

Setting: an incidence host has rows = points, columns = lines, and the helpers of a column are the
points on its line. A cell (p, ℓ) is *incident* if p ∈ ℓ; incident cells are free in every code.
Two non-incident cells (p, ℓ), (q, m) are *mutual* if q ∈ ℓ and p ∈ m. A *mutual triangle* is three
pairwise mutual cells. For a cell v, H_v is the set of cells in the helper rows of its column.

## 1. An explicit code beyond pairing on the 3×3 grid

Host: points (i, j) ∈ Z₃², lines R_k (first coordinate k) and C_k (second coordinate k). It has 54
cells, 36 non-incident, no mutual triangle. Pairing gives 18 on the non-incident cells; the order
value is 23 (36 minus the largest acyclic set, 13, by exact recurrence).

Write A_j[i,k] = X[(i,j), R_k] for i ≠ k and B_i[j,k] = X[(i,j), C_k] for j ≠ k. Take free symbols
S_j[i,k] and T_i[j,k] (first index smaller) and D[a,b] (a < b) in an abelian group of order q, and put

- A_j[i,k] = S_j[i,k] and A_j[k,i] = S_j[i,k] − D[i,k] for i < k;
- B_i[j,k] = T_i[j,k] and B_i[k,j] = T_i[j,k] − D[j,k] for j < k.

**Proposition.** This is a whole-row code with q^21 words on the non-incident cells, for every q ≥ 2.
Hence 39 ≤ log_q(capacity) ≤ 41 on the 54 cells, against 36 for pairing.

*Proof.* The helper rows of R_k are (k,0), (k,1), (k,2). They contain row k of every A_j and all of
B_k. D is the difference of opposite entries of B_k, so A_j[i,k] = A_j[k,i] ± D is determined. The
same argument with A and B exchanged gives C_k. The 21 parameters are entries of the word. ∎

The gain over pairing is one shared three-symbol object that the helper rows of every line reveal.
On the m × m grid the same construction adds m(m−1)/2 symbols to a pairing value m²(m−1): a term of
lower order, like the d − 1 of the cyclic window-two code. Whether 22 or 23 is attained is open.

## 2. Order values (exact)

| host | non-incident cells | largest acyclic set | order value | pairing / triangle value |
|---|---:|---:|---:|---:|
| Fano | 28 | 8 | 20 | 56/3 (triangles) |
| PG(2,3) | 117 | 29 | 88 | 78 (triangles) |
| 3×3 grid | 36 | 13 | 23 | 18 (pairing), 21 (Section 1) |
| quadrangle of order (2,2) | 180 | 62 | 118 | 90 (pairing) |

The two planes agree with the values in the projective-plane calibration note. The quadrangle is
the smallest triangle-free configuration with three points on a line and three lines on a point.

## 3. The soft form of the order bound

For random variables X_v on the cells put TC = Σ_v H(X_v) − H(X), the total correlation.

**Lemma.** Let A be a set of cells that is acyclic for the helper relation v → H_v. Then, for
arbitrary random variables, Σ_{v∈A} I(X_v; X_{H_v}) ≤ TC.

*Proof.* Order A so that H_v ∩ A precedes v, and put the cells outside A first. Then
Σ_{v∈A} I(X_v; X_{H_v}) ≤ Σ_{v∈A} I(X_v; X_{<v}) = Σ_{v∈A} H(X_v) − H(X_A | X_{outside}), and this is
TC(X_A) + I(X_A; X_{outside}) ≤ TC. ∎

For a code I(X_v; X_{H_v}) = H(X_v), and the lemma is the order bound H(X) ≤ Σ_{v∉A} H(X_v).
Averaging over acyclic sets cannot do better than the largest one. Define

c(host) = sup over all distributions of Σ_v I(X_v; X_{H_v}) / TC.

Every code has H(X) ≤ (1 − 1/c) Σ_v H(X_v) on the cells that need recovery. Averaging the lemma
over acyclic sets gives c ≤ the fractional acyclic chromatic number, which is N/α on a transitive
host (N cells, α the largest acyclic set); a mutual s-clique gives c ≥ s. The paid Fano
inequality is the statement c(Fano) = 3, against N/α = 7/2. In this language a *high-order base* is
a family with c bounded and N/α unbounded.

## 4. Triangle codes do not survive at fixed window (sketch)

**Claim.** In a host with windows at most w on d rows, every fractional packing of mutual triangles
into cells has total weight O(w^{3/2} d^{3/2}).

Call a row heavy if it helps more than εd/w columns; there are at most w²/ε heavy rows. A triangle
on rows p, q, r with at most one heavy row has a cell whose two partner rows are light, and there
are at most εwd² such cells: for a column ℓ and a light q ∈ ρ(ℓ), fewer than εd rows share a column
with q. A triangle with two heavy rows has two cells in heavy rows, and there are at most dw²/ε
cells in heavy rows. Take ε = d^{-1/2}.

This limits the *attaining code*, not the bound: the amplification theorem carries the Fano upper
bound to fixed window, while the three-lane code does not lift. On those lifts nothing is known
about the capacity beyond the upper bound 17/21.

## 5. Where the order bound loses on two lines of a plane

In PG(2,n) let ℓ₁, ℓ₂ meet at o. Let O be the row of o, A_i the rows of ℓ_i ∖ {o}, and K₁₂ the n
cells (a, ℓ₁) with a ∈ ℓ₂ ∖ {o}; K₂₁ symmetrically. K₁₂ lies in A₂ and is a function of (O, A₁). So
(K₁₂, K₂₁) is a common function of (O, A₁) and (O, A₂), and

H(A₁, A₂ | O) ≤ 2(n³ − n) + I(K₁₂; K₂₁ | O).

The order bound is the case I = n. In the triangle lane code I = 2n/(n+1): the two cross sets are
almost independent given the common row, and they are coupled only through the n² triangles with a
vertex at o. Every cell of K₁₂ is mutual with every cell of K₂₁, so I(K₁₂; K₂₁ | O) measures how
much a code *pairs* across the two lines. A proof of the two-thirds value for planes has to show
that pairing across line pairs is paid for elsewhere.

Submodularity on two cell sets A, B is tight for the triangle code exactly when no triangle lies in
A ∪ B without lying in A or in B. Two line closures always satisfy this (three non-collinear points
of ℓ₁ ∪ ℓ₂ have two on one line). For order n > 2 the closure of a point set is everything only when
at most one point is missing, so the final steps of the seven-point certificate (two five-point
closures covering everything) have no analogue, and a proof must average over many closures.

## 6. Numerical leads (heuristic)

Alternating least squares for a real matrix of rank N − K supported on the helper relation
(`als.py`):

- Fano and PG(2,3): every run above the triangle value stops at squared error exactly 3K − 2N
  (Fano K = 19: 1.0; PG(2,3) K = 80, 84, 90: 6, 18, 36). That is the value of a packing by disjoint
  rank-one triangle blocks. Nothing above 2N/3 was found at order three.
- Grid: full convergence at K = 19, 20, 21, none at 22, 23.
- The method returns errors near 10⁻³ at K = 24 on the grid, which is impossible. Runs that do not
  converge fully carry no information.
