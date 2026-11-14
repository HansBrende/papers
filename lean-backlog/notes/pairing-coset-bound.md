# Codes built on top of a pairing code gain only O(d)

Status: written proof by Claude Fable, 14 November 2026. Not reviewed, not Lean-verified. No
novelty claim. Front D1; it restricts constructions (D7).

## Statement

Host: helper sets ρ(c) of size at most w; every row lies in at most D helper sets. Alphabet: an
abelian group of order q. N = d².

Let ι be an involution of the cell set such that, for every non-incident cell v = (p,c), the cell
ιv lies in a helper row of c. Put P_ι = {S : S∘ι = S}. It is a whole-row code (each non-incident
cell is copied from its partner), with log_q |P_ι| = (N + f)/2, f the number of fixed cells.
The symmetric matrices are the case ρ(c) = {c}, ι = transposition.

**Theorem.** Let C be a whole-row code, not necessarily linear, with C + P_ι = C. Then

log_q |C| ≤ log_q |P_ι| + (w² + w)·D·d.

So a code that is a union of cosets of a full pairing code exceeds that pairing code by O(d)
symbols at fixed window and reverse degree. For linear C the hypothesis is P_ι ⊂ C.

## Proof

For X ∈ C put A_X[v] = X[v] − X[ιv]. Adding S ∈ P_ι does not change A_X.

Fix a column c and let Inside(c) be the set of cells u in the helper rows of c whose partner ιu is
also in those rows.

*Claim.* For X, Y ∈ C, if A_X = A_Y on Inside(c), then A_X = A_Y on column c.

Define S on the helper rows of c by S[u] = Y[u] − X[u]. On a pair inside the bundle this is
ι-symmetric because A_X = A_Y there. On a cell whose partner is outside the bundle, copy the value
to the partner. Put S = 0 on all remaining pairs. Then S ∈ P_ι, so X + S ∈ C, and X + S agrees
with Y on the helper rows of c. By recovery they agree on column c. For a non-incident v in column
c the partner ιv is in a helper row, so A_{X+S}[v] = A_Y[v], and A_{X+S} = A_X. Incident cells of
column c lie in the bundle and are covered directly. ∎

*Counting.* A non-incident u = (q,m) in the bundle has its partner in a row q′ ∈ ρ(m). It is inside
only if q′ ∈ ρ(c) as well, so m is one of at most D columns helped by q′: at most w·D·w such cells.
The bundle contains at most wD incident cells. So |Inside(c)| ≤ (w² + w)D.

By the claim A_X is determined by its values on the union of the sets Inside(c), at most
(w² + w)D·d cells. Two codewords with the same A differ by an element of P_ι. ∎

## Remarks

- It explains the pattern of the known gadgets at fixed window: the grid code is the pairing code
  plus one shared antisymmetric object, and the window-two difference code has excess d − 1.
- For a linear code C of dimension above (N + f)/2 + (w² + w)Dd it follows that C contains no full
  pairing code, for any pairing ι. A gain of positive density has to destroy pairing, not extend it.
- The same proof works lane by lane for a direct sum of pairing codes on lanes.
- Open: the same conclusion when C is invariant under a pairing code on all but ηN pairs, with the
  loss bounded by a multiple of ηN; and the analogue for codes invariant under a triangle lane code.
