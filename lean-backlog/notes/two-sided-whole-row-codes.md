# Two-sided whole-row codes: using the involution of the problem

Status: proposal and written arguments by Claude Fable, 14 November 2026. Not reviewed, not
Lean-verified. Section 1 must be audited against the Lean transfer before anything is built on it.
Front D10 of the [roadmap](../wall.md). No novelty claim.

## 1. The observation

Let an oblivious machine transpose, and let ρ be the helper map of breach B1: after the cheap cut,
output row r depends on the input only through input rows ρ(r) and the advice. ρ depends on the
schedule, not on the data.

Output row r on input A is column r of A. Output row r on input Aᵀ is **row r of A**, and it depends
on input rows ρ(r) of Aᵀ, which are **columns ρ(r) of A**.

Let a(A) be the advice, B bits. Fix the most frequent pair (τ, τ′) and put
C = {A : a(A) = τ, a(Aᵀ) = τ′}. Then |C| ≥ 2^{N − 2B}, and on C

- column r is a function of rows ρ(r), and
- row r is a function of columns ρ(r),

for every non-exceptional r, with the same ρ. Call such a code *two-sided*. Equivalently C and Cᵀ
are both whole-row codes for ρ.

**Consequence.** If every two-sided whole-row code at window w has at most 2^{(1 − δ₂)N} words,
then B ≥ δ₂N/2. So in the wall statement "whole-row code" may be replaced by "two-sided whole-row
code", at the cost of a factor two in the deficit. The class of codes is smaller; every bound we
have still applies.

To audit: the Lean transfer (`cruxOn_of_wholeRowBounds`) takes one fibre of one advice value. The
two-sided version needs the fibre of the pair (a(A), a(Aᵀ)) and exceptional rows as well as columns.

## 2. What survives and what does not

- **Pairing survives exactly on symmetric incidences.** A pair (p,c) ~ (q,m) serves both
  directions iff q ∈ ρ(c), c ∈ ρ(q), p ∈ ρ(m), m ∈ ρ(p). On a symmetric relation (p ∈ ρ(c) iff
  c ∈ ρ(p)) every pairing code is two-sided.
- **Triangles survive.** Index Fano by the standard polarity (column r is the line r^⊥). The
  three-lane triangle code is two-sided, so the value 119/3 is unchanged. The complete host
  ρ(r) = [s] ∖ {r} with one diagonal check is two-sided too. So the two-sided statement still fails
  at growing windows, as it must.
- **One-way recovery is expensive.** Cells x → y → z → x with each recovered row-wise from the
  next and column-wise from the previous form a two-sided code of rate 1/3: two independent checks
  for three cells, against one check for two cells in a pair.
- **Not known to survive:** the difference code on ρ(r) = {r, r+1}. Its only symmetric incidences
  are the loops. Row c would have to be recovered from columns c and c + 1, which carry differences
  in the wrong index. I expect the two-sided value there to be d(d+1)/2 + O(1) against d(d+3)/2 − 1.

## 3. A first lemma: rows without a symmetric incidence are redundant

Put ρ²(p) = ∪_{c ∈ ρ(p)} ρ(c). In a two-sided code row p is a function of columns ρ(p), hence of
rows ρ²(p).

**Lemma.** Let R = {p : p ∉ ρ²(p)}. Then log_q |C| ≤ d² − d|R|/(2w² + 1).

*Proof.* The digraph p → ρ²(p) on R has out-degree at most w², so its underlying graph has an
independent set A with |A| ≥ |R|/(2w² + 1). For p ∈ A the rows ρ²(p) lie outside A, so the rows of
A are functions of the other rows. ∎

So at rate 1 − ε all but ε(2w² + 1)d row indices p have some c with c ∈ ρ(p) and p ∈ ρ(c). On a
relation with no symmetric incidences the closure cascades: for a uniformly random relation a row
set of density s has P(ρ²(p) ⊂ S) ≈ s^{w²} > 0, so the hosts that are hardest for one-sided order
bounds have two-sided rate o(1) (heuristic count, not written out).

## 4. Common functions of a row bundle and a column bundle

In a two-sided code X[p,c] = f(rows ρ(c)) = g(columns ρ(p)). The two bundles meet in the w × w
block ρ(c) × ρ(p), which is exactly the set of cells mutual with (p,c).

**Lemma (rectangle form).** For a row set S and a column set T let
V = {(p,c) : ρ(c) ⊂ S, ρ(p) ⊂ T, (p,c) ∉ S × T}. Then X_V is a common function of X_{rows S} and
X_{columns T}, so H(X_V | X_{S×T}) ≤ I(rows S; columns T | S × T) ≤ 2(d² − H(X)), and
|V| ≤ 3(d² − H(X)) in symbol units.

With T everything this is the order bound. Optimising S and T gives a deficit of order 1/w again,
so the lemma is a new mechanism with no new constant. What would give more: showing that at high
rate X[p,c] is (nearly) a function of its mutual block. Shearer over the bundles gives only
Σ_{p,c} H(X[p,c] | block) ≤ 2wd(d² − H(X)), which is vacuous. If that localisation held, every
theorem we have for mutual-only recovery would apply to native fibres.

## 5. Tests that decide whether the premise has bite

Exact two-sided values (same pipeline, both closure rules) on hosts where the one-sided value
exceeds pairing:

| host | pairing | one-sided value | two-sided |
|---|---:|---:|---|
| cyclic ρ(r) = {r, r+1}, d = 5 | 15 | 19 | ? |
| basis host d = 8, w = 3 (symmetric relation) | 44 | 46 | ? |
| Fano with the polarity indexing | — | 119/3 | 119/3 (triangle code) |

If the first two drop to pairing, the natural conjecture is that two-sided codes at fixed window
have rate one half, with fewer gadgets in the way. If neither drops, the premise is a free
strengthening of the statement and nothing more.
