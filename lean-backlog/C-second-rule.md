# C. The second rule for whole-row decoders

## Setting

F is any field, d ≥ 1. A *row relation* ρ assigns to every column index r a set ρ(r) of row
indices. For d × d matrices M_{rs} over F (one for every pair with s ∈ ρ(r)) the *code* is

  C = {X ∈ F^{d×d} : column r of X = Σ_{s ∈ ρ(r)} M_{rs} · (row s of X) for every r},

that is, X_{ir} = Σ_{s ∈ ρ(r)} Σ_j (M_{rs})_{ij} X_{sj}.

Fix an order s_0, …, s_{d−1} of the rows. At step t put
- A_t = {s_0, …, s_{t−1}} (the rows known before step t),
- B_t = {r : ρ(r) ⊆ A_t} (the columns that the known rows determine),
- F_t = {r : s_t ∈ ρ(r) ⊆ A_t ∪ {s_t}} (the columns whose only unknown row is the new one).

## Statements

**Proposition C1 (general blocks).** Let Y_t be the matrix obtained by stacking, over r ∈ F_t, the
submatrices of M_{r s_t} with rows in A_t and columns outside B_t. Then
dim C ≤ Σ_t (d − |B_t| − rank Y_t).

**Corollary C2 (invertible blocks).** If every M_{rs} with s ∈ ρ(r) is invertible, then
dim C ≤ Σ_t (d − max(|B_t|, |A_t| · [F_t ≠ ∅])).

Only C2 is in `Statements.lean` (`finrank_rowCode_le`); there the order is a permutation σ of
`Fin d`, s_t = σ t and |A_t| = t.

## Proofs

*C1.* Let C_t = {X ∈ C : the rows in A_t of X vanish}. Then C_0 = C, C_d = 0, C_{t+1} ⊆ C_t, and
C_t / C_{t+1} embeds in F^d by X ↦ row s_t of X. So dim C = Σ_t δ_t with
δ_t = dim{row s_t of X : X ∈ C_t}.
Let X ∈ C_t and x = row s_t of X.
- For r ∈ B_t all rows of ρ(r) vanish, so column r of X vanishes; in particular x_r = 0.
- For r ∈ F_t the other rows of ρ(r) vanish, so column r of X equals M_{r s_t} x; its entries in the
  rows of A_t vanish, because those rows of X vanish. Together with the first point,
  Σ_{j ∉ B_t} (M_{r s_t})_{ij} x_j = 0 for every i ∈ A_t.
So x lies in the space of vectors supported outside B_t that Y_t annihilates, of dimension
d − |B_t| − rank Y_t. ∎

*C2.* If F_t is empty, C1 gives d − |B_t| and |B_t| is the maximum. Otherwise take one r ∈ F_t and
M = M_{r s_t}. The rows of M with index in A_t are linearly independent, so the submatrix with
these rows has rank |A_t|, and deleting the |B_t| columns of B_t lowers the rank by at most |B_t|.
So rank Y_t ≥ max(0, |A_t| − |B_t|) and d − |B_t| − rank Y_t ≤ d − max(|B_t|, |A_t|). ∎

## Suggested route in Lean

- The filtration C_t and the identity dim C = Σ_t δ_t: a chain of submodules with
  `Submodule.finrank_quotient_add_finrank` or `LinearMap.finrank_range_add_finrank_ker` applied to
  X ↦ row s_t of X on C_t.
- For C2 one can skip Y_t: for X ∈ C_t and r ∈ F_t the vector x satisfies x_j = 0 for j ∈ B_t and
  (M x)_i = 0 for i ∈ A_t, and M is invertible, so x is determined by the coordinates of M x
  outside A_t; this gives δ_t ≤ d − |A_t| directly, and δ_t ≤ d − |B_t| from the first point.
- C1 with the rank of a stacked submatrix is heavier to state; it is optional.

## What it is for

With Y_t omitted this is the known bound from an order of the rows. The second rule (a column and
all but one of its rows give the last row when the block is invertible) improves it on every
relation: on small instances the right side of C2, minimised over orders, is below the dimension
of the codes that pair positions, so decoders with invertible blocks cannot reach the best codes
known. It holds over every field.
