# C. The second rule for whole-row decoders

**Status:** C1 and C2 are proved in Lean, together with a local-invertibility refinement of C2.
The definitions and proofs are in `LeanMachine.WholeRow`. The original C2 statement follows
directly, without weakened hypotheses; the formalization also includes d = 0.

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

C2 originally appeared in `Statements.lean` as `finrank_rowCode_le`; C1 was an optional written
target. Both are now verified. The order is a permutation σ of `Fin d`, s_t = σ t and |A_t| = t.

**Formalized refinement of C2 (local invertibility).** Put
F_t^× = {r ∈ F_t : M_{r s_t} is invertible}. Without any global invertibility assumption,

$$
\dim C\le\sum_t\left(d-\max\left(|B_t|,\ |A_t|\,[F_t^\times\ne\varnothing]\right)\right).
$$

Only one invertible frontier block is needed to apply the second rule at a step; all other
blocks may be singular. If every incident block is invertible, F_t^× = F_t and this gives C2
exactly. The shared statements also allow arbitrary finite ordered index types.

## Outlines of the formal proofs

*Common dimension argument.* Let U_t be the subspace of row vectors x satisfying
x_j = 0 for j ∈ B_t and (M_{r s_t} x)_i = 0 for every r ∈ F_t and i ∈ A_t.
If X ∈ C has all earlier rows zero, its current row lies in U_t:

- A completed column has only vanishing helper rows, so that entire column vanishes.
- A frontier column has only one potentially nonzero helper row, so it equals M_{r s_t} x.
  Its entries in the earlier rows vanish.

For each t choose a linear retraction p_t from F^d to U_t, using Mathlib's left-inverse theorem
for the subspace inclusion. The map X ↦ (p_t(row s_t of X))_t is injective on C. Indeed, if all
these records vanish, induction in t shows each row vanishes: after the earlier rows vanish,
the current row lies in U_t, where p_t is the identity. Hence dim C ≤ Σ_t dim U_t.
The reusable theorem `SequentialDimension.finrank_le_sum_of_prefix` proves this for arbitrary
finite-dimensional coordinate spaces and conditional subspaces. This avoids a separate
quotient-filtration formalization.

*C1.* Restrict a vector in U_t to coordinates outside B_t. This restriction is injective,
since its coordinates in B_t already vanish. The restricted vector lies in ker Y_t by the
frontier constraints. Mathlib's rank–nullity identity gives
dim U_t ≤ d − |B_t| − rank Y_t. Summing proves C1. The matrix `stepMatrix` has entries
Y_t((r,i),j) = (M_{r s_t})_{ij}, with r ∈ F_t, i ∈ A_t and j ∉ B_t, exactly as in the statement.

*C2 and the local refinement.* Restriction outside B_t first gives dim U_t ≤ d − |B_t|.
If r ∈ F_t^×, the map x ↦ M_{r s_t}x is injective and its entries on A_t vanish for x ∈ U_t.
Therefore its coordinates outside A_t still distinguish vectors of U_t, giving
dim U_t ≤ d − |A_t|. Combine the two bounds, then sum. This proves the local version directly;
the global invertibility hypothesis makes every frontier block usable and yields C2. ∎

## Verified declarations

Names in this table have prefix `LeanMachine.WholeRow`.

| Statement | Declaration | Module |
|---|---|---|
| Code, known rows, completed columns, frontier | `rowCode`, `known`, `complete`, `frontier` | [`Basic`](../lean-machine/LeanMachine/WholeRow/Basic.lean) |
| Necessary per-step constraints | `row_mem_stepSpace` | `Basic` |
| Common ordered dimension bound | `finrank_rowCode_le_sum_stepSpace` | [`Bounds`](../lean-machine/LeanMachine/WholeRow/Bounds.lean) |
| Local invertibility refinement | `finrank_rowCode_le_local` | `Bounds` |
| C2, original invertible-block bound | `finrank_rowCode_le` | `Bounds` |
| The stacked matrix Y_t | `stepMatrix` | [`Rank`](../lean-machine/LeanMachine/WholeRow/Rank.lean) |
| Per-step joint-rank bound | `finrank_rowSpace_add_rank_le` | `Rank` |
| C1, arbitrary blocks | `finrank_rowCode_le_rank` | `Rank` |

The proofs use only `propext`, `Classical.choice` and `Quot.sound`. See the
[module guide](../lean-machine/LeanMachine/WholeRow/README.md) for shared dependencies and
build commands. No C1 or C2 formalization obligations remain.

## What it is for

Ignoring the frontier gives the ordered bound Σ_t (d − |B_t|). C2 and its local refinement are
never worse than that bound; strict improvement depends on the relation and order. C1 additionally
retains the joint rank of all frontier constraints, which can be useful even when every block is
singular. These are obstructions for linear whole-row decoders over every field, independent of
the norm assumptions used in item A.

The original notes also report small-instance numerical comparisons with codes built by pairing
positions. Those comparisons are not used in these proofs and have not been formalized here.
