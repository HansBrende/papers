# B. Codes with a recovery matrix

**Status: B1–B3 proved in Lean**, with the strengthenings below. The original Lean statements
are direct specializations of the new theorems; no original hypothesis was strengthened.
All declarations depend at most on `propext`, `Classical.choice`, and `Quot.sound`.

## Setting

N ≥ 0 and M is an N × N matrix. A linear code C ⊆ F^N *has recovery matrix M* if M x = x for all
x in C; row p of M is then a recovery vector for the coordinate p. So C ⊆ ker(1 − M), and the three
statements bound dim ker(1 − M).

## Statements

**Theorem B1 (real or complex, contraction).** If ‖M x‖ ≤ ‖x‖ for all x (Euclidean norm), then
2 dim ker(1 − M) ≤ N + Re tr M.

**Theorem B2 (real or complex).** For every N × N matrix Z, |tr Z|² ≤ rank(Z) · Σ_{i,j} |Z_{ij}|².
Applied to Z = 1 − M, writing D = dim ker(1 − M) and S = ‖1 − M‖_F², this gives

\[
|N-\operatorname{tr}M|^2 + DS \le NS.
\]

If S > 0, equivalently D ≤ N − |N − tr M|² / S. The undivided inequality also covers M = 1;
the original written quotient needed this qualification.

**Proposition B3 (any field in which 2 ≠ 0).** If D is a diagonal matrix with entries ±1 and
D M D = −M, then 2 dim ker(1 − M) ≤ N.

## Strengthenings

**B1: weighted control only on the orthogonal complement.** Let E be a finite-dimensional
real or complex inner-product space, let f be linear, and let C be a subspace fixed pointwise
by f. Write D = dim C and N = dim E. If ‖f x‖ ≤ γ‖x‖ for x ∈ C⊥, then

\[
|\operatorname{tr} f-D|\le (N-D)\gamma,
\qquad
(1+\gamma)D\le\gamma N+\operatorname{Re}\operatorname{tr}f.
\]

The formal statement allows any real γ satisfying the displayed norm hypothesis. Taking γ = 1
and C = ker(1 − M) gives B1. The matrix corollary with a global bound γ is ready for use in A2.

**B2: real scalars and a reusable rectangular trace inequality.** The formalization covers
both ℝ and ℂ. Its Cauchy–Schwarz lemma applies to arbitrary rectangular A and B with AB square:
|tr(AB)|² ≤ (Σ |Aᵢⱼ|²)(Σ |Bᵢⱼ|²). Both recovery-code forms above are also formalized.

**B3: arbitrary injective anticommuting maps.** Let f and g be linear endomorphisms of a
finite-dimensional vector space V over any field. If g is injective and f(g x) = −g(f x), then

\[
\dim E_\mu(f)=\dim E_{-\mu}(f).
\]

If μ ≠ −μ, then 2 dim E_μ(f) ≤ dim V. No diagonality or involution assumption is needed.
The original sign-change statement follows with f = M, g = D and μ = 1.

## Field extensions and algebraic alternatives

The following additions are Lean-verified. The rank and restriction arguments reuse
existing shared results; they are not claimed as new lower-bound mechanisms.

**Transport through embeddings.** If f: F → K is a field embedding, then
rank_K(f(A)) = rank_F(A) and dim_K ker f(A) = dim_F ker A, with f applied entrywise.
In particular, fixed-space dimensions are preserved. B1 and B2 therefore apply to matrices
over any field with a specified embedding into ℝ or ℂ, using norms of the mapped entries.
B1 still requires the mapped matrix to be a contraction (or satisfy the weighted norm
bound); the embedding does not establish this hypothesis. No finite field embeds into ℂ.

**Rank defects in every characteristic.** Let C ⊆ ker(I − M), with M, L, R all N × N over
any field. The existing intertwining rank identity and rank–nullity give

\[
2\dim C+\operatorname{rank}(L-R)
\le 2N+\operatorname{rank}(ML-RM).
\]

If L − R is invertible, this becomes

\[
2\dim C\le N+\operatorname{rank}(ML-RM).
\]

This is an algebraic alternative to B1, with different hypotheses. It requires an actual
low-rank intertwining defect, not small norm or small trace. Witnesses may also be sought
over an extension field: apply the bound to the extended fixed space and use dimension
preservation. If N = d², a defect of rank o(d²) and invertible L − R would recover an
asymptotic half-dimension bound over any field. Producing such witnesses is a separate task.

**Bipartite recovery, including characteristic two.** If S is a coordinate subset and
Mᵢⱼ = 0 whenever i, j ∈ S, then dim C ≤ N − |S|. If the same vanishing holds within Sᶜ,
then

\[
\dim C\le\min(|S|,N-|S|).
\]

Indeed, a fixed vector vanishing outside S vanishes on S too; restriction to Sᶜ is
injective. Apply the argument in both directions for the bipartite statement. In odd
characteristic the sign hypothesis in B3 enforces this support condition, giving the
sharper bound by the smaller sign class. In characteristic two the sign equation alone
is vacuous, but the support criterion remains valid.

**Why traces cannot simply replace ranks.** In characteristic p > 0 the p × p identity
has trace zero in every positive power, yet its fixed space has dimension p. The zero
matrix has the same positive-power traces and a zero-dimensional fixed space. The identity's
zero traces and full fixed dimension are separately Lean-verified below. This obstructs
using those traces alone to determine integer multiplicities; it is not a counterexample
to A4, whose analytic hypotheses have not been translated to finite fields.

### Ordered-field extension of B2: written proof only

For any ordered field F and Z ∈ F^(N × N), the real form of B2 remains valid:

\[
(\operatorname{tr}Z)^2\le (\operatorname{rank}Z)\sum_{i,j} Z_{ij}^2,
\]

where the natural-number rank is interpreted in F. For positive rank r, choose an N × r
matrix B whose columns form a basis of im Z. The Gram matrix G = BᵀB is invertible:
xᵀGx = Σᵢ(Bx)ᵢ² can vanish only if Bx = 0, hence x = 0. Set P = BG⁻¹Bᵀ. Then PZ = Z,
Pᵀ = P, P² = P, and tr P = tr(G⁻¹G) = r. Consequently ΣᵢⱼPᵢⱼ² = r. The algebraic
Cauchy–Schwarz inequality, obtained from the sum-of-squares identity, gives
(tr Z)² = (tr(PZ))² ≤ r ΣᵢⱼZᵢⱼ². Rank zero means Z = 0 and is immediate. This proof needs
neither completeness nor square roots. It is not yet formalized and still requires an
order, so it does not address finite fields.

## Outlines of the formal proofs

*B1.* Split the identity into orthogonal projections onto C and C⊥. Cyclicity of trace gives
tr f = D + tr(Q f|_{C⊥}), where Q projects onto C⊥. The compression is bounded by γ. Express
its trace in an orthonormal basis and bound each diagonal entry by γ. Taking real parts gives
the weighted dimension inequality. For the backlog's positive-semidefinite formulation,
⟨x, (1 − M* M)x⟩ ≥ 0 supplies ‖M x‖ ≤ ‖x‖. ∎

*B2.* Let P be the orthogonal projector on the range of Z; it has rank r = rank Z, so
Σ_{i,j} |P_{ij}|² = tr(P*P) = tr P = r. Since P Z = Z, tr Z = tr(P Z) = Σ_{i,j} P_{ij} Z_{ji}, and by
the Cauchy–Schwarz inequality |tr Z|² ≤ r Σ_{i,j} |Z_{ij}|². ∎

*B3.* Anticommutation embeds E_μ(f) into E_{−μ}(f). Applying the same argument to −μ gives
equality of dimensions. Distinct eigenspaces are disjoint, so their dimensions sum to at most
dim V. For the original criterion, D² = 1 implies injectivity and anticommutation. ∎

## Lean declarations and verification

Each declaration below is in the namespace `LeanMachine.<module>`.

| Item | Module | Main declarations |
|---|---|---|
| B1 | [`RecoveryTrace`](../lean-machine/LeanMachine/RecoveryTrace.lean) | `norm_trace_sub_finrank_le`, `weighted_finrank_le`, `weighted_finrank_fixed_le`, `two_mul_finrank_fixed_le_of_contraction` |
| B2 | [`RecoveryFrobenius`](../lean-machine/LeanMachine/RecoveryFrobenius.lean) | `norm_trace_mul_sq_le`, `norm_trace_sq_le_rank_mul`, `norm_trace_sub_sq_add_finrank_mul_le`, `finrank_fixed_le_sub_div` |
| B3 | [`RecoverySign`](../lean-machine/LeanMachine/RecoverySign.lean) | `finrank_eigenspace_eq_neg`, `two_mul_finrank_eigenspace_le`, `two_mul_finrank_fixed_le_of_sign` |
| Field embeddings | [`MatrixRankCertificate`](../lean-machine/LeanMachine/MatrixRankCertificate.lean) | `rank_map_field`, `finrank_ker_map_field`, `finrank_fixed_map_field` |
| Embedded B1–B2 | [`RecoveryTransfer`](../lean-machine/LeanMachine/RecoveryTransfer.lean) | `weighted_finrank_fixed_le`, `two_mul_finrank_fixed_le_of_contraction`, `norm_trace_sq_le_rank_mul`, `norm_trace_sub_sq_add_finrank_mul_le` |
| Arbitrary-field certificates | [`RecoveryAlgebra`](../lean-machine/LeanMachine/RecoveryAlgebra.lean) | `two_mul_finrank_add_rank_le`, `two_mul_finrank_le_of_isUnit`, `finrank_le_of_zero_square`, `finrank_le_min_of_bipartite` |
| Trace limitation | [`RecoveryAlgebra`](../lean-machine/LeanMachine/RecoveryAlgebra.lean) | `trace_identity_pow_eq_zero`, `finrank_fixed_identity` |

From the repository root:

```sh
cd lean-machine
lake build
lake env lean Axioms.lean
```

For just these modules, use
`lake build LeanMachine.RecoveryTrace LeanMachine.RecoverySign LeanMachine.RecoveryAlgebra LeanMachine.RecoveryTransfer`.
The proofs reuse Mathlib's orthogonal projections, trace cyclicity, rank–nullity,
Cauchy–Schwarz inequality, and disjointness of distinct eigenspaces.

## What it is for

In a storage code on any helper relation, position p is recovered from its helpers by a recovery
vector. For a real or complex code with a zero-diagonal recovery matrix, B1 gives rate at most
one half when the matrix is a contraction. If N > 0 and τ = (Σ |Mᵢⱼ|²)/N, zero diagonal gives
tr M = 0 and ‖1 − M‖_F² = N(1 + τ); B2 then gives rate at most τ/(1 + τ). These rate substitutions
are written consequences, not separately exported Lean theorems. Nonzero diagonal entries must
be accounted for using the full trace and Frobenius expressions above.

B3 gives a half-dimension bound whenever the nonzero matrix entries go between two sign classes,
including over finite fields of odd characteristic. The direct bipartite theorem strengthens
this to the smaller class size and also applies in characteristic two. These are criteria for
recovery matrices; applying them to a tape machine still requires deriving a recovery matrix
with the stated hypotheses.
