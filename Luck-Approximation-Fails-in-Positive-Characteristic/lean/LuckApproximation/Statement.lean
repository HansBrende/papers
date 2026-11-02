import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The Lück approximation conjecture over an arbitrary field

This file states parts (1) and (2) of Conjecture 1.2 of

  A. Jaikin-Zapirain, *L²-Betti numbers and their analogues in positive characteristic*,
  in: Groups St Andrews 2017 in Birmingham, LMS Lecture Note Ser. 455 (2019), 346–406.

The survey calls parts (1) and (2) together the *Lück approximation conjecture*; part (3), the
strong Atiyah conjecture, is not stated here. Parts (1) and (2) of Conjecture 2 of
A. Jaikin-Zapirain and H. Souza, *Sylvester domains and pro-p groups* (arXiv:2402.14130v2;
Doc. Math. 2026, DOI 10.4171/DM/1034) are the same statement.

## Scope of a disproof

* This is Jaikin-Zapirain's version for an arbitrary field `K`. Lück's own approximation
  conjectures concern subfields of `ℂ`, where parts (1) and (2) are known (survey, §1 and
  Thm. 10.1). A counterexample in characteristic `p` disproves the arbitrary-field version only.
* In characteristic `p > 0`, parts (1) and (2) are known only for amenable groups (survey, §1;
  Jaikin-Zapirain–Souza, §8). In a blog post ("The Lück approximation", andreijaikin.wordpress.com,
  6 May 2024) Jaikin-Zapirain expects that in positive characteristic the conjecture holds only
  under conditions on the completion, and states a refined conjecture for embeddings into
  virtually pro-`p` groups. A counterexample along a chain whose completion is not virtually
  pro-`p` leaves that refined conjecture untouched.

## The survey's setting (§1), in the notation used below

* `G` is a group, `K` a field, and `A` an `n × m` matrix over the group algebra `K[G]`.
* For a normal subgroup `N` of finite index, `φ_A^{G/N} : K[G/N]^n → K[G/N]^m` sends a row
  vector `x` to the product `x A`, the entries of `A` being mapped to `K[G/N]`. It is `K`-linear
  (`phi`).
* `rk_{G/N}(A) = dim_K Im φ_A^{G/N} / |G : N|` (`rk`).
* A chain is `G > G₁ > G₂ > ⋯` with every `Gᵢ` normal in `G`, of finite index, and with
  `⋂ Gᵢ = {1}` (`Chain`).

## Conjecture 1.2, parts (1) and (2)

1. Along every chain the sequence `i ↦ rk_{G/Gᵢ}(A)` converges (`Convergence`).
2. The limit does not depend on the chain (`ChainIndependence`).

`LuckApproximation K G` is the conjunction, for one field and one group, and
`LuckApproximationConjecture` quantifies over all fields and groups in `Type`.

## Conventions

* Chains are indexed from `0`; the first term may be `G` itself. Dropping or adding finitely many
  initial terms does not change limits.
* The inclusions are strict, as in `G > G₁ > ⋯`. Quantifying only over strictly descending chains
  can only weaken the conjecture, so a disproof of this version disproves the non-strict reading
  too. (For infinite `G` the two readings are equivalent: in a non-strict chain with trivial
  intersection no term repeats infinitely often.)
-/

namespace Luck

open Filter Topology

universe u v

section Rank

variable (K : Type u) [Field K] {G : Type v} [Group G]

/-- The image of a matrix over `K[G]` under the ring map `K[G] → K[G/N]` induced by the quotient
map `G → G/N`. -/
noncomputable def quotientMatrix (N : Subgroup G) [N.Normal] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    Matrix (Fin n) (Fin m) (MonoidAlgebra K (G ⧸ N)) :=
  A.map (MonoidAlgebra.mapDomainRingHom K (QuotientGroup.mk' N))

/-- `φ_A^{G/N} : K[G/N]^n → K[G/N]^m`, `x ↦ x A` (row vectors), as a `K`-linear map. -/
noncomputable def phi (N : Subgroup G) [N.Normal] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    (Fin n → MonoidAlgebra K (G ⧸ N)) →ₗ[K] (Fin m → MonoidAlgebra K (G ⧸ N)) where
  toFun x := Matrix.vecMul x (quotientMatrix K N A)
  map_add' x y := Matrix.add_vecMul _ x y
  map_smul' c x := Matrix.smul_vecMul c x _

/-- `rk_{G/N}(A) = dim_K Im φ_A^{G/N} / |G : N|`, defined (as in the survey) only for `N` of finite
index, where `K[G/N]` is finite-dimensional. -/
noncomputable def rk (N : Subgroup G) [N.Normal] [N.FiniteIndex] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : ℝ :=
  (Module.finrank K (LinearMap.range (phi K N A)) : ℝ) / (N.index : ℝ)

end Rank

/-- A chain `G > G₁ > G₂ > ⋯`: a strictly descending sequence of normal subgroups of finite index
with trivial intersection. -/
structure Chain (G : Type v) [Group G] where
  /-- The terms of the chain. -/
  N : ℕ → Subgroup G
  normal : ∀ i, (N i).Normal
  finiteIndex : ∀ i, (N i).FiniteIndex
  strictAnti : StrictAnti N
  iInf_eq_bot : ⨅ i, N i = ⊥

/-- The sequence `i ↦ rk_{G/Gᵢ}(A)` along a chain. -/
noncomputable def Chain.rkSeq (K : Type u) [Field K] {G : Type v} [Group G] (c : Chain G)
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : ℕ → ℝ :=
  fun i => haveI := c.normal i; haveI := c.finiteIndex i; rk K (c.N i) A

/-- Conjecture 1.2 (1) over `K` for `G`: along every chain, `rk_{G/Gᵢ}(A)` converges. -/
def Convergence (K : Type u) [Field K] (G : Type v) [Group G] : Prop :=
  ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) (c : Chain G),
    ∃ l : ℝ, Tendsto (c.rkSeq K A) atTop (𝓝 l)

/-- Conjecture 1.2 (2) over `K` for `G`: the limit does not depend on the chain. -/
def ChainIndependence (K : Type u) [Field K] (G : Type v) [Group G] : Prop :=
  ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) (c₁ c₂ : Chain G) (l₁ l₂ : ℝ),
    Tendsto (c₁.rkSeq K A) atTop (𝓝 l₁) → Tendsto (c₂.rkSeq K A) atTop (𝓝 l₂) → l₁ = l₂

/-- **The Lück approximation conjecture over `K` for `G`**: parts (1) and (2) of Conjecture 1.2. -/
def LuckApproximation (K : Type u) [Field K] (G : Type v) [Group G] : Prop :=
  Convergence K G ∧ ChainIndependence K G

/-- The Lück approximation conjecture for every field and every group (in `Type`). -/
def LuckApproximationConjecture : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [Group G], LuckApproximation K G

/-- The target of the formal statement: the conjecture fails over `𝔽₃` for a free group of finite
rank. It negates the conjunction of parts (1) and (2). The main theorem (`Main.lean`) proves more,
assuming `Luck.Op.KernelNotNegligible` (proved in the paper, not in Lean): part (2) fails for
`FreeGroup (Fin 89)` over every field of characteristic 3. -/
def MainTheoremTarget : Prop :=
  ∃ r : ℕ, ¬ LuckApproximation (ZMod 3) (FreeGroup (Fin r))

end Luck
