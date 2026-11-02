import LuckApproximation.Statement
import Mathlib.Order.CompletePartialOrder

/-!
# A second, independent formalisation of the conjecture, proved equivalent

Written independently from the survey's text, then compared with `LuckApproximation/Statement.lean` and
proved equivalent in Lean.

Source: A. Jaikin-Zapirain, *L²-Betti numbers and their analogues in positive characteristic*
(2019), §1: formula (1) for `rk_{G/N}` and Conjecture 1.2, parts (1) and (2).

Literal reading: `G` a group, `K` a field, `A ∈ Mat_{n×m}(K[G])`, `N ⊴ G` of finite index,
`φ^A_{G/N} : K[G/N]^n → K[G/N]^m, (x₁,…,xₙ) ↦ (x₁,…,xₙ) A`,
`rk_{G/N}(A) = dim_K Im φ^A_{G/N} / |G : N|`.
A chain is `G > G₁ > G₂ > ⋯` (strict, starting below `G`), each `Gᵢ` normal of finite index,
with `⋂ Gᵢ = {1}`.

* `Luck.Literal.equiv`: `Conj K G ↔ Luck.LuckApproximation K G`.
* `Luck.Literal.nonStrict_imp_luck`: the non-strict reading `G ≥ G₁ ≥ ⋯` implies
  `Luck.LuckApproximation K G`, so a disproof of the latter disproves that reading as well.
-/

open Filter Topology

namespace Luck.Literal

universe u v

section Rank

variable (K : Type u) [Field K] {G : Type v} [Group G]

/-- The image of a matrix over `K[G]` in `Mat_{n×m}(K[G/N])`, via the ring map induced by the
quotient map `G → G/N`. -/
noncomputable def reduce (N : Subgroup G) [N.Normal] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    Matrix (Fin n) (Fin m) (MonoidAlgebra K (G ⧸ N)) :=
  A.map (MonoidAlgebra.mapDomainRingHom K (QuotientGroup.mk' N))

/-- `φ^A_{G/N} : K[G/N]^n → K[G/N]^m`, `x ↦ x A` with `x` a row vector, as a `K`-linear map. -/
noncomputable def phi (N : Subgroup G) [N.Normal] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    (Fin n → MonoidAlgebra K (G ⧸ N)) →ₗ[K] (Fin m → MonoidAlgebra K (G ⧸ N)) where
  toFun x := Matrix.vecMul x (reduce K N A)
  map_add' x y := Matrix.add_vecMul _ x y
  map_smul' c x := Matrix.smul_vecMul c x _

/-- `rk_{G/N}(A) = dim_K Im φ^A_{G/N} / |G : N|` (formula (1) of the survey). -/
noncomputable def rk (N : Subgroup G) [N.Normal] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : ℝ :=
  (Module.finrank K (LinearMap.range (phi K N A)) : ℝ) / (N.index : ℝ)

end Rank

/-- A chain `G > G₁ > G₂ > ⋯` of normal subgroups of finite index with `⋂ᵢ Gᵢ = {1}`.
`sub i` is `G_{i+1}`.  The inclusions are strict (`>`), as the survey writes `≤` for
not-necessarily-proper subgroups elsewhere. -/
structure Chain (G : Type v) [Group G] where
  sub : ℕ → Subgroup G
  first_lt : sub 0 < ⊤
  strict : ∀ i, sub (i + 1) < sub i
  normal : ∀ i, (sub i).Normal
  finiteIndex : ∀ i, (sub i).index ≠ 0
  inter : ⨅ i, sub i = ⊥

/-- The sequence `{rk_{G/Gᵢ}(A)}_{i ≥ 1}` (shifted to start at `0`). -/
noncomputable def seq (K : Type u) [Field K] {G : Type v} [Group G] (c : Chain G) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : ℕ → ℝ :=
  fun i => haveI := c.normal i; rk K (c.sub i) A

/-- Conjecture 1.2 (1) for `A`: the sequence converges, for every chain. -/
def Part1 (K : Type u) [Field K] (G : Type v) [Group G] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : Prop :=
  ∀ c : Chain G, ∃ L : ℝ, Tendsto (seq K c A) atTop (𝓝 L)

/-- Conjecture 1.2 (2) for `A`: the limit does not depend on the chain. -/
def Part2 (K : Type u) [Field K] (G : Type v) [Group G] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : Prop :=
  ∀ (c c' : Chain G) (L L' : ℝ),
    Tendsto (seq K c A) atTop (𝓝 L) → Tendsto (seq K c' A) atTop (𝓝 L') → L = L'

/-- Parts (1) and (2) of Conjecture 1.2 hold for every matrix over `K[G]`. -/
def Conj (K : Type u) [Field K] (G : Type v) [Group G] : Prop :=
  ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)), Part1 K G A ∧ Part2 K G A

/-! ## Comparison with `Luck.LuckApproximation` -/

section Compare

variable {K : Type u} [Field K] {G : Type v} [Group G]

/-- The two rank functions are the same term up to unfolding. -/
theorem rk_eq_luck (N : Subgroup G) [N.Normal] [N.FiniteIndex] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : rk K N A = Luck.rk K N A := rfl

/-- Every chain in the literal sense (`G > G₁ > ⋯`) is a `Luck.Chain`. -/
def Chain.toLuck (c : Chain G) : Luck.Chain G where
  N := c.sub
  normal := c.normal
  finiteIndex i := ⟨c.finiteIndex i⟩
  strictAnti := strictAnti_nat_of_succ_lt c.strict
  iInf_eq_bot := c.inter

theorem Chain.toLuck_rkSeq (c : Chain G) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    c.toLuck.rkSeq K A = seq K c A := rfl

/-- A `Luck.Chain` (whose first term may be `G`) with its first term dropped is a chain in the
literal sense. -/
def ofLuck (c : Luck.Chain G) : Chain G where
  sub i := c.N (i + 1)
  first_lt := lt_of_lt_of_le (c.strictAnti (Nat.lt_succ_self 0)) le_top
  strict i := c.strictAnti (Nat.lt_succ_self (i + 1))
  normal i := c.normal (i + 1)
  finiteIndex i := (c.finiteIndex (i + 1)).index_ne_zero
  inter := by
    apply eq_bot_iff.mpr
    rw [← c.iInf_eq_bot]
    exact le_iInf fun i => (iInf_le _ i).trans (c.strictAnti.antitone (Nat.le_succ i))

theorem ofLuck_seq (c : Luck.Chain G) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    seq K (ofLuck c) A = fun i => c.rkSeq K A (i + 1) := rfl

theorem tendsto_ofLuck_iff (c : Luck.Chain G) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) (L : ℝ) :
    Tendsto (seq K (ofLuck c) A) atTop (𝓝 L) ↔ Tendsto (c.rkSeq K A) atTop (𝓝 L) := by
  rw [ofLuck_seq]
  exact Filter.tendsto_add_atTop_iff_nat (f := c.rkSeq K A) 1

end Compare

/-- **Equivalence.** The literal formalisation agrees with `Luck.LuckApproximation`. -/
theorem equiv (K : Type u) [Field K] (G : Type v) [Group G] :
    Conj K G ↔ Luck.LuckApproximation K G := by
  constructor
  · intro h
    refine ⟨fun n m A c => ?_, fun n m A c₁ c₂ l₁ l₂ h₁ h₂ => ?_⟩
    · obtain ⟨L, hL⟩ := (h n m A).1 (ofLuck c)
      exact ⟨L, (tendsto_ofLuck_iff c A L).mp hL⟩
    · exact (h n m A).2 (ofLuck c₁) (ofLuck c₂) l₁ l₂
        ((tendsto_ofLuck_iff c₁ A l₁).mpr h₁) ((tendsto_ofLuck_iff c₂ A l₂).mpr h₂)
  · rintro ⟨hconv, hind⟩ n m A
    refine ⟨fun c => ?_, fun c c' L L' hL hL' => ?_⟩
    · obtain ⟨L, hL⟩ := hconv n m A c.toLuck
      exact ⟨L, by rwa [Chain.toLuck_rkSeq] at hL⟩
    · exact hind n m A c.toLuck c'.toLuck L L'
        (by rwa [Chain.toLuck_rkSeq]) (by rwa [Chain.toLuck_rkSeq])

/-- The direction needed for a disproof: a disproof of `Luck.LuckApproximation K G` disproves the
literal statement. -/
theorem conj_imp_luck (K : Type u) [Field K] (G : Type v) [Group G] :
    Conj K G → Luck.LuckApproximation K G := (equiv K G).mp

/-! ## The non-strict reading -/

section Weak

variable {K : Type u} [Field K] {G : Type v} [Group G]

/-- Non-strict chains `G ≥ G₁ ≥ G₂ ≥ ⋯`. -/
structure WeakChain (G : Type v) [Group G] where
  N : ℕ → Subgroup G
  normal : ∀ i, (N i).Normal
  finiteIndex : ∀ i, (N i).FiniteIndex
  anti : Antitone N
  iInf_eq_bot : ⨅ i, N i = ⊥

noncomputable def WeakChain.rkSeq (K : Type u) [Field K] (c : WeakChain G) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : ℕ → ℝ :=
  fun i => haveI := c.normal i; haveI := c.finiteIndex i; Luck.rk K (c.N i) A

/-- Conjecture 1.2 (1)+(2) with non-strict chains. -/
def ConjWeak (K : Type u) [Field K] (G : Type v) [Group G] : Prop :=
  ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)),
    (∀ c : WeakChain G, ∃ L : ℝ, Tendsto (c.rkSeq K A) atTop (𝓝 L)) ∧
    (∀ (c c' : WeakChain G) (L L' : ℝ),
      Tendsto (c.rkSeq K A) atTop (𝓝 L) → Tendsto (c'.rkSeq K A) atTop (𝓝 L') → L = L')

def ofStrict (c : Luck.Chain G) : WeakChain G :=
  ⟨c.N, c.normal, c.finiteIndex, c.strictAnti.antitone, c.iInf_eq_bot⟩

theorem nonStrict_imp_luck (K : Type u) [Field K] (G : Type v) [Group G] :
    ConjWeak K G → Luck.LuckApproximation K G := fun h =>
  ⟨fun n m A c => (h n m A).1 (ofStrict c),
   fun n m A c₁ c₂ l₁ l₂ h₁ h₂ => (h n m A).2 (ofStrict c₁) (ofStrict c₂) l₁ l₂ h₁ h₂⟩

end Weak

end Luck.Literal
