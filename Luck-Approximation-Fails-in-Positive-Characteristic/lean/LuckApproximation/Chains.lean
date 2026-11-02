import LuckApproximation.Sanity
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Subchains, and a criterion for the failure of part (2)

* `Chain.comp`: a subsequence of a chain is a chain.
* `not_chainIndependence_of_frequently`: if one chain converges to `l` and the ranks along another chain are
  `≤ l − ε` infinitely often, part (2) alone fails. A subchain of the second converges, by Bolzano–Weierstrass
  (ranks lie in `[0, n]`), to a limit `≤ l − ε`. So the two limits both exist and differ.
* `not_chainIndependence_of_full` (**the criterion**): for a square matrix, a full-rank limit along one chain and
  a normalised kernel (`Chain.kerSeq`) not tending to 0 along another chain.
-/

namespace Luck

open Filter Topology

universe u v

/-- A subsequence of a chain is a chain. -/
def Chain.comp {G : Type v} [Group G] (c : Chain G) (φ : ℕ → ℕ) (hφ : StrictMono φ) : Chain G where
  N i := c.N (φ i)
  normal i := c.normal (φ i)
  finiteIndex i := c.finiteIndex (φ i)
  strictAnti := c.strictAnti.comp_strictMono hφ
  iInf_eq_bot := by
    refine eq_bot_iff.2 ((le_iInf fun i => (iInf_le _ i).trans ?_).trans c.iInf_eq_bot.le)
    exact c.strictAnti.antitone (hφ.id_le i)

theorem Chain.rkSeq_nonneg {K : Type u} [Field K] {G : Type v} [Group G] (c : Chain G) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) (i : ℕ) : 0 ≤ c.rkSeq K A i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem Chain.rkSeq_le {K : Type u} [Field K] {G : Type v} [Group G] (c : Chain G) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) (i : ℕ) : c.rkSeq K A i ≤ n := by
  have := c.normal i
  have := c.finiteIndex i
  exact rk_le K (c.N i) A

/-- **Part (2) alone fails** as soon as one chain converges to `l` and the ranks along another chain
are `≤ l − ε` infinitely often. -/
theorem not_chainIndependence_of_frequently {K : Type u} [Field K] {G : Type v} [Group G] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) (c₁ c₂ : Chain G) {l ε : ℝ} (hε : 0 < ε)
    (h₁ : Tendsto (c₁.rkSeq K A) atTop (𝓝 l)) (h₂ : ∃ᶠ i in atTop, c₂.rkSeq K A i ≤ l - ε) :
    ¬ ChainIndependence K G := by
  intro hind
  obtain ⟨ψ, hψ, hψle⟩ := extraction_of_frequently_atTop h₂
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) n)
    (x := c₂.rkSeq K A ∘ ψ) fun i => ⟨c₂.rkSeq_nonneg A _, c₂.rkSeq_le A _⟩
  have ha : a ≤ l - ε := le_of_tendsto' hlim fun i => hψle (φ i)
  have := hind n m A c₁ (c₂.comp (ψ ∘ φ) (hψ.comp hφ)) l a h₁ hlim
  linarith

/-- The normalised kernel dimension of a square matrix along a chain. -/
noncomputable def Chain.kerSeq {K : Type u} [Field K] {G : Type v} [Group G] (c : Chain G) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra K G)) (i : ℕ) : ℝ :=
  haveI := c.normal i
  haveI := c.finiteIndex i
  (Module.finrank K (LinearMap.ker (phi K (c.N i) A)) : ℝ) / (c.N i).index

theorem Chain.kerSeq_nonneg {K : Type u} [Field K] {G : Type v} [Group G] (c : Chain G) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra K G)) (i : ℕ) : 0 ≤ c.kerSeq A i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem Chain.rkSeq_eq_sub {K : Type u} [Field K] {G : Type v} [Group G] (c : Chain G) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra K G)) (i : ℕ) : c.rkSeq K A i = n - c.kerSeq A i := by
  have := c.normal i
  have := c.finiteIndex i
  exact rk_eq_sub K (c.N i) A

/-- **The criterion**: if the ranks of a square matrix tend to `n` (full rank) along one chain and its
normalised kernel does not tend to 0 along another chain, part (2) fails. -/
theorem not_chainIndependence_of_full {K : Type u} [Field K] {G : Type v} [Group G] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra K G)) (c₁ c₂ : Chain G)
    (h₁ : Tendsto (c₁.rkSeq K A) atTop (𝓝 n)) (h₂ : ¬ Tendsto (c₂.kerSeq A) atTop (𝓝 0)) :
    ¬ ChainIndependence K G := by
  have hfreq : ∃ ε > 0, ∃ᶠ i in atTop, c₂.rkSeq K A i ≤ n - ε := by
    by_contra hne
    push Not at hne
    apply h₂
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun i => ha.trans_le (c₂.kerSeq_nonneg A i),
      fun a ha => ?_⟩
    filter_upwards [hne a ha] with i hi
    rw [Chain.rkSeq_eq_sub] at hi
    linarith
  obtain ⟨ε, hε, hf⟩ := hfreq
  exact not_chainIndependence_of_frequently A c₁ c₂ hε h₁ hf

end Luck
