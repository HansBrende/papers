import LuckApproximation.Operator
import LuckApproximation.Chains

/-!
# The hypothesis of the main theorem (proved in the paper, not in Lean)

* `KernelNotNegligible`, the hypothesis of the main theorem: along some chain of `F = π₁(X₀)` the normalised
  kernel `kerDensity c i = dim_𝔽₃ ker φ_{F/c.N i}(opA) / |F : c.N i|` does not tend to 0. This is the weakest
  possible hypothesis for this operator: along a pro-3-cofinal 3-chain the normalised rank of `opA` tends to the
  full rank 110 (`Main.lean`), so the hypothesis holds exactly when along some chain the ranks of `opA`
  do not tend to 110.
* `KernelDensityHypothesis`, the form proved in the paper: some chain and some `ε > 0` with
  `ε · |F : Fᵢ| ≤ dim_𝔽₃ ker φ_{F/Fᵢ}(opA)` for every `i`. It implies `KernelNotNegligible`
  (`kernelNotNegligible_of_density`).

Theorem H of the paper proves `KernelDensityHypothesis` with `ε = 20` along the λ₀-adic congruence chain,
by Riemann–Roch on the Goren–Oort divisor of a Hilbert modular surface in characteristic 3. That proof is not
formalised. `tools/lambda_level1.py` computes the kernel exactly at the first nested level of the chain.
-/

namespace Luck.Op

/-- **The hypothesis** (proved in the paper, not in Lean): some chain of `F` along which the kernel of
`opA` has positive density. -/
def KernelDensityHypothesis : Prop :=
  ∃ (c : Chain F) (ε : ℝ), 0 < ε ∧ ∀ i,
    haveI := c.normal i
    haveI := c.finiteIndex i
    ε * ((c.N i).index : ℝ) ≤
      (Module.finrank (ZMod 3) (LinearMap.ker (phi (ZMod 3) (c.N i) opA)) : ℝ)

/-- The normalised kernel dimension of `opA` over `𝔽₃` at level `i` of a chain. -/
noncomputable def kerDensity (c : Chain F) (i : ℕ) : ℝ := c.kerSeq opA i

theorem kerDensity_nonneg (c : Chain F) (i : ℕ) : 0 ≤ kerDensity c i := c.kerSeq_nonneg opA i

/-- **The weakest hypothesis**: along some chain the normalised kernel of `opA` does not tend to 0. This is
equivalent to density at least some `ε > 0` at infinitely many levels, and to the ranks not tending to
110; the main theorem uses only this. -/
def KernelNotNegligible : Prop :=
  ∃ c : Chain F, ¬ Filter.Tendsto (kerDensity c) Filter.atTop (nhds 0)

/-- The paper's form (density `≥ ε` at every level) implies the weakest form. -/
theorem kernelNotNegligible_of_density (h : KernelDensityHypothesis) : KernelNotNegligible := by
  obtain ⟨c, ε, hε, hk⟩ := h
  refine ⟨c, fun ht => ?_⟩
  have hge : ∀ i, ε ≤ kerDensity c i := by
    intro i
    have := c.normal i
    have := c.finiteIndex i
    have hidx : (0 : ℝ) < (c.N i).index := by
      exact_mod_cast Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    rw [kerDensity, Chain.kerSeq, le_div_iff₀ hidx]
    exact hk i
  have := ge_of_tendsto' ht hge
  linarith

end Luck.Op
