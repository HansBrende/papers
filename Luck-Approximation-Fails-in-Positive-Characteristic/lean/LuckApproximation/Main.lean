import LuckApproximation.CyclicTower
import LuckApproximation.PChain
import LuckApproximation.Monotone
import LuckApproximation.Hypothesis
import LuckApproximation.Chains
import LuckApproximation.BaseChange
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Main theorem: chain-independence fails over every field of characteristic 3

For `F = FreeGroup (Fin 89)` and every field `K` of characteristic 3, part (2) of the conjecture fails outright:
two chains along which the ranks of one matrix converge, to different limits. The only hypothesis is
`KernelNotNegligible` (`Hypothesis.lean`): along some chain the normalised kernel of `opA` over `𝔽₃` does not
tend to 0. The paper proves it, with density `≥ 20` at every level of the λ₀-adic chain. Standard axioms only.

* **3-chain side** (`tendsto_full_of_cofinal`). On every cyclic `3^j` cover the kernel is at most 42
  (`finrank_ker_Ncyc_le`, from the kernel-checked certificate), so `rk ≥ 110 − 42/3^j`. By the
  monotonicity (`rk_le_rk_of_isPGroup`), **every** chain with 3-group quotients that passes below each cyclic
  level has ranks squeezed between `110 − 42/3^j` and `110`, so they tend to 110. Such chains exist
  (`exists_pChain_le`).
* **Hypothesis side.** The kernel only grows when the coefficients are mapped to `K` (`finrank_ker_le_map`), so
  the normalised kernel over `K` does not tend to 0 either (`kerDensity_le`).
* **Criterion.** `not_chainIndependence_of_full` (`Chains.lean`, any field, group and square matrix) concludes.
-/

namespace Luck.Op

open Filter Topology

section Field

variable (K : Type*) [Field K] [CharP K 3]

/-- **Every** chain with 3-group quotients that passes below each cyclic level `Ncyc j` (in particular every
chain cofinal in the pro-3 topology) has limit 110, the full rank. -/
theorem tendsto_full_of_cofinal (c : Chain F)
    (hp : ∀ i, haveI := c.normal i; IsPGroup 3 (F ⧸ c.N i))
    (hcof : ∀ j, ∃ i, c.N i ≤ Ncyc j) :
    Tendsto (c.rkSeq K (opK K)) atTop (𝓝 110) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun i =>
    (by exact_mod_cast c.rkSeq_le (opK K) i : c.rkSeq K (opK K) i ≤ 110).trans_lt ha⟩
  have h0 : Tendsto (fun j : ℕ => (42 : ℝ) / 3 ^ j) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (1 / 3 : ℝ) < 1)).const_mul 42
    simpa [div_eq_mul_inv, one_div, inv_pow] using this
  obtain ⟨j, hj⟩ := (h0.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 110 - a))).exists
  obtain ⟨i₀, hi₀⟩ := hcof j
  filter_upwards [eventually_ge_atTop i₀] with i hi
  have := c.normal i
  have := c.finiteIndex i
  have hle : c.N i ≤ Ncyc j := (c.strictAnti.antitone hi).trans hi₀
  have h := (rk_Ncyc K j).trans (rk_le_rk_of_isPGroup 3 (Ncyc j) (c.N i) hle (hp i) (opK K))
  change a < rk K (c.N i) (opK K)
  linarith

/-- Such a chain exists: a chain with 3-group quotients below every cyclic level, along which the ranks tend to
110. -/
theorem exists_chain_tendsto_full : ∃ c : Chain F, (∀ i, haveI := c.normal i; IsPGroup 3 (F ⧸ c.N i)) ∧
    (∀ j, c.N j ≤ Ncyc j) ∧ Tendsto (c.rkSeq K (opK K)) atTop (𝓝 110) := by
  obtain ⟨c, hp, hle⟩ := exists_pChain_le 3 89 (by norm_num) Ncyc isPGroup_Ncyc
  exact ⟨c, hp, hle, tendsto_full_of_cofinal K c hp fun j => ⟨j, hle j⟩⟩

/-- The normalised kernel over `K` is at least the one over `𝔽₃`. -/
theorem kerDensity_le (c : Chain F) (i : ℕ) : kerDensity c i ≤ c.kerSeq (opK K) i := by
  let := ZMod.algebra K 3
  have := c.normal i
  have := c.finiteIndex i
  have h : Module.finrank (ZMod 3) (LinearMap.ker (phi (ZMod 3) (c.N i) opA)) ≤
      Module.finrank K (LinearMap.ker (phi K (c.N i) (opK K))) := finrank_ker_le_map (c.N i) opA
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg _)

/-- **Main theorem**: under the weakest hypothesis, part (2) fails over every field of characteristic 3: two
chains along which the ranks of `opK K` converge, to 110 and to a limit `< 110`. -/
theorem chainIndependence_fails (h : KernelNotNegligible) : ¬ ChainIndependence K F := by
  obtain ⟨c₁, -, -, h₁⟩ := exists_chain_tendsto_full K
  obtain ⟨c, hc⟩ := h
  exact not_chainIndependence_of_full (opK K) c₁ c (by exact_mod_cast h₁) fun hK =>
    hc (squeeze_zero (kerDensity_nonneg c) (kerDensity_le K c) hK)

end Field

/-- The strengthened target: for one free group of finite rank, part (2) fails over every field of
characteristic 3, with both limits existing. -/
def CharThreeChainTarget : Prop :=
  ∃ r : ℕ, ∀ (K : Type) [Field K] [CharP K 3], ¬ ChainIndependence K (FreeGroup (Fin r))

theorem charThreeChainTarget (h : KernelNotNegligible) : CharThreeChainTarget :=
  ⟨89, fun K _ _ => chainIndependence_fails K h⟩

/-- Parts (1) and (2) do not both hold for `F` over `𝔽₃`. -/
theorem luckApproximation_fails (h : KernelNotNegligible) : ¬ LuckApproximation (ZMod 3) F :=
  fun hL => chainIndependence_fails (ZMod 3) h hL.2

/-- The target `MainTheoremTarget` of `Statement.lean` follows. -/
theorem mainTheorem (h : KernelNotNegligible) : MainTheoremTarget :=
  ⟨89, luckApproximation_fails h⟩

theorem conjecture_false (h : KernelNotNegligible) : ¬ LuckApproximationConjecture :=
  not_conjecture_of_target (mainTheorem h)

/-- With the paper's form of the hypothesis. -/
theorem charThreeChainTarget_of_density (h : KernelDensityHypothesis) : CharThreeChainTarget :=
  charThreeChainTarget (kernelNotNegligible_of_density h)

/-- A chain cofinal in the pro-3 topology: every normal subgroup of 3-power index contains a term. -/
def ProThreeCofinal (c : Chain F) : Prop :=
  ∀ (M : Subgroup F) [M.Normal], M.FiniteIndex → IsPGroup 3 (F ⧸ M) → ∃ i, c.N i ≤ M

/-- Every pro-3-cofinal chain with 3-group quotients has limit 110, over every field of characteristic 3. -/
theorem tendsto_full_of_proThreeCofinal (K : Type*) [Field K] [CharP K 3] (c : Chain F)
    (hp : ∀ i, haveI := c.normal i; IsPGroup 3 (F ⧸ c.N i)) (hc : ProThreeCofinal c) :
    Tendsto (c.rkSeq K (opK K)) atTop (𝓝 110) :=
  tendsto_full_of_cofinal K c hp fun j => hc (Ncyc j) inferInstance (isPGroup_Ncyc j)

/-- **Unconditional form of the main theorem.** If chain-independence held over some field of characteristic 3,
the normalised kernel of `opA` over `𝔽₃` would tend to 0 along every chain. The paper shows that it does not
along the λ₀-adic chain (density `≥ 20` at every level). -/
theorem kernel_density_tendsto_zero (K : Type*) [Field K] [CharP K 3] (hK : ChainIndependence K F)
    (c : Chain F) : Tendsto (kerDensity c) atTop (𝓝 0) := by
  by_contra hc
  exact chainIndependence_fails K ⟨c, hc⟩ hK

/-- The same with the conjecture's parts (1) and (2) over `𝔽₃`. -/
theorem kernel_density_tendsto_zero_of_luck (hL : LuckApproximation (ZMod 3) F) (c : Chain F) :
    Tendsto (kerDensity c) atTop (𝓝 0) :=
  kernel_density_tendsto_zero (ZMod 3) hL.2 c

end Luck.Op
