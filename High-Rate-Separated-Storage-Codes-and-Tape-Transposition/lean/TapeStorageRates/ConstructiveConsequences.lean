import TapeStorageRates.MajorityFamily
import TapeStorageRates.RateGap

/-! # Consequences for unrestricted storage-code rate gaps

The construction supplies the paper's rate witnesses independently of a
tape machine, conditional on the explicitly stated above-half linear seed.
Consequently unrestricted family-rate gaps cannot meet the slow-gap
criteria. No converse from abstract codes to a native computation is used.
-/

namespace TapeStorageRates

open Filter DirectedRecovery
open scoped Topology

set_option autoImplicit false
noncomputable section

/-- Polynomially small rate loss at every sufficiently large fixed cap.
Both constants precede the degree cap and the growing family index. -/
def PolynomialRateWitnesses : Prop :=
  ∃ K α : ℝ, 0 < K ∧ 0 < α ∧ ∀ᶠ Δ : ℕ in atTop,
    ∃ F : SeparatedBinaryFamily Δ,
      1 - K * (Δ : ℝ) ^ (-α) ≤ liminf (fun i => storageCodeRate (F.code i)) atTop

/-- An unrestricted upper rate gap cannot exceed the loss of these actual
families. This comparison does not assume any transposition algorithm. -/
theorem PolynomialRateWitnesses.uniform_gap_bound (h : PolynomialRateWitnesses) :
    ∃ K α : ℝ, 0 < K ∧ 0 < α ∧ ∀ g : ℕ → ℝ, FamilyRateGap g →
      ∀ᶠ Δ : ℕ in atTop, g Δ ≤ K * (Δ : ℝ) ^ (-α) := by
  obtain ⟨K, α, hK, hα, hfamilies⟩ := h
  refine ⟨K, α, hK, hα, fun g hg => ?_⟩
  filter_upwards [hg, hfamilies] with Δ ⟨_, hupper⟩ ⟨F, hF⟩
  have hlim := F.liminf_le_limsup.trans (hupper F)
  linarith

/-- The fixed-gap specialization of the bound uniform over all gaps. -/
theorem PolynomialRateWitnesses.eventually_gap_le (h : PolynomialRateWitnesses)
    {g : ℕ → ℝ} (hg : FamilyRateGap g) :
    ∃ K α : ℝ, 0 < K ∧ 0 < α ∧ ∀ᶠ Δ : ℕ in atTop,
      g Δ ≤ K * (Δ : ℝ) ^ (-α) := by
  obtain ⟨K, α, hK, hα, hbound⟩ := h.uniform_gap_bound
  exact ⟨K, α, hK, hα, hbound g hg⟩

/-- A degree inverse power dominates even the double-log factor needed
to compare with the paper's slow quantitative scale. -/
theorem polynomial_mul_loglog_tendsto_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (fun Δ : ℕ => (Δ : ℝ) ^ (-α) * degreeLogLog Δ) atTop (𝓝 0) := by
  have hlog : Tendsto (fun Δ : ℕ => Real.logb 2 (Δ : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h₁ := (Real.isLittleO_logb_id_atTop (b := 2)).tendsto_div_nhds_zero.comp hlog
  have h₂ := (logb_div_power hα).comp tendsto_natCast_atTop_atTop
  have h := h₁.mul h₂
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with Δ hΔ
  change (degreeLogLog Δ / Real.logb 2 (Δ : ℝ)) *
    (Real.logb 2 (Δ : ℝ) / (Δ : ℝ) ^ α) = _
  rw [div_mul_div_cancel₀ hΔ.ne', Real.rpow_neg (Nat.cast_nonneg _) α,
    div_eq_mul_inv, mul_comm]

/-- Polynomial-rate families satisfy every fixed-tape quantitative witness
condition. This is a statement about abstract codes, not tape realization. -/
theorem PolynomialRateWitnesses.rate_witnesses (h : PolynomialRateWitnesses) (k : ℕ) :
    RateWitnesses k := by
  suffices hzero : RateWitnesses 0 from hzero.mono (Nat.zero_le k)
  obtain ⟨K, α, hK, hα, hfamilies⟩ := h
  refine ⟨K, hK, ?_⟩
  filter_upwards [hfamilies,
    (polynomial_mul_loglog_tendsto_zero hα).eventually_lt_const zero_lt_one,
    tendsto_degreeLogLog.eventually_ge_atTop 2] with Δ ⟨F, hF⟩ hsmall hy
  have hypos : 0 < degreeLogLog Δ := by linarith
  have hlog : 1 ≤ Real.logb 2 (degreeLogLog Δ) := by
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num) hy
  have hscale : (Δ : ℝ) ^ (-α) ≤ deficitScale 0 Δ := by
    have hdiv := (le_div_iff₀ hypos).mpr hsmall.le
    have hratio : 1 / degreeLogLog Δ ≤ Real.logb 2 (degreeLogLog Δ) / degreeLogLog Δ :=
      div_le_div_of_nonneg_right hlog hypos.le
    simpa [deficitScale, degreeLogLog] using hdiv.trans hratio
  exact ⟨F, (sub_le_sub_left (mul_le_mul_of_nonneg_left hscale hK.le) 1).trans hF⟩

/-- The unrestricted unbounded-ratio premise is incompatible with the
constructed abstract rate witnesses, for every fixed tape count. -/
theorem PolynomialRateWitnesses.not_unbounded_ratio (h : PolynomialRateWitnesses)
    {g : ℕ → ℝ} (hg : FamilyRateGap g) (k : ℕ) :
    ¬ (∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < g Δ / deficitScale k Δ) := by
  intro hu
  exact hg.no_witnesses hu (h.rate_witnesses k)

/-- The all-positive-powers premise of the original unrestricted gap
criterion is likewise impossible for these families. -/
theorem PolynomialRateWitnesses.not_all_powers (h : PolynomialRateWitnesses)
    {g : ℕ → ℝ} (hg : FamilyRateGap g) :
    ¬ (∀ a : ℝ, 0 < a → ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop,
      K < g Δ * degreeLogLog Δ ^ a) := by
  intro hp
  apply h.not_unbounded_ratio hg 0
  intro K
  have hpow := hp (1 / 2) (by norm_num) K
  have hinv : ∀ᶠ Δ : ℕ in atTop,
      degreeLogLog Δ ^ (1 / 2 : ℝ) ≤ 1 / deficitScale 0 Δ := by
    simpa using eventually_power_le_inv_scale 0
  refine ((hpow.and_eventually hinv).and_eventually hg).mono ?_
  rintro Δ ⟨⟨hlarge, hbound⟩, hnonneg, _⟩
  exact hlarge.trans_le (by simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left hbound hnonneg)

namespace OddGirthLinearSeed

variable {K : Type} [Field K] [Fintype K] {D : ℕ} {ρ : ℝ}
variable (S : OddGirthLinearSeed K D ρ)

include S

/-- The generic polynomial predicate is instantiated by the actual
majority-matrix syndrome fibres, with only the explicit seed as input. -/
theorem polynomial_rate_witnesses (h2 : (2 : K) ≠ 0)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) : PolynomialRateWitnesses := by
  let δ := LeanMachine.BinomialTail.decay ρ
  let C := Real.logb 2 (Fintype.card K) * Real.exp (2 * δ)
  let α := δ / Real.log (D + 1 : ℕ)
  have hδ : 0 < δ := LeanMachine.BinomialTail.decay_pos hρ hρ1
  have hlog : 0 < Real.log (D + 1 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (by have := S.degree_pos (by linarith : 0 < ρ); omega : 1 < D + 1)
  have hC : 0 < C := by
    apply mul_pos
    · exact Real.logb_pos (by norm_num) (by exact_mod_cast Fintype.one_lt_card (α := K))
    · exact Real.exp_pos _
  refine ⟨C, α, hC, div_pos hδ hlog, ?_⟩
  filter_upwards [eventually_ge_atTop (D + 1)] with Δ hΔ
  obtain ⟨F, hF⟩ := S.exists_family_at_cap h2 hρ hρ1 hΔ
  refine ⟨F, le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun i =>
    MergeDepth.storageCodeRate_le_one (by simp) (F.code i))) ?_⟩
  apply Eventually.of_forall
  intro i
  simpa only [C, α, δ, neg_div] using hF i

/-- One pair of positive constants works for every unrestricted family-rate
gap. The constants are chosen before the candidate gap and the degree cap. -/
theorem uniform_familyRateGap_bound (h2 : (2 : K) ≠ 0)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ g : ℕ → ℝ, FamilyRateGap g →
      ∀ᶠ Δ : ℕ in atTop, g Δ ≤ C * (Δ : ℝ) ^ (-α) :=
  (S.polynomial_rate_witnesses h2 hρ hρ1).uniform_gap_bound

/-- Conditional on the supplied seed, every unrestricted family-rate gap
is eventually bounded by a negative power of the incidence degree. -/
theorem familyRateGap_bound (h2 : (2 : K) ≠ 0) (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    {g : ℕ → ℝ} (hg : FamilyRateGap g) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ᶠ Δ : ℕ in atTop,
      g Δ ≤ C * (Δ : ℝ) ^ (-α) :=
  (S.polynomial_rate_witnesses h2 hρ hρ1).eventually_gap_le hg

/-- Abstract rate witnesses for every fixed tape count require no machine
assumption once the above-half odd-field seed is supplied. -/
theorem rate_witnesses (h2 : (2 : K) ≠ 0) (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    (k : ℕ) : RateWitnesses k :=
  (S.polynomial_rate_witnesses h2 hρ hρ1).rate_witnesses k

theorem not_unbounded_familyRateGap (h2 : (2 : K) ≠ 0) (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    {g : ℕ → ℝ} (hg : FamilyRateGap g) (k : ℕ) :
    ¬ (∀ C : ℝ, ∃ᶠ Δ : ℕ in atTop, C < g Δ / deficitScale k Δ) :=
  (S.polynomial_rate_witnesses h2 hρ hρ1).not_unbounded_ratio hg k

theorem not_all_powers_familyRateGap (h2 : (2 : K) ≠ 0) (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    {g : ℕ → ℝ} (hg : FamilyRateGap g) :
    ¬ (∀ a : ℝ, 0 < a → ∀ C : ℝ, ∃ᶠ Δ : ℕ in atTop,
      C < g Δ * degreeLogLog Δ ^ a) :=
  (S.polynomial_rate_witnesses h2 hρ hρ1).not_all_powers hg

end OddGirthLinearSeed

end
end TapeStorageRates
