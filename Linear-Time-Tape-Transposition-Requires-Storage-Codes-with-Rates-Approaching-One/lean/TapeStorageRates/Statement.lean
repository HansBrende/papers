import AboveHalfRate.Main
import MergeDepth.Traces
import Transpose.Eventually
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Storage-code targets for linear-time transposition

`QuantitativeTarget` and `QualitativeTarget` are the statements of the paper's transfers.
The complete packet construction in the main module proves the quantitative target. The implication
`qualitative_of_quantitative` is proved below.
-/

namespace TapeStorageRates

open Filter DirectedRecovery MotionDepthCodes
open scoped Topology

set_option autoImplicit false

open Classical in
/-- A family at a fixed incidence degree cap. Its positive lengths tend to infinity. At each
fixed radius, eventually every coordinate has its two ports farther apart than that radius.
The extended graph distance assigns infinite distance to disconnected ports. -/
structure SeparatedBinaryFamily (Δ : ℕ) where
  length : ℕ → ℕ
  length_pos : ∀ i, 0 < length i
  length_tendsto : Tendsto length atTop atTop
  recovery : (i : ℕ) → Fin (length i) → Finset (Fin (length i))
  code : (i : ℕ) → Finset (Fin (length i) → Bool)
  nonempty : ∀ i, (code i).Nonempty
  storage : ∀ i, IsStorageCode (recovery i) (code i)
  degree_le : ∀ i v, (pairedIncidenceGraph (recovery i)).degree v ≤ Δ
  paired_far : ∀ r : ℕ, ∀ᶠ i in atTop, ∀ q : Fin (length i),
    ¬ (pairedIncidenceGraph (recovery i)).edist (Sum.inl q) (Sum.inr q) ≤ r

/-- Growing minimum paired distance implies Paper 5's vanishing fraction of short pairs. -/
theorem SeparatedBinaryFamily.hasPairedDistanceSeparation {Δ : ℕ} (F : SeparatedBinaryFamily Δ) :
    HasPairedDistanceSeparation F.recovery :=
  AboveHalf.hasPairedDistanceSeparation_of_eventually F.recovery (fun r _ => F.paired_far r)

/-- The deficit scale with `k` work tapes, written in base two. It is used at large `Δ`. -/
noncomputable def deficitScale (k Δ : ℕ) : ℝ :=
  let y := Real.logb 2 (Real.logb 2 (Δ : ℝ))
  (Real.logb 2 y / y) ^ (1 / (4 * (k : ℝ) ^ 2 + 1) : ℝ)

/-- The deficit scale tends to zero at every fixed tape count. -/
theorem tendsto_deficitScale (k : ℕ) : Tendsto (deficitScale k) atTop (𝓝 0) := by
  have hlog : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hratio : Tendsto (fun y : ℝ => Real.logb 2 y / y) atTop (𝓝 0) :=
    (Real.isLittleO_logb_id_atTop (b := 2)).tendsto_div_nhds_zero
  exact (hratio.comp (hlog.comp (hlog.comp tendsto_natCast_atTop_atTop))).rpow_const_nhds_zero
    (by positivity : 0 < (1 / (4 * (k : ℝ) ^ 2 + 1) : ℝ))

/-- The rate and separation conclusion at every sufficiently large incidence-degree cap.
The machine-dependent constant is independent of both the cap and the family index. -/
def RateWitnesses (k : ℕ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ᶠ Δ : ℕ in atTop, ∃ F : SeparatedBinaryFamily Δ,
    1 - K * deficitScale k Δ ≤ liminf (fun i => storageCodeRate (F.code i)) atTop

/-- **Quantitative machine-to-code transfer.** A fixed native machine succeeds on every
input at arbitrarily large canonical dimensions within `c (L + 1)` steps. The constant `K` is
chosen before the integer degree cap. At every sufficiently large cap there is a family attaining
the stated lower bound on its limiting lower rate. `max 1 M.k` includes the zero-tape case with
the exponent obtained by adjoining one unused tape. -/
def QuantitativeTarget : Prop :=
  ∀ (M : Transpose.TM) (c : ℝ), 0 < c →
    (∀ d₀ : ℕ, ∃ d ≥ d₀, MergeDepth.TransposesAt M d c) →
    RateWitnesses (max 1 M.k)

/-- **Qualitative machine-to-code transfer.** Under Paper 1's frozen (T), every positive
rate loss can be achieved by a separated binary family at each sufficiently large degree cap. -/
def QualitativeTarget : Prop :=
  Transpose.LinearTimeTransposable → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ Δ : ℕ in atTop, ∃ F : SeparatedBinaryFamily Δ,
      1 - ε ≤ liminf (fun i => storageCodeRate (F.code i)) atTop

/-- Passing from the frozen all-size problem to a positive real time coefficient and unbounded
canonical successes. This same witness is used for every conditional exclusion. -/
theorem unbounded_success_of_linear (h : Transpose.LinearTimeTransposable) :
    ∃ (M : Transpose.TM) (c : ℝ), 0 < c ∧ ∀ d₀ : ℕ, ∃ d ≥ d₀, MergeDepth.TransposesAt M d c := by
  obtain ⟨M, c, hM⟩ := h
  have hM' : Transpose.TransposesWithin M (fun L => (c + 1) * (L + 1)) := by
    intro d hd A
    exact (hM d hd A).mono (Nat.mul_le_mul_right _ (Nat.le_succ c))
  refine ⟨M, (c + 1 : ℕ), by positivity, ?_⟩
  exact fun d₀ => ⟨d₀+1, Nat.le_succ _, MergeDepth.transposesAt_of_transposesWithin hM' (Nat.succ_pos _)⟩

/-- The quantitative transfer implies the qualitative transfer for Paper 1's exact (T). -/
theorem qualitative_of_quantitative (hquant : QuantitativeTarget) : QualitativeTarget := by
  intro h ε hε
  obtain ⟨M, c, hc, hgood⟩ := unbounded_success_of_linear h
  obtain ⟨K, _, hK⟩ := hquant M c hc hgood
  have ht : Tendsto (fun Δ => K * deficitScale (max 1 M.k) Δ) atTop (𝓝 0) := by
    simpa using (tendsto_deficitScale (max 1 M.k)).const_mul K
  filter_upwards [hK, ht.eventually_lt_const hε] with Δ hF hδ
  obtain ⟨F, hF⟩ := hF
  exact ⟨F, (sub_le_sub_left hδ.le 1).trans hF⟩

end TapeStorageRates
