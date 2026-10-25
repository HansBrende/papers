import DirectedRecovery.PathPacking
import DirectedRecovery.Hyperfinite
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative and asymptotic consequences of native path transport

The radius, degree bound, and transport constants are fixed before the size.
The actual native transport theorem remains an explicit hypothesis. Entry
width may vary arbitrarily, subject only to positivity.
-/

namespace DirectedRecovery

open Classical Filter
open scoped BigOperators Topology Asymptotics
set_option autoImplicit false

/-- The exact transport premise used by the finite packing theorem. -/
def HasDisjointPathTransport {V : Type*} [Fintype V] [DecidableEq V]
    (N : V → Finset V) (r : ℕ) (M : ℕ → ℝ) : Prop :=
  ∀ p : ∀ i : shortPairedCoordinates N r,
    (pairedIncidenceGraph N).Walk (Sum.inl i.val) (Sum.inr i.val),
    (∀ i, (p i).IsPath) →
    ∀ s, Odd s → s ≤ r → ∀ J : Finset (shortPairedCoordinates N r),
    (∀ i ∈ J, (p i).length = s) →
    (J : Set (shortPairedCoordinates N r)).PairwiseDisjoint
      (fun i => (p i).support.toFinset) → (J.card : ℝ) ≤ M s

/-- The finite constant after the common `L/log₂ d` factor is removed. -/
def pathPackingConstant (r Δ : ℕ) (A : ℕ → ℝ) : ℝ :=
  ∑ s ∈ (Finset.range (r + 1)).filter Odd,
    ((s + 1 : ℕ) : ℝ) *
      (∑ j ∈ Finset.range (r + 1), (max 1 Δ) ^ j : ℕ) * A s

theorem pathPackingConstant_nonneg (r Δ : ℕ) (A : ℕ → ℝ)
    (hA : ∀ s, 0 ≤ A s) : 0 ≤ pathPackingConstant r Δ A := by
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (by positivity) (hA s)

/-- The exact finite `C L/log₂ d` estimate on the actual incidence graph. -/
theorem short_paired_count_log_bound {V : Type*} [Fintype V] [DecidableEq V]
    (N : V → Finset V) (r Δ d b : ℕ) (A : ℕ → ℝ)
    (hdegree : ∀ v, (pairedIncidenceGraph N).degree v ≤ Δ)
    (htransport : HasDisjointPathTransport N r
      (fun s => A s * ((d : ℝ) ^ 2 * b) / Real.logb 2 d)) :
    ((shortPairedCoordinates N r).card : ℝ) ≤ pathPackingConstant r Δ A *
      (((d : ℝ) ^ 2 * b) / Real.logb 2 d) := by
  have h := short_paired_count_of_disjoint_transport N r Δ hdegree
    (fun s => A s * ((d : ℝ) ^ 2 * b) / Real.logb 2 d) htransport
  refine h.trans_eq ?_
  unfold pathPackingConstant
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- A fixed log-transport constant gives a genuine big-O estimate and
vanishing short-pair density, with arbitrary positive entry widths. -/
theorem short_paired_count_log_asymptotics
    {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (N : ∀ n, V n → Finset (V n)) (r Δ : ℕ) (A : ℕ → ℝ)
    (hA : ∀ s, 0 ≤ A s) (d b : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) (hb : ∀ n, 1 ≤ b n)
    (hdegree : ∀ᶠ n in atTop, ∀ v, (pairedIncidenceGraph (N n)).degree v ≤ Δ)
    (htransport : ∀ᶠ n in atTop, HasDisjointPathTransport (N n) r
      (fun s => A s * ((d n : ℝ) ^ 2 * b n) / Real.logb 2 (d n))) :
    (fun n => ((shortPairedCoordinates (N n) r).card : ℝ)) =O[atTop]
      (fun n => ((d n : ℝ) ^ 2 * b n) / Real.logb 2 (d n)) ∧
    Tendsto (fun n => ((shortPairedCoordinates (N n) r).card : ℝ) /
      ((d n : ℝ) ^ 2 * b n)) atTop (𝓝 0) := by
  let C := pathPackingConstant r Δ A
  have hC : 0 ≤ C := pathPackingConstant_nonneg r Δ A hA
  have hbound : ∀ᶠ n in atTop,
      ((shortPairedCoordinates (N n) r).card : ℝ) ≤
        C * (((d n : ℝ) ^ 2 * b n) / Real.logb 2 (d n)) := by
    filter_upwards [hdegree, htransport] with n hn ht
    exact short_paired_count_log_bound (N n) r Δ (d n) (b n) A hn ht
  have hlog : Tendsto (fun n => Real.logb 2 (d n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_natCast_atTop_atTop.comp hd)
  have hlim : Tendsto (fun n => C / Real.logb 2 (d n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨C, ?_⟩
    filter_upwards [hbound, hd.eventually (eventually_ge_atTop 2)] with n hn hn2
    have hlog0 : 0 < Real.logb 2 (d n : ℝ) := Real.logb_pos (by norm_num)
      (by exact_mod_cast (by omega : 1 < d n))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤
        (shortPairedCoordinates (N n) r).card from Nat.cast_nonneg _),
      abs_of_nonneg (by positivity : 0 ≤ ((d n : ℝ) ^ 2 * b n) /
        Real.logb 2 (d n))] using hn
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · exact Eventually.of_forall (fun n => by positivity)
    · filter_upwards [hbound, hd.eventually (eventually_ge_atTop 1)] with n hn hn1
      have hvol : 0 < (d n : ℝ) ^ 2 * b n := by
        have hd0 : (0 : ℝ) < d n := by exact_mod_cast (by omega : 0 < d n)
        have hb0 : (0 : ℝ) < b n := by exact_mod_cast (by have := hb n; omega : 0 < b n)
        positivity
      apply (div_le_iff₀ hvol).mpr
      convert hn using 1
      ring

/-- If the coordinate count is the matrix volume, the limiting density is
the prescribed-pair fraction itself, with disconnected pairs excluded by
the finite theorem's extended-distance convention. -/
theorem short_paired_fraction_tendsto_zero
    {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (N : ∀ n, V n → Finset (V n)) (r Δ : ℕ) (A : ℕ → ℝ)
    (hA : ∀ s, 0 ≤ A s) (d b : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) (hb : ∀ n, 1 ≤ b n)
    (hcard : ∀ n, Fintype.card (V n) = d n ^ 2 * b n)
    (hdegree : ∀ᶠ n in atTop, ∀ v, (pairedIncidenceGraph (N n)).degree v ≤ Δ)
    (htransport : ∀ᶠ n in atTop, HasDisjointPathTransport (N n) r
      (fun s => A s * ((d n : ℝ) ^ 2 * b n) / Real.logb 2 (d n))) :
    Tendsto (fun n => ((shortPairedCoordinates (N n) r).card : ℝ) /
      Fintype.card (V n)) atTop (𝓝 0) := by
  simpa only [hcard, Nat.cast_mul, Nat.cast_pow] using
    (short_paired_count_log_asymptotics N r Δ A hA d b hd hb hdegree htransport).2

/-- Radius-by-radius transport estimates supply exactly the paired-distance
separation condition consumed by the hyperfinite coding theorem. Constants
may depend on the fixed radius, but are chosen before the size index. -/
theorem path_transport_implies_paired_distance_separation
    {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (N : ∀ n, V n → Finset (V n)) (d b : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) (hb : ∀ n, 1 ≤ b n)
    (hcard : ∀ n, Fintype.card (V n) = d n ^ 2 * b n)
    (htransport : ∀ r : ℕ, 0 < r → ∃ (Δ : ℕ) (A : ℕ → ℝ),
      (∀ s, 0 ≤ A s) ∧
      (∀ᶠ n in atTop, ∀ v, (pairedIncidenceGraph (N n)).degree v ≤ Δ) ∧
      ∀ᶠ n in atTop, HasDisjointPathTransport (N n) r
        (fun s => A s * ((d n : ℝ) ^ 2 * b n) / Real.logb 2 (d n))) :
    HasPairedDistanceSeparation N := by
  intro r hr
  obtain ⟨Δ, A, hA, hdegree, ht⟩ := htransport r hr
  exact short_paired_fraction_tendsto_zero N r Δ A hA d b hd hb hcard hdegree ht

end DirectedRecovery
