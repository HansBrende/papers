import MacroProjection
import FanoOrder
import LeanMachine.WholeRow.LiftOrder

/-!
# The deterministic Fano lift gap

Every lift with helper containment and per-incidence rectangle mixing has
the stated gap between its feasible full-cell polymatroid value and every
row-order cost. Positions are one-based and empty helper sets have cost zero.
Existence, degree bounds and growing girth are not asserted here. Comparing
against all acyclic-set bounds additionally uses Paper 17's written theorem.
-/

namespace LeanBacklog.FanoLift

open Finset MotionDepthCodes LeanMachine.WholeRow.LiftOrder MacroProjection
open scoped BigOperators Classical
noncomputable section

abbrev Clone (n : ℕ) := Fin 7 × Fin n

/-- The value 41 is the same one-based last-helper cost used in the lift. -/
theorem base_cost_lower (p : Fin 7 ≃ Fin (Fintype.card (Fin 7))) :
    41 ≤ cost FanoOrder.line p := by
  convert FanoOrder.exact_last_helper_value.1 p using 1
  unfold cost FanoOrder.lastHelperPosition
  congr 1

/-- No fine row order costs less than `41*(n-r+1)^2`. -/
theorem clone_cost_lower (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n)
    (ρ : Clone n → Finset (Clone n))
    (hmix : RectangleMixing Prod.fst Prod.fst ρ FanoOrder.line r)
    (o : Clone n ≃ Fin (Fintype.card (Clone n))) :
    41 * (n - r + 1)^2 ≤ cost ρ o := by
  simpa only [mul_comm] using cost_ge_of_base_bound Prod.fst Prod.fst ρ FanoOrder.line
    n r 41 hr hrn (clone_group_card n) (clone_group_card n) hmix base_cost_lower o

/-- Contiguous clone groups retain the base order upper bound, without mixing. -/
theorem clone_cost_upper (n : ℕ) (ρ : Clone n → Finset (Clone n))
    (hρ : ∀ j x, x ∈ ρ j → FanoCertificate.incident x.1 j.1) :
    ∃ o : Clone n ≃ Fin (Fintype.card (Clone n)), cost ρ o ≤ 41 * n^2 := by
  obtain ⟨p, hp⟩ := FanoOrder.exact_last_helper_value.2
  refine ⟨cloneOrder n p, ?_⟩
  have hp' : cost FanoOrder.line p = 41 := hp
  have hu := cost_clone_order_le n ρ FanoOrder.line
    (fun j x hx => mem_filter.mpr ⟨mem_univ _, hρ j x hx⟩) p
  simpa only [hp', mul_comm] using hu

/-- A finite gap for every feasible polymatroid and every fine row order. -/
theorem conditional_gap (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n)
    (ρ : Clone n → Finset (Clone n))
    (hρ : ∀ j x, x ∈ ρ j → FanoCertificate.incident x.1 j.1)
    (hmix : RectangleMixing Prod.fst Prod.fst ρ FanoOrder.line r)
    {h : Finset (Clone n × Clone n) → ℝ}
    (hh : IsPolymatroid h) (hv : IsValid h (rowHelpers ρ)) (hc : ∀ x, h {x} ≤ 1)
    (o : Clone n ≃ Fin (Fintype.card (Clone n))) :
    41 * ((n - r + 1 : ℕ) : ℝ)^2 - (119 / 3 : ℝ) * (n : ℝ)^2 ≤
      (cost ρ o : ℝ) - h univ := by
  have hl : 41 * ((n - r + 1 : ℕ) : ℝ)^2 ≤ (cost ρ o : ℝ) := by
    exact_mod_cast clone_cost_lower n r hr hrn ρ hmix o
  have hu : 3 * h univ ≤ 119 * (n : ℝ)^2 := by
    simpa only [Nat.cast_mul, pow_two] using fano_clone_upper n n ρ hρ hh hv hc
  linarith

/-- With `a ≥ 99n/100`, the gap is at least `15523 n²/30000`.
The threshold is given without a rounding convention; in particular it
holds for `r = ceil(n/100)`. -/
theorem conditional_gap_one_percent (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hthreshold : 99 * n ≤ 100 * (n - r + 1))
    (ρ : Clone n → Finset (Clone n))
    (hρ : ∀ j x, x ∈ ρ j → FanoCertificate.incident x.1 j.1)
    (hmix : RectangleMixing Prod.fst Prod.fst ρ FanoOrder.line r)
    {h : Finset (Clone n × Clone n) → ℝ}
    (hh : IsPolymatroid h) (hv : IsValid h (rowHelpers ρ)) (hc : ∀ x, h {x} ≤ 1)
    (o : Clone n ≃ Fin (Fintype.card (Clone n))) :
    (15523 / 30000 : ℝ) * (n : ℝ)^2 ≤ (cost ρ o : ℝ) - h univ := by
  have ht : (99 : ℝ) * n ≤ 100 * ((n - r + 1 : ℕ) : ℝ) := by exact_mod_cast hthreshold
  have hsq : ((99 : ℝ) * n)^2 ≤ (100 * ((n - r + 1 : ℕ) : ℝ))^2 :=
    pow_le_pow_left₀ (by positivity) ht 2
  have hg := conditional_gap n r hr hrn ρ hρ hmix hh hv hc o
  nlinarith

/-- The exact gap coefficient is strictly larger than one percent of the
full `(7n)²` array whenever the clone count is positive. -/
theorem gap_coefficient_gt_one_percent (n : ℕ) (hn : 0 < n) :
    (1 / 100 : ℝ) * (7 * n)^2 < (15523 / 30000 : ℝ) * (n : ℝ)^2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith [sq_pos_of_pos hn']

#print axioms Clone
#print axioms base_cost_lower
#print axioms clone_cost_lower
#print axioms clone_cost_upper
#print axioms conditional_gap
#print axioms conditional_gap_one_percent
#print axioms gap_coefficient_gt_one_percent

end
end LeanBacklog.FanoLift
