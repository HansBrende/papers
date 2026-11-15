import MacroProjection
import FanoOrder
import LeanMachine.WholeRow.LiftOrder

/-!
# The deterministic Fano lift gap

Every lift with helper containment and per-incidence rectangle mixing has
the stated gap between its feasible full-cell polymatroid value and every
row-order cost, and hence every induced acyclic-set invoice. Positions are
one-based and empty helper sets have cost zero. `FanoOrder.line` and
`FanoCertificate.incident` describe exactly the same base incidence.

The complete lift below supplies an explicit instance, of growing window
`3n`. Fixed-degree existence and growing girth are not asserted here.
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

/-- The same finite gap holds against the invoice from any induced acyclic set. -/
theorem conditional_acyclic_gap (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n)
    (ρ : Clone n → Finset (Clone n))
    (hρ : ∀ j x, x ∈ ρ j → FanoCertificate.incident x.1 j.1)
    (hmix : RectangleMixing Prod.fst Prod.fst ρ FanoOrder.line r)
    {h : Finset (Clone n × Clone n) → ℝ}
    (hh : IsPolymatroid h) (hv : IsValid h (rowHelpers ρ)) (hc : ∀ x, h {x} ≤ 1)
    (A : Finset (Clone n × Clone n))
    (hA : LeanMachine.RecoveryAcyclic.Acyclic (rowHelpers ρ) A) :
    41 * ((n - r + 1 : ℕ) : ℝ)^2 - (119 / 3 : ℝ) * (n : ℝ)^2 ≤
      (7 * n : ℝ)^2 - A.card - h univ := by
  obtain ⟨o, ho⟩ := LeanMachine.WholeRow.AcyclicOrder.exists_cost_le_complement ρ A hA
  have ho' : (A.card : ℝ) + (cost ρ o : ℝ) ≤ (7 * n : ℝ)^2 := by
    exact_mod_cast (by simpa [Fintype.card_prod, pow_two] using ho :
      A.card + cost ρ o ≤ (7 * n)^2)
  have hg := conditional_gap n r hr hrn ρ hρ hmix hh hv hc o
  linarith

/-- At the one-percent mixing threshold, every induced acyclic-set invoice
exceeds every feasible Shannon value by strictly more than one percent. -/
theorem conditional_acyclic_gap_gt_one_percent (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hthreshold : 99 * n ≤ 100 * (n - r + 1))
    (ρ : Clone n → Finset (Clone n))
    (hρ : ∀ j x, x ∈ ρ j → FanoCertificate.incident x.1 j.1)
    (hmix : RectangleMixing Prod.fst Prod.fst ρ FanoOrder.line r)
    {h : Finset (Clone n × Clone n) → ℝ}
    (hh : IsPolymatroid h) (hv : IsValid h (rowHelpers ρ)) (hc : ∀ x, h {x} ≤ 1)
    (A : Finset (Clone n × Clone n))
    (hA : LeanMachine.RecoveryAcyclic.Acyclic (rowHelpers ρ) A) :
    (1 / 100 : ℝ) * (7 * n)^2 < (7 * n : ℝ)^2 - A.card - h univ := by
  obtain ⟨o, ho⟩ := LeanMachine.WholeRow.AcyclicOrder.exists_cost_le_complement ρ A hA
  have ho' : (A.card : ℝ) + (cost ρ o : ℝ) ≤ (7 * n : ℝ)^2 := by
    exact_mod_cast (by simpa [Fintype.card_prod, pow_two] using ho :
      A.card + cost ρ o ≤ (7 * n)^2)
  have hg := conditional_gap_one_percent n r hr hrn hthreshold ρ hρ hmix hh hv hc o
  have hs := gap_coefficient_gt_one_percent n (by omega)
  linarith

/-- All clones of each incident base row. Its window grows as `3n`. -/
def completeLift (n : ℕ) (j : Clone n) : Finset (Clone n) :=
  (FanoOrder.line j.1).product univ

theorem completeLift_containment (n : ℕ) :
    ∀ j x, x ∈ completeLift n j → FanoCertificate.incident x.1 j.1 := by
  intro j x hx
  exact (mem_filter.mp (mem_product.mp hx).1).2

theorem completeLift_width (n : ℕ) (j : Clone n) : (completeLift n j).card = 3 * n := by
  have hl : ∀ j, (FanoOrder.line j).card = 3 := by decide
  simp [completeLift, hl]

/-- The containment and mixing premises coexist, including for every positive
clone count. Empty clone types make this statement vacuously true at zero. -/
theorem completeLift_mixing (n : ℕ) :
    RectangleMixing Prod.fst Prod.fst (completeLift n) FanoOrder.line 1 := by
  intro b k hb X Y hX hY hcX hcY
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < X.card)
  obtain ⟨y, hy⟩ := card_pos.mp (by omega : 0 < Y.card)
  refine ⟨x, hx, y, hy, ?_⟩
  apply mem_product.mpr
  exact ⟨by simpa only [hX x hx, hY y hy] using hb, mem_univ _⟩

/-- The complete lift has the base gap multiplied by `n²`.
This is a growing-window instance, not fixed-degree sparse existence. -/
theorem completeLift_gap (n : ℕ) (hn : 1 ≤ n)
    {h : Finset (Clone n × Clone n) → ℝ}
    (hh : IsPolymatroid h) (hv : IsValid h (rowHelpers (completeLift n)))
    (hc : ∀ x, h {x} ≤ 1) (o : Clone n ≃ Fin (Fintype.card (Clone n))) :
    (4 / 3 : ℝ) * (n : ℝ)^2 ≤ (cost (completeLift n) o : ℝ) - h univ := by
  have hg := conditional_gap n 1 (by omega) hn (completeLift n)
    (completeLift_containment n) (completeLift_mixing n) hh hv hc o
  have he : n - 1 + 1 = n := by omega
  rw [he] at hg
  linarith

#print axioms Clone
#print axioms base_cost_lower
#print axioms clone_cost_lower
#print axioms clone_cost_upper
#print axioms conditional_gap
#print axioms conditional_gap_one_percent
#print axioms gap_coefficient_gt_one_percent
#print axioms conditional_acyclic_gap
#print axioms conditional_acyclic_gap_gt_one_percent
#print axioms completeLift
#print axioms completeLift_containment
#print axioms completeLift_width
#print axioms completeLift_mixing
#print axioms completeLift_gap

end
end LeanBacklog.FanoLift
