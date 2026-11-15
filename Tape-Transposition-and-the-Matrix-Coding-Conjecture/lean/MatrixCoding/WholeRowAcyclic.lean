import MatrixCoding.MacroProjection
import MatrixCoding.FanoOrder
import MatrixCoding.GridOrder

/-!
# Fano and grid gaps against every induced acyclic set

The generic rectangular containment theorem identifies the maximum induced
acyclic set with total cells minus the minimum row-order cost. The full Fano
and grid maxima are respectively 8 and 13. Consequently the already checked
Shannon bounds beat every induced acyclic-set invoice by at least 4/3 and 1/5.
No capacity equality for the grid or sparse-lift existence is asserted.
-/

namespace LeanBacklog.WholeRowAcyclic

open Finset MotionDepthCodes LeanMachine.RecoveryAcyclic
open LeanMachine.WholeRow.AcyclicOrder LeanMachine.WholeRow.LiftOrder
open scoped Classical
noncomputable section

theorem fano_helpers_eq : rowHelpers FanoOrder.line = FanoFull.helpers := by
  funext x
  ext y
  simp [rowHelpers, FanoOrder.line, FanoFull.helpers]

theorem grid_helpers_eq : rowHelpers GridOrder.line = GridFull.helpers := by
  funext x
  ext y
  simp [rowHelpers, GridOrder.line, GridFull.helpers]

theorem fano_minimumCost : minimumCost FanoOrder.line = 41 := by
  exact minimumCost_eq_of_bounds _ _ FanoOrder.exact_last_helper_value.1
    FanoOrder.exact_last_helper_value.2

theorem grid_minimumCost : minimumCost GridOrder.line = 41 := by
  exact minimumCost_eq_of_bounds _ _ GridOrder.exact_last_helper_value.1
    GridOrder.exact_last_helper_value.2

/-- The full Fano host has maximum induced acyclic-set size exactly eight. -/
theorem fano_exact_acyclic_card :
    (∀ A, Acyclic FanoFull.helpers A → A.card ≤ 8) ∧
    ∃ A, Acyclic FanoFull.helpers A ∧ A.card = 8 := by
  simpa [fano_helpers_eq, fano_minimumCost] using exact_acyclic_card FanoOrder.line

/-- The rectangular 9-by-6 grid has maximum induced acyclic-set size thirteen. -/
theorem grid_exact_acyclic_card :
    (∀ A, Acyclic GridFull.helpers A → A.card ≤ 13) ∧
    ∃ A, Acyclic GridFull.helpers A ∧ A.card = 13 := by
  simpa [grid_helpers_eq, grid_minimumCost] using exact_acyclic_card GridOrder.line

/-- The full Fano Shannon bound beats every acyclic invoice by at least 4/3. -/
theorem fano_gap {h : Finset FanoFull.Grid → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h FanoFull.helpers) (hc : ∀ x, h {x} ≤ 1)
    (A : Finset FanoFull.Grid) (hA : Acyclic FanoFull.helpers A) :
    (4 / 3 : ℝ) ≤ 49 - A.card - h univ := by
  have ha : (A.card : ℝ) ≤ 8 := by exact_mod_cast fano_exact_acyclic_card.1 A hA
  have hu := FanoFull.full_upper hh hv hc
  linarith

/-- The full grid Shannon bound beats every acyclic invoice by at least 1/5. -/
theorem grid_gap {h : Finset GridFull.Grid → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h GridFull.helpers) (hc : ∀ x, h {x} ≤ 1)
    (A : Finset GridFull.Grid) (hA : Acyclic GridFull.helpers A) :
    (1 / 5 : ℝ) ≤ 54 - A.card - h univ := by
  have ha : (A.card : ℝ) ≤ 13 := by exact_mod_cast grid_exact_acyclic_card.1 A hA
  have hu := GridFull.full_upper hh hv hc
  linarith

#print axioms fano_helpers_eq
#print axioms grid_helpers_eq
#print axioms fano_minimumCost
#print axioms grid_minimumCost
#print axioms fano_exact_acyclic_card
#print axioms grid_exact_acyclic_card
#print axioms fano_gap
#print axioms grid_gap

end
end LeanBacklog.WholeRowAcyclic
