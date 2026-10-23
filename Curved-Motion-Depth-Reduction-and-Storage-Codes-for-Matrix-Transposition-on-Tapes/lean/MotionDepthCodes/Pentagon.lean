import MotionDepthCodes.Polymatroid
import MotionDepthCodes.FinSums

/-!
# The pentagon is good

Every valid polymatroid on the 5-cycle satisfies `2 h(V) ≤ Σ_v h(v)`. The
certificate is the sum of five elemental inequalities between non-adjacent
vertices,

  `I(0;2) + I(0;3 | 1,2) + I(1;3) + I(1;4) + I(2;4 | 1) ≥ 0`,

after the closures `{0,1,2} → {0,2}`, `{1,2,3} → {1,3}`,
`{0,1,2,3} → V` and `{1,2,4} → V`.
-/

namespace MotionDepthCodes

open Finset
open scoped BigOperators
set_option autoImplicit false

/-- Neighbourhoods of the 5-cycle `0-1-2-3-4-0`. -/
def pentagonNbhd : Fin 5 → Finset (Fin 5) :=
  ![{1, 4}, {0, 2}, {1, 3}, {2, 4}, {0, 3}]

theorem nbhd_cycleGraph_five : nbhd (SimpleGraph.cycleGraph 5) = pentagonNbhd := by
  decide

/-- **The pentagon is good.** -/
theorem rateBound_pentagon : RateBound pentagonNbhd (1 / 2) := by
  intro h hh hv
  have c1 : h {0, 1, 2} = h {0, 2} := hh.eq_of_closure hv (by decide) (by decide)
  have c2 : h {1, 2, 3} = h {1, 3} := hh.eq_of_closure hv (by decide) (by decide)
  have c3 : h univ = h {0, 1, 2, 3} := hh.eq_of_closure hv (by decide) (by decide)
  have c4 : h univ = h {1, 2, 4} := hh.eq_of_closure hv (by decide) (by decide)
  have e1 : h {0, 2} + h ∅ ≤ h {0} + h {2} := hh.elemental (by decide) (by decide)
  have e2 : h {0, 1, 2, 3} + h {1, 2} ≤ h {0, 1, 2} + h {1, 2, 3} :=
    hh.elemental (by decide) (by decide)
  have e3 : h {1, 3} + h ∅ ≤ h {1} + h {3} := hh.elemental (by decide) (by decide)
  have e4 : h {1, 4} + h ∅ ≤ h {1} + h {4} := hh.elemental (by decide) (by decide)
  have e5 : h {1, 2, 4} + h {1} ≤ h {1, 2} + h {1, 4} := hh.elemental (by decide) (by decide)
  have h0 := hh.empty
  simp only [sum_fin_5]
  linarith

/-- **C₅ is good**, for Mathlib's `cycleGraph 5`. -/
theorem rateBound_cycleGraph_five : RateBound (nbhd (SimpleGraph.cycleGraph 5)) (1 / 2) := by
  rw [nbhd_cycleGraph_five]
  exact rateBound_pentagon

end MotionDepthCodes
