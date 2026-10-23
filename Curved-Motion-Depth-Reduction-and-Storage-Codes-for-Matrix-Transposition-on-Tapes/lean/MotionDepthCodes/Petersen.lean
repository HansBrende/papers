import MotionDepthCodes.Polymatroid
import MotionDepthCodes.FinSums

/-!
# The Petersen graph is good

Every valid polymatroid on the Petersen graph satisfies `2 h(V) ≤ Σ_v h(v)`.
The certificate is an exact nonnegative combination of 58 elemental
inequalities `I(i;j|K)` between non-adjacent vertices, with weights `1/4` and
`1/2`, found by linear programming and re-solved exactly in rationals (the
generator is `tools/certificates.py`). `linear_combination` checks the
combination, with its exact coefficients, against the closure equalities.

The labelling is the standard one (outer cycle `0-1-2-3-4`, spokes `i — i+5`,
inner pentagram `5-7-9-6-8`); `petersenGraph_adj_iff` identifies it with the
Kneser graph `K(5,2)`.
-/

namespace MotionDepthCodes

open Finset
open scoped BigOperators
set_option autoImplicit false

/-- Neighbourhoods of the Petersen graph. -/
def petersenNbhd : Fin 10 → Finset (Fin 10) :=
  ![{1, 4, 5}, {0, 2, 6}, {1, 3, 7}, {2, 4, 8}, {0, 3, 9},
    {0, 7, 8}, {1, 8, 9}, {2, 5, 9}, {3, 5, 6}, {4, 6, 7}]

/-- The Petersen graph. -/
def petersenGraph : SimpleGraph (Fin 10) where
  Adj i j := j ∈ petersenNbhd i
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel petersenGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (j ∈ petersenNbhd i))

theorem nbhd_petersenGraph : nbhd petersenGraph = petersenNbhd := by
  decide

/-- The Kneser labelling: vertex `i` is the 2-subset `petersenKneser i` of `Fin 5`. -/
def petersenKneser : Fin 10 → Finset (Fin 5) :=
  ![{0, 1}, {2, 3}, {0, 4}, {1, 2}, {3, 4}, {2, 4}, {1, 4}, {1, 3}, {0, 3}, {0, 2}]

theorem petersenKneser_card : ∀ i, (petersenKneser i).card = 2 := by
  decide

theorem petersenKneser_injective : Function.Injective petersenKneser := by
  decide

/-- `petersenGraph` is the Kneser graph `K(5,2)`: the labelling is a bijection onto
the ten 2-subsets of `Fin 5`, and adjacency is disjointness. -/
theorem petersenGraph_adj_iff (i j : Fin 10) :
    petersenGraph.Adj i j ↔ Disjoint (petersenKneser i) (petersenKneser j) := by
  revert i j
  decide

/-- **The Petersen graph is good.** -/
theorem rateBound_petersen : RateBound petersenNbhd (1 / 2) := by
  intro h hh hv
  have e1 : h {0, 2} + h ∅ ≤ h {0} + h {2} := hh.elemental (by decide) (by decide)
  have e2 : h {0, 1, 2, 3, 6, 7} + h {1, 2, 6, 7} ≤ h {0, 1, 2, 6, 7} + h {1, 2, 3, 6, 7} := hh.elemental (by decide) (by decide)
  have e3 : h {0, 2, 3} + h {2} ≤ h {0, 2} + h {2, 3} := hh.elemental (by decide) (by decide)
  have e4 : h {0, 2, 4, 6, 8, 9} + h {2, 4, 8, 9} ≤ h {0, 2, 4, 8, 9} + h {2, 4, 6, 8, 9} := hh.elemental (by decide) (by decide)
  have e5 : h {0, 2, 6} + h {2} ≤ h {0, 2} + h {2, 6} := hh.elemental (by decide) (by decide)
  have e6 : h {0, 2, 4, 6, 7, 8, 9} + h {2, 4, 6, 8, 9} ≤ h {0, 2, 4, 6, 8, 9} + h {2, 4, 6, 7, 8, 9} := hh.elemental (by decide) (by decide)
  have e7 : h {0, 1, 2, 7} + h {1, 2} ≤ h {0, 1, 2} + h {1, 2, 7} := hh.elemental (by decide) (by decide)
  have e8 : h {0, 1, 3, 6, 7, 8, 9} + h {1, 3, 6, 7, 9} ≤ h {0, 1, 3, 6, 7, 9} + h {1, 3, 6, 7, 8, 9} := hh.elemental (by decide) (by decide)
  have e9 : h {0, 2, 3, 4, 8, 9} + h {2, 3, 4, 9} ≤ h {0, 2, 3, 4, 9} + h {2, 3, 4, 8, 9} := hh.elemental (by decide) (by decide)
  have e10 : h {0, 1, 3, 6, 7, 9} + h {1, 3, 6, 7} ≤ h {0, 1, 3, 6, 7} + h {1, 3, 6, 7, 9} := hh.elemental (by decide) (by decide)
  have e11 : h {0, 2, 3, 9} + h {2, 3} ≤ h {0, 2, 3} + h {2, 3, 9} := hh.elemental (by decide) (by decide)
  have e12 : h {1, 3, 5, 6, 8, 9} + h {5, 6, 8, 9} ≤ h {1, 5, 6, 8, 9} + h {3, 5, 6, 8, 9} := hh.elemental (by decide) (by decide)
  have e13 : h {1, 3} + h ∅ ≤ h {1} + h {3} := hh.elemental (by decide) (by decide)
  have e14 : h {1, 2, 3, 4, 7} + h {2, 3, 7} ≤ h {1, 2, 3, 7} + h {2, 3, 4, 7} := hh.elemental (by decide) (by decide)
  have e15 : h {1, 4} + h ∅ ≤ h {1} + h {4} := hh.elemental (by decide) (by decide)
  have e16 : h {1, 2, 4, 5, 6, 7} + h {2, 4, 6, 7} ≤ h {1, 2, 4, 6, 7} + h {2, 4, 5, 6, 7} := hh.elemental (by decide) (by decide)
  have e17 : h {1, 5, 6, 8} + h {6, 8} ≤ h {1, 6, 8} + h {5, 6, 8} := hh.elemental (by decide) (by decide)
  have e18 : h {1, 7, 9} + h {9} ≤ h {1, 9} + h {7, 9} := hh.elemental (by decide) (by decide)
  have e19 : h {1, 7} + h ∅ ≤ h {1} + h {7} := hh.elemental (by decide) (by decide)
  have e20 : h {1, 2, 8} + h {2} ≤ h {1, 2} + h {2, 8} := hh.elemental (by decide) (by decide)
  have e21 : h {1, 8} + h ∅ ≤ h {1} + h {8} := hh.elemental (by decide) (by decide)
  have e22 : h {1, 2, 4, 8, 9} + h {2, 4, 8} ≤ h {1, 2, 4, 8} + h {2, 4, 8, 9} := hh.elemental (by decide) (by decide)
  have e23 : h {1, 9} + h ∅ ≤ h {1} + h {9} := hh.elemental (by decide) (by decide)
  have e24 : h {2, 4, 6, 7, 9} + h {6, 7, 9} ≤ h {2, 6, 7, 9} + h {4, 6, 7, 9} := hh.elemental (by decide) (by decide)
  have e25 : h {1, 2, 4} + h {1} ≤ h {1, 2} + h {1, 4} := hh.elemental (by decide) (by decide)
  have e26 : h {1, 2, 3, 4, 5, 8, 9} + h {1, 3, 4, 8, 9} ≤ h {1, 2, 3, 4, 8, 9} + h {1, 3, 4, 5, 8, 9} := hh.elemental (by decide) (by decide)
  have e27 : h {2, 5, 9} + h {9} ≤ h {2, 9} + h {5, 9} := hh.elemental (by decide) (by decide)
  have e28 : h {2, 6, 7, 9} + h {7, 9} ≤ h {2, 7, 9} + h {6, 7, 9} := hh.elemental (by decide) (by decide)
  have e29 : h {2, 6} + h ∅ ≤ h {2} + h {6} := hh.elemental (by decide) (by decide)
  have e30 : h {2, 4, 6, 8} + h {4, 6} ≤ h {2, 4, 6} + h {4, 6, 8} := hh.elemental (by decide) (by decide)
  have e31 : h {2, 8} + h ∅ ≤ h {2} + h {8} := hh.elemental (by decide) (by decide)
  have e32 : h {2, 9} + h ∅ ≤ h {2} + h {9} := hh.elemental (by decide) (by decide)
  have e33 : h {1, 2, 3, 4, 5, 6, 7} + h {1, 2, 4, 6, 7} ≤ h {1, 2, 3, 4, 6, 7} + h {1, 2, 4, 5, 6, 7} := hh.elemental (by decide) (by decide)
  have e34 : h {3, 5} + h ∅ ≤ h {3} + h {5} := hh.elemental (by decide) (by decide)
  have e35 : h {1, 2, 3, 6, 7} + h {1, 2, 7} ≤ h {1, 2, 3, 7} + h {1, 2, 6, 7} := hh.elemental (by decide) (by decide)
  have e36 : h {3, 6} + h ∅ ≤ h {3} + h {6} := hh.elemental (by decide) (by decide)
  have e37 : h {1, 3, 7, 9} + h {1, 9} ≤ h {1, 3, 9} + h {1, 7, 9} := hh.elemental (by decide) (by decide)
  have e38 : h {1, 3, 7} + h {1} ≤ h {1, 3} + h {1, 7} := hh.elemental (by decide) (by decide)
  have e39 : h {3, 5, 6, 8, 9} + h {5, 6, 8} ≤ h {3, 5, 6, 8} + h {5, 6, 8, 9} := hh.elemental (by decide) (by decide)
  have e40 : h {2, 3, 9} + h {2} ≤ h {2, 3} + h {2, 9} := hh.elemental (by decide) (by decide)
  have e41 : h {1, 3, 4, 5, 8, 9} + h {1, 3, 8, 9} ≤ h {1, 3, 4, 8, 9} + h {1, 3, 5, 8, 9} := hh.elemental (by decide) (by decide)
  have e42 : h {2, 4, 5, 6, 7, 9} + h {2, 6, 7, 9} ≤ h {2, 4, 6, 7, 9} + h {2, 5, 6, 7, 9} := hh.elemental (by decide) (by decide)
  have e43 : h {1, 3, 4, 6, 7} + h {1, 3, 7} ≤ h {1, 3, 4, 7} + h {1, 3, 6, 7} := hh.elemental (by decide) (by decide)
  have e44 : h {4, 6, 7} + h {7} ≤ h {4, 7} + h {6, 7} := hh.elemental (by decide) (by decide)
  have e45 : h {2, 3, 4, 7} + h {2, 3} ≤ h {2, 3, 4} + h {2, 3, 7} := hh.elemental (by decide) (by decide)
  have e46 : h {4, 7} + h ∅ ≤ h {4} + h {7} := hh.elemental (by decide) (by decide)
  have e47 : h {4, 6, 8} + h {6} ≤ h {4, 6} + h {6, 8} := hh.elemental (by decide) (by decide)
  have e48 : h {1, 2, 4, 8} + h {1, 2} ≤ h {1, 2, 4} + h {1, 2, 8} := hh.elemental (by decide) (by decide)
  have e49 : h {2, 5, 6, 7, 9} + h {2, 7, 9} ≤ h {2, 5, 7, 9} + h {2, 6, 7, 9} := hh.elemental (by decide) (by decide)
  have e50 : h {3, 5, 6} + h {3} ≤ h {3, 5} + h {3, 6} := hh.elemental (by decide) (by decide)
  have e51 : h {1, 5, 6, 8, 9} + h {1, 6, 8} ≤ h {1, 5, 6, 8} + h {1, 6, 8, 9} := hh.elemental (by decide) (by decide)
  have e52 : h {5, 9} + h ∅ ≤ h {5} + h {9} := hh.elemental (by decide) (by decide)
  have e53 : h {0, 1, 2, 6, 7} + h {0, 1, 2} ≤ h {0, 1, 2, 6} + h {0, 1, 2, 7} := hh.elemental (by decide) (by decide)
  have e54 : h {6, 7} + h ∅ ≤ h {6} + h {7} := hh.elemental (by decide) (by decide)
  have e55 : h {1, 3, 7, 8, 9} + h {1, 3, 9} ≤ h {1, 3, 7, 9} + h {1, 3, 8, 9} := hh.elemental (by decide) (by decide)
  have e56 : h {2, 4, 6, 7, 8} + h {2, 4, 6} ≤ h {2, 4, 6, 7} + h {2, 4, 6, 8} := hh.elemental (by decide) (by decide)
  have e57 : h {2, 3, 4, 8, 9} + h {2, 3, 4} ≤ h {2, 3, 4, 8} + h {2, 3, 4, 9} := hh.elemental (by decide) (by decide)
  have e58 : h {1, 8, 9} + h {1} ≤ h {1, 8} + h {1, 9} := hh.elemental (by decide) (by decide)
  have c1 : h {1, 6, 8, 9} = h {1, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c2 : h {2, 3, 4, 6, 7, 8, 9} = h {2, 4, 6, 7, 8} := hh.eq_of_closure hv (by decide) (by decide)
  have c3 : h {1, 2, 3, 6, 7, 8, 9} = h {1, 3, 7, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c4 : h {3, 5, 6, 8} = h {3, 5, 6} := hh.eq_of_closure hv (by decide) (by decide)
  have c5 : h {4, 6, 7, 9} = h {4, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c6 : h {1, 2, 3, 4, 7} = h {1, 3, 4, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c7 : h {1, 2, 3, 4, 6, 7, 9} = h {1, 3, 4, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c8 : h {1, 3, 5, 6, 8, 9} = h {1, 3, 5, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c9 : h {1, 3, 6, 8, 9} = h {1, 3, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c10 : h {1, 2, 3, 7} = h {1, 3, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c11 : h {1, 2, 3, 7, 9} = h {1, 3, 7, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c12 : h {1, 2, 3, 4, 6, 7, 9} = h {1, 2, 3, 4, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c13 : h univ = h {1, 2, 3, 4, 5, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c14 : h {2, 3, 4, 6, 8} = h {2, 4, 6, 8} := hh.eq_of_closure hv (by decide) (by decide)
  have c15 : h {2, 5, 7, 9} = h {2, 5, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c16 : h {0, 1, 3, 4, 5, 6, 8, 9} = h {1, 3, 4, 5, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c17 : h {1, 2, 3, 4, 6, 8, 9} = h {1, 2, 3, 4, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c18 : h {1, 3, 4, 6, 8, 9} = h {1, 3, 4, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c19 : h univ = h {1, 2, 3, 4, 5, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c20 : h {1, 2, 3, 4, 8} = h {1, 2, 4, 8} := hh.eq_of_closure hv (by decide) (by decide)
  have c21 : h {2, 3, 4, 8} = h {2, 4, 8} := hh.eq_of_closure hv (by decide) (by decide)
  have c22 : h {1, 2, 3, 4, 6, 8, 9} = h {1, 2, 4, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c23 : h {2, 4, 5, 6, 7, 9} = h {2, 4, 5, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c24 : h {1, 2, 4, 6, 7, 9} = h {1, 2, 4, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c25 : h {2, 4, 6, 7, 9} = h {2, 4, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c26 : h {0, 1, 2, 4, 5, 6, 7, 9} = h {1, 2, 4, 5, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c27 : h {0, 2, 3, 4, 9} = h {0, 2, 3, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c28 : h {0, 1, 2, 3, 6, 7} = h {0, 1, 3, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c29 : h {1, 2, 3, 6, 7} = h {1, 3, 6, 7} := hh.eq_of_closure hv (by decide) (by decide)
  have c30 : h {1, 2, 3, 6, 7, 8, 9} = h {1, 3, 6, 7, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c31 : h {0, 1, 2, 3, 4, 6, 7, 9} = h {0, 1, 3, 6, 7, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c32 : h {1, 2, 3, 6, 7, 9} = h {1, 3, 6, 7, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c33 : h univ = h {0, 1, 3, 6, 7, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c34 : h {2, 3, 4, 6, 7, 8, 9} = h {2, 4, 6, 7, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c35 : h univ = h {0, 2, 4, 6, 7, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c36 : h {0, 1, 2, 6} = h {0, 2, 6} := hh.eq_of_closure hv (by decide) (by decide)
  have c37 : h {2, 3, 4, 6, 8, 9} = h {2, 4, 6, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c38 : h {0, 2, 3, 4, 8, 9} = h {0, 2, 4, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c39 : h {2, 3, 4, 8, 9} = h {2, 4, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have c40 : h {0, 1, 2, 3, 4, 6, 8, 9} = h {0, 2, 4, 6, 8, 9} := hh.eq_of_closure hv (by decide) (by decide)
  have h0 := hh.empty
  simp only [sum_fin_10]
  linear_combination (1 / 2 : ℝ) * e1 + (1 / 4 : ℝ) * e2 + (1 / 4 : ℝ) * e3 + (1 / 4 : ℝ) * e4 +
    (1 / 4 : ℝ) * e5 + (1 / 4 : ℝ) * e6 + (1 / 4 : ℝ) * e7 + (1 / 4 : ℝ) * e8 + (1 / 4 : ℝ) * e9 +
    (1 / 4 : ℝ) * e10 + (1 / 4 : ℝ) * e11 + (1 / 4 : ℝ) * e12 + (1 / 4 : ℝ) * e13 +
    (1 / 4 : ℝ) * e14 + (1 / 4 : ℝ) * e15 + (1 / 4 : ℝ) * e16 + (1 / 4 : ℝ) * e17 +
    (1 / 4 : ℝ) * e18 + (1 / 4 : ℝ) * e19 + (1 / 4 : ℝ) * e20 + (1 / 4 : ℝ) * e21 +
    (1 / 4 : ℝ) * e22 + (1 / 4 : ℝ) * e23 + (1 / 4 : ℝ) * e24 + (1 / 4 : ℝ) * e25 +
    (1 / 4 : ℝ) * e26 + (1 / 4 : ℝ) * e27 + (1 / 4 : ℝ) * e28 + (1 / 4 : ℝ) * e29 +
    (1 / 4 : ℝ) * e30 + (1 / 4 : ℝ) * e31 + (1 / 2 : ℝ) * e32 + (1 / 4 : ℝ) * e33 +
    (1 / 4 : ℝ) * e34 + (1 / 4 : ℝ) * e35 + (1 / 4 : ℝ) * e36 + (1 / 4 : ℝ) * e37 +
    (1 / 4 : ℝ) * e38 + (1 / 4 : ℝ) * e39 + (1 / 4 : ℝ) * e40 + (1 / 4 : ℝ) * e41 +
    (1 / 4 : ℝ) * e42 + (1 / 4 : ℝ) * e43 + (1 / 4 : ℝ) * e44 + (1 / 4 : ℝ) * e45 +
    (1 / 4 : ℝ) * e46 + (1 / 4 : ℝ) * e47 + (1 / 4 : ℝ) * e48 + (1 / 4 : ℝ) * e49 +
    (1 / 4 : ℝ) * e50 + (1 / 4 : ℝ) * e51 + (1 / 4 : ℝ) * e52 + (1 / 4 : ℝ) * e53 +
    (1 / 4 : ℝ) * e54 + (1 / 4 : ℝ) * e55 + (1 / 4 : ℝ) * e56 + (1 / 4 : ℝ) * e57 +
    (1 / 4 : ℝ) * e58 + (1 / 4 : ℝ) * c1 + (1 / 4 : ℝ) * c2 + (1 / 4 : ℝ) * c3 + (1 / 4 : ℝ) * c4 +
    (1 / 4 : ℝ) * c5 + (-1 / 4 : ℝ) * c6 + (1 / 4 : ℝ) * c7 + (-1 / 4 : ℝ) * c8 +
    (1 / 2 : ℝ) * c10 + (-1 / 4 : ℝ) * c12 + (1 / 4 : ℝ) * c13 + (1 / 4 : ℝ) * c15 +
    (-1 / 4 : ℝ) * c17 + (1 / 4 : ℝ) * c19 + (1 / 4 : ℝ) * c21 + (1 / 4 : ℝ) * c22 +
    (-1 / 4 : ℝ) * c23 + (1 / 4 : ℝ) * c27 + (-1 / 4 : ℝ) * c28 + (-1 / 4 : ℝ) * c30 +
    (1 / 4 : ℝ) * c33 + (-1 / 4 : ℝ) * c34 + (1 / 4 : ℝ) * c35 + (1 / 4 : ℝ) * c36 +
    (-1 / 4 : ℝ) * c38 + (-4 : ℝ) * h0

theorem rateBound_petersenGraph : RateBound (nbhd petersenGraph) (1 / 2) := by
  rw [nbhd_petersenGraph]
  exact rateBound_petersen

end MotionDepthCodes
