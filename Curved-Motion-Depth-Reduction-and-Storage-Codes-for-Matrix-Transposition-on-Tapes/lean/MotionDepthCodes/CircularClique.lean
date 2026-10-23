import MotionDepthCodes.Polymatroid
import MotionDepthCodes.FinSums
import MotionDepthCodes.Symmetry

/-!
# Circular cliques are good

The circular clique `K_{p/q}` has vertices `ℤ/p`, with `i ~ j` iff
`q ≤ (j - i) mod p ≤ p - q`. A graph has circular chromatic number at most `p/q`
iff it maps homomorphically to `K_{p/q}`. The circular clique `K_{14/5}` (the
Andrásfai graph `And(5)`) satisfies `2 h(V) ≤ Σ_v h(v)` for every valid
polymatroid. The polymatroid is first symmetrized over the dihedral automorphism
group; the certificate then uses 32 orbit rows, explicit automorphisms, and
`linear_combination` with exact coefficients.

If `p/q ≤ p'/q'` (with `q' ≥ 1`), the map `i ↦ ⌊p' i / p⌋` is a homomorphism
`K_{p/q} → K_{p'/q'}` (Bondy–Hell, `circularCliqueHom`). So every circular clique `K_{p/q}` with
`p/q ≤ 14/5`, for instance `K_{8/3}` (the Möbius ladder, `And(3)`) and `K_{11/4}` (`And(4)`), is good
by Theorem H (`rateBound_circularClique_of_le`). The odd cycle `C_{2k+1}` maps to `K_{(2k+1)/k}` by
`i ↦ k i`, so every odd cycle of length at least `5` is good (`rateBound_cycleGraph_odd`).
-/

namespace MotionDepthCodes

open Finset
open scoped BigOperators
set_option autoImplicit false

/-- The circular clique `K_{p/q}`. -/
def circularClique (p q : ℕ) : SimpleGraph (Fin p) :=
  SimpleGraph.fromRel fun i j => q ≤ (j - i).val ∧ (j - i).val ≤ p - q

instance (p q : ℕ) : DecidableRel (circularClique p q).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ((q ≤ (j - i).val ∧ (j - i).val ≤ p - q) ∨
    (q ≤ (i - j).val ∧ (i - j).val ≤ p - q))))

/-- Neighbourhoods of `K_{14/5}`. -/
def k145Nbhd : Fin 14 → Finset (Fin 14) :=
  ![{5, 6, 7, 8, 9}, {6, 7, 8, 9, 10}, {7, 8, 9, 10, 11}, {8, 9, 10, 11, 12},
    {9, 10, 11, 12, 13}, {0, 10, 11, 12, 13}, {0, 1, 11, 12, 13}, {0, 1, 2, 12, 13},
    {0, 1, 2, 3, 13}, {0, 1, 2, 3, 4}, {1, 2, 3, 4, 5}, {2, 3, 4, 5, 6}, {3, 4, 5, 6, 7},
    {4, 5, 6, 7, 8}]

theorem nbhd_circularClique_14_5 : nbhd (circularClique 14 5) = k145Nbhd := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut0 : Equiv.Perm (Fin 14) where
  toFun := ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 1]
  invFun := ![12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut0_isAut : IsAut k145Nbhd k145Aut0 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut1 : Equiv.Perm (Fin 14) where
  toFun := ![3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 1, 2]
  invFun := ![11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut1_isAut : IsAut k145Nbhd k145Aut1 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut2 : Equiv.Perm (Fin 14) where
  toFun := ![4, 3, 2, 1, 0, 13, 12, 11, 10, 9, 8, 7, 6, 5]
  invFun := ![4, 3, 2, 1, 0, 13, 12, 11, 10, 9, 8, 7, 6, 5]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut2_isAut : IsAut k145Nbhd k145Aut2 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut3 : Equiv.Perm (Fin 14) where
  toFun := ![4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3]
  invFun := ![10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut3_isAut : IsAut k145Nbhd k145Aut3 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut4 : Equiv.Perm (Fin 14) where
  toFun := ![0, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]
  invFun := ![0, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut4_isAut : IsAut k145Nbhd k145Aut4 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut5 : Equiv.Perm (Fin 14) where
  toFun := ![8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![6, 7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut5_isAut : IsAut k145Nbhd k145Aut5 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut6 : Equiv.Perm (Fin 14) where
  toFun := ![13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  invFun := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut6_isAut : IsAut k145Nbhd k145Aut6 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut7 : Equiv.Perm (Fin 14) where
  toFun := ![3, 2, 1, 0, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4]
  invFun := ![3, 2, 1, 0, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut7_isAut : IsAut k145Nbhd k145Aut7 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut8 : Equiv.Perm (Fin 14) where
  toFun := ![7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6]
  invFun := ![7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut8_isAut : IsAut k145Nbhd k145Aut8 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut9 : Equiv.Perm (Fin 14) where
  toFun := ![12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  invFun := ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut9_isAut : IsAut k145Nbhd k145Aut9 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut10 : Equiv.Perm (Fin 14) where
  toFun := ![8, 7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 11, 10, 9]
  invFun := ![8, 7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 11, 10, 9]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut10_isAut : IsAut k145Nbhd k145Aut10 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut11 : Equiv.Perm (Fin 14) where
  toFun := ![5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4]
  invFun := ![9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut11_isAut : IsAut k145Nbhd k145Aut11 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut12 : Equiv.Perm (Fin 14) where
  toFun := ![2, 1, 0, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3]
  invFun := ![2, 1, 0, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut12_isAut : IsAut k145Nbhd k145Aut12 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut13 : Equiv.Perm (Fin 14) where
  toFun := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0]
  invFun := ![13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut13_isAut : IsAut k145Nbhd k145Aut13 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut14 : Equiv.Perm (Fin 14) where
  toFun := ![7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 11, 10, 9, 8]
  invFun := ![7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 11, 10, 9, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut14_isAut : IsAut k145Nbhd k145Aut14 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut15 : Equiv.Perm (Fin 14) where
  toFun := ![11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  invFun := ![3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 1, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut15_isAut : IsAut k145Nbhd k145Aut15 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut16 : Equiv.Perm (Fin 14) where
  toFun := ![6, 7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5]
  invFun := ![8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut16_isAut : IsAut k145Nbhd k145Aut16 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut17 : Equiv.Perm (Fin 14) where
  toFun := ![1, 0, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2]
  invFun := ![1, 0, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut17_isAut : IsAut k145Nbhd k145Aut17 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut18 : Equiv.Perm (Fin 14) where
  toFun := ![10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  invFun := ![4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut18_isAut : IsAut k145Nbhd k145Aut18 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut19 : Equiv.Perm (Fin 14) where
  toFun := ![11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 13, 12]
  invFun := ![11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 13, 12]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut19_isAut : IsAut k145Nbhd k145Aut19 := by
  decide

/-- An automorphism used by the certificate. -/
def k145Aut20 : Equiv.Perm (Fin 14) where
  toFun := ![9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 11, 10]
  invFun := ![9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 11, 10]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem k145Aut20_isAut : IsAut k145Nbhd k145Aut20 := by
  decide

/-- **`K_{14/5}` is good.** -/
theorem rateBound_k145 : RateBound k145Nbhd (1 / 2) := by
  apply RateBound.of_invariant
  intro h hh hv hinv
  have e1 : h {0, 1, 11, 12, 13} + h {11, 12, 13} ≤ h {0, 11, 12, 13} + h {1, 11, 12, 13} := hh.elemental (by decide) (by decide)
  have e2 : h {0, 1, 2, 3, 12, 13} + h {2, 3, 12, 13} ≤ h {0, 2, 3, 12, 13} + h {1, 2, 3, 12, 13} := hh.elemental (by decide) (by decide)
  have e3 : h {0, 1, 3, 4, 13} + h {3, 4, 13} ≤ h {0, 3, 4, 13} + h {1, 3, 4, 13} := hh.elemental (by decide) (by decide)
  have e4 : h {0, 1, 2, 13} + h {2, 13} ≤ h {0, 2, 13} + h {1, 2, 13} := hh.elemental (by decide) (by decide)
  have e5 : h {0, 1, 12} + h {12} ≤ h {0, 12} + h {1, 12} := hh.elemental (by decide) (by decide)
  have e6 : h {0, 1, 5, 10, 11} + h {5, 10, 11} ≤ h {0, 5, 10, 11} + h {1, 5, 10, 11} := hh.elemental (by decide) (by decide)
  have e7 : h {0, 1, 10} + h {10} ≤ h {0, 10} + h {1, 10} := hh.elemental (by decide) (by decide)
  have e8 : h {0, 1, 2, 5, 6, 10, 11, 12, 13} + h {1, 5, 6, 10, 11, 12, 13} ≤ h {0, 1, 5, 6, 10, 11, 12, 13} + h {1, 2, 5, 6, 10, 11, 12, 13} := hh.elemental (by decide) (by decide)
  have e9 : h {0, 2, 12, 13} + h {12, 13} ≤ h {0, 12, 13} + h {2, 12, 13} := hh.elemental (by decide) (by decide)
  have e10 : h {0, 1, 2, 6, 10, 11, 12} + h {1, 6, 10, 11, 12} ≤ h {0, 1, 6, 10, 11, 12} + h {1, 2, 6, 10, 11, 12} := hh.elemental (by decide) (by decide)
  have e11 : h {0, 1, 2, 6, 10, 11} + h {1, 6, 10, 11} ≤ h {0, 1, 6, 10, 11} + h {1, 2, 6, 10, 11} := hh.elemental (by decide) (by decide)
  have e12 : h {0, 1, 2, 6, 11} + h {1, 6, 11} ≤ h {0, 1, 6, 11} + h {1, 2, 6, 11} := hh.elemental (by decide) (by decide)
  have e13 : h {0, 2} + h ∅ ≤ h {0} + h {2} := hh.elemental (by decide) (by decide)
  have e14 : h {0, 1, 2, 3, 6, 7, 11, 12, 13} + h {1, 2, 6, 7, 11, 12, 13} ≤ h {0, 1, 2, 6, 7, 11, 12, 13} + h {1, 2, 3, 6, 7, 11, 12, 13} := hh.elemental (by decide) (by decide)
  have e15 : h {0, 2, 3, 6, 7, 11, 12, 13} + h {2, 6, 7, 11, 12, 13} ≤ h {0, 2, 6, 7, 11, 12, 13} + h {2, 3, 6, 7, 11, 12, 13} := hh.elemental (by decide) (by decide)
  have e16 : h {0, 1, 2, 3, 7, 11, 12, 13} + h {1, 2, 7, 11, 12, 13} ≤ h {0, 1, 2, 7, 11, 12, 13} + h {1, 2, 3, 7, 11, 12, 13} := hh.elemental (by decide) (by decide)
  have e17 : h {0, 3, 4, 13} + h {4, 13} ≤ h {0, 4, 13} + h {3, 4, 13} := hh.elemental (by decide) (by decide)
  have e18 : h {0, 1, 2, 3, 5, 6, 7, 10, 11, 12} + h {1, 2, 5, 6, 7, 10, 11, 12} ≤ h {0, 1, 2, 5, 6, 7, 10, 11, 12} + h {1, 2, 3, 5, 6, 7, 10, 11, 12} := hh.elemental (by decide) (by decide)
  have e19 : h {0, 1, 2, 3, 6, 7, 10, 11, 12} + h {1, 2, 6, 7, 10, 11, 12} ≤ h {0, 1, 2, 6, 7, 10, 11, 12} + h {1, 2, 3, 6, 7, 10, 11, 12} := hh.elemental (by decide) (by decide)
  have e20 : h {0, 1, 2, 3, 7, 12} + h {1, 2, 7, 12} ≤ h {0, 1, 2, 7, 12} + h {1, 2, 3, 7, 12} := hh.elemental (by decide) (by decide)
  have e21 : h {0, 2, 3, 12} + h {2, 12} ≤ h {0, 2, 12} + h {2, 3, 12} := hh.elemental (by decide) (by decide)
  have e22 : h {0, 3} + h ∅ ≤ h {0} + h {3} := hh.elemental (by decide) (by decide)
  have e23 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13} + h {1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13} ≤ h {0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13} + h {1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13} := hh.elemental (by decide) (by decide)
  have e24 : h {0, 1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13} + h {1, 2, 3, 6, 7, 8, 10, 11, 12, 13} ≤ h {0, 1, 2, 3, 6, 7, 8, 10, 11, 12, 13} + h {1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13} := hh.elemental (by decide) (by decide)
  have e25 : h {0, 1, 2, 3, 4, 6, 7, 8, 11, 12, 13} + h {1, 2, 3, 6, 7, 8, 11, 12, 13} ≤ h {0, 1, 2, 3, 6, 7, 8, 11, 12, 13} + h {1, 2, 3, 4, 6, 7, 8, 11, 12, 13} := hh.elemental (by decide) (by decide)
  have e26 : h {0, 1, 2, 3, 4, 7, 8, 11, 12, 13} + h {1, 2, 3, 7, 8, 11, 12, 13} ≤ h {0, 1, 2, 3, 7, 8, 11, 12, 13} + h {1, 2, 3, 4, 7, 8, 11, 12, 13} := hh.elemental (by decide) (by decide)
  have e27 : h {0, 2, 3, 4, 7, 8, 12, 13} + h {2, 3, 7, 8, 12, 13} ≤ h {0, 2, 3, 7, 8, 12, 13} + h {2, 3, 4, 7, 8, 12, 13} := hh.elemental (by decide) (by decide)
  have e28 : h {0, 3, 4, 7, 8, 12, 13} + h {3, 7, 8, 12, 13} ≤ h {0, 3, 7, 8, 12, 13} + h {3, 4, 7, 8, 12, 13} := hh.elemental (by decide) (by decide)
  have e29 : h {0, 1, 2, 3, 4, 8, 13} + h {1, 2, 3, 8, 13} ≤ h {0, 1, 2, 3, 8, 13} + h {1, 2, 3, 4, 8, 13} := hh.elemental (by decide) (by decide)
  have e30 : h {0, 4, 8, 13} + h {8, 13} ≤ h {0, 8, 13} + h {4, 8, 13} := hh.elemental (by decide) (by decide)
  have e31 : h {0, 3, 4} + h {3} ≤ h {0, 3} + h {3, 4} := hh.elemental (by decide) (by decide)
  have e32 : h {0, 2, 4} + h {2} ≤ h {0, 2} + h {2, 4} := hh.elemental (by decide) (by decide)
  have s1 : h {2, 4} = h {0, 2} := by
    have h1 := hinv k145Aut0 k145Aut0_isAut {0, 2}
    rwa [show ({0, 2} : Finset (Fin 14)).map k145Aut0.toEmbedding = {2, 4} by decide] at h1
  have s2 : h {3, 4} = h {0, 1} := by
    have h1 := hinv k145Aut1 k145Aut1_isAut {0, 1}
    rwa [show ({0, 1} : Finset (Fin 14)).map k145Aut1.toEmbedding = {3, 4} by decide] at h1
  have s3 : h {0, 3, 4} = h {0, 1, 4} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0, 1, 4}
    rwa [show ({0, 1, 4} : Finset (Fin 14)).map k145Aut2.toEmbedding = {0, 3, 4} by decide] at h1
  have s4 : h {4, 8, 13} = h {0, 4, 9} := by
    have h1 := hinv k145Aut3 k145Aut3_isAut {0, 4, 9}
    rwa [show ({0, 4, 9} : Finset (Fin 14)).map k145Aut3.toEmbedding = {4, 8, 13} by decide] at h1
  have s5 : h {0, 8, 13} = h {0, 1, 6} := by
    have h1 := hinv k145Aut4 k145Aut4_isAut {0, 1, 6}
    rwa [show ({0, 1, 6} : Finset (Fin 14)).map k145Aut4.toEmbedding = {0, 8, 13} by decide] at h1
  have s6 : h {8, 13} = h {0, 5} := by
    have h1 := hinv k145Aut5 k145Aut5_isAut {0, 5}
    rwa [show ({0, 5} : Finset (Fin 14)).map k145Aut5.toEmbedding = {8, 13} by decide] at h1
  have s7 : h {0, 4, 8, 13} = h {0, 1, 5, 9} := by
    have h1 := hinv k145Aut6 k145Aut6_isAut {0, 1, 5, 9}
    rwa [show ({0, 1, 5, 9} : Finset (Fin 14)).map k145Aut6.toEmbedding = {0, 4, 8, 13} by decide] at h1
  have s8 : h {1, 2, 3, 4, 8, 13} = h {0, 2, 3, 4, 5, 9} := by
    have h1 := hinv k145Aut6 k145Aut6_isAut {0, 2, 3, 4, 5, 9}
    rwa [show ({0, 2, 3, 4, 5, 9} : Finset (Fin 14)).map k145Aut6.toEmbedding = {1, 2, 3, 4, 8, 13} by decide] at h1
  have s9 : h {0, 1, 2, 3, 8, 13} = h {0, 1, 2, 3, 4, 9} := by
    have h1 := hinv k145Aut6 k145Aut6_isAut {0, 1, 2, 3, 4, 9}
    rwa [show ({0, 1, 2, 3, 4, 9} : Finset (Fin 14)).map k145Aut6.toEmbedding = {0, 1, 2, 3, 8, 13} by decide] at h1
  have s10 : h {1, 2, 3, 8, 13} = h {0, 1, 2, 4, 9} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 4, 9}
    rwa [show ({0, 1, 2, 4, 9} : Finset (Fin 14)).map k145Aut7.toEmbedding = {1, 2, 3, 8, 13} by decide] at h1
  have c1 : h {0, 1, 2, 3, 4, 8, 9, 13} = h {0, 1, 2, 3, 4, 8, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s11 : h {0, 1, 2, 3, 4, 8, 9, 13} = h {0, 1, 2, 3, 4, 5, 9, 10} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0, 1, 2, 3, 4, 5, 9, 10}
    rwa [show ({0, 1, 2, 3, 4, 5, 9, 10} : Finset (Fin 14)).map k145Aut2.toEmbedding = {0, 1, 2, 3, 4, 8, 9, 13} by decide] at h1
  have s12 : h {3, 4, 7, 8, 12, 13} = h {0, 1, 4, 5, 9, 10} := by
    have h1 := hinv k145Aut1 k145Aut1_isAut {0, 1, 4, 5, 9, 10}
    rwa [show ({0, 1, 4, 5, 9, 10} : Finset (Fin 14)).map k145Aut1.toEmbedding = {3, 4, 7, 8, 12, 13} by decide] at h1
  have s13 : h {0, 3, 7, 8, 12, 13} = h {0, 1, 5, 6, 7, 10} := by
    have h1 := hinv k145Aut8 k145Aut8_isAut {0, 1, 5, 6, 7, 10}
    rwa [show ({0, 1, 5, 6, 7, 10} : Finset (Fin 14)).map k145Aut8.toEmbedding = {0, 3, 7, 8, 12, 13} by decide] at h1
  have s14 : h {3, 7, 8, 12, 13} = h {0, 1, 5, 6, 10} := by
    have h1 := hinv k145Aut8 k145Aut8_isAut {0, 1, 5, 6, 10}
    rwa [show ({0, 1, 5, 6, 10} : Finset (Fin 14)).map k145Aut8.toEmbedding = {3, 7, 8, 12, 13} by decide] at h1
  have s15 : h {0, 3, 4, 7, 8, 12, 13} = h {0, 1, 2, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 1, 2, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut9.toEmbedding = {0, 3, 4, 7, 8, 12, 13} by decide] at h1
  have s16 : h {2, 3, 4, 7, 8, 12, 13} = h {0, 1, 4, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 1, 4, 5, 6, 9, 10}
    rwa [show ({0, 1, 4, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut9.toEmbedding = {2, 3, 4, 7, 8, 12, 13} by decide] at h1
  have s17 : h {0, 2, 3, 7, 8, 12, 13} = h {0, 1, 2, 4, 5, 9, 10} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 1, 2, 4, 5, 9, 10}
    rwa [show ({0, 1, 2, 4, 5, 9, 10} : Finset (Fin 14)).map k145Aut9.toEmbedding = {0, 2, 3, 7, 8, 12, 13} by decide] at h1
  have s18 : h {2, 3, 7, 8, 12, 13} = h {0, 1, 4, 5, 9, 10} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 4, 5, 9, 10}
    rwa [show ({0, 1, 4, 5, 9, 10} : Finset (Fin 14)).map k145Aut7.toEmbedding = {2, 3, 7, 8, 12, 13} by decide] at h1
  have s19 : h {0, 2, 3, 4, 7, 8, 12, 13} = h {0, 1, 2, 4, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 1, 2, 4, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 4, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut9.toEmbedding = {0, 2, 3, 4, 7, 8, 12, 13} by decide] at h1
  have s20 : h {1, 2, 3, 4, 7, 8, 11, 12, 13} = h {0, 1, 2, 3, 5, 6, 7, 10, 11} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0, 1, 2, 3, 5, 6, 7, 10, 11}
    rwa [show ({0, 1, 2, 3, 5, 6, 7, 10, 11} : Finset (Fin 14)).map k145Aut2.toEmbedding = {1, 2, 3, 4, 7, 8, 11, 12, 13} by decide] at h1
  have c2 : h {0, 1, 2, 3, 6, 7, 8, 11, 12, 13} = h {0, 1, 2, 3, 7, 8, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s21 : h {0, 1, 2, 3, 6, 7, 8, 11, 12, 13} = h {0, 1, 2, 3, 4, 5, 6, 9, 10, 11} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 3, 4, 5, 6, 9, 10, 11}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 9, 10, 11} : Finset (Fin 14)).map k145Aut7.toEmbedding = {0, 1, 2, 3, 6, 7, 8, 11, 12, 13} by decide] at h1
  have s22 : h {1, 2, 3, 7, 8, 11, 12, 13} = h {0, 1, 2, 4, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 4, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 4, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut7.toEmbedding = {1, 2, 3, 7, 8, 11, 12, 13} by decide] at h1
  have c3 : h {0, 1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13} = h {0, 1, 2, 3, 4, 7, 8, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s23 : h {0, 1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13} = h {0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12} : Finset (Fin 14)).map k145Aut2.toEmbedding = {0, 1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13} by decide] at h1
  have s24 : h {1, 2, 3, 4, 6, 7, 8, 11, 12, 13} = h {0, 1, 2, 4, 5, 6, 7, 9, 10, 11} := by
    have h1 := hinv k145Aut10 k145Aut10_isAut {0, 1, 2, 4, 5, 6, 7, 9, 10, 11}
    rwa [show ({0, 1, 2, 4, 5, 6, 7, 9, 10, 11} : Finset (Fin 14)).map k145Aut10.toEmbedding = {1, 2, 3, 4, 6, 7, 8, 11, 12, 13} by decide] at h1
  have s25 : h {1, 2, 3, 6, 7, 8, 11, 12, 13} = h {0, 1, 2, 4, 5, 6, 9, 10, 11} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 4, 5, 6, 9, 10, 11}
    rwa [show ({0, 1, 2, 4, 5, 6, 9, 10, 11} : Finset (Fin 14)).map k145Aut7.toEmbedding = {1, 2, 3, 6, 7, 8, 11, 12, 13} by decide] at h1
  have c4 : h {0, 1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13} = h {0, 1, 2, 3, 4, 6, 7, 8, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s26 : h {1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13} = h {0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12}
    rwa [show ({0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12} : Finset (Fin 14)).map k145Aut2.toEmbedding = {1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13} by decide] at h1
  have c5 : h {0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13} = h {0, 1, 2, 3, 6, 7, 8, 10, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s27 : h {0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13} = h {0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12} : Finset (Fin 14)).map k145Aut7.toEmbedding = {0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13} by decide] at h1
  have s28 : h {1, 2, 3, 6, 7, 8, 10, 11, 12, 13} = h {0, 1, 2, 4, 5, 6, 7, 9, 10, 11} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 4, 5, 6, 7, 9, 10, 11}
    rwa [show ({0, 1, 2, 4, 5, 6, 7, 9, 10, 11} : Finset (Fin 14)).map k145Aut7.toEmbedding = {1, 2, 3, 6, 7, 8, 10, 11, 12, 13} by decide] at h1
  have c6 : h univ = h {0, 1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s29 : h {1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13} = h {0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12} := by
    have h1 := hinv k145Aut10 k145Aut10_isAut {0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12} : Finset (Fin 14)).map k145Aut10.toEmbedding = {1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13} by decide] at h1
  have s30 : h {1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13} = h {0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12} := by
    have h1 := hinv k145Aut11 k145Aut11_isAut {0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12}
    rwa [show ({0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12} : Finset (Fin 14)).map k145Aut11.toEmbedding = {1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13} by decide] at h1
  have c7 : h univ = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s31 : h {2, 3, 12} = h {0, 1, 5} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 5}
    rwa [show ({0, 1, 5} : Finset (Fin 14)).map k145Aut7.toEmbedding = {2, 3, 12} by decide] at h1
  have s32 : h {0, 2, 12} = h {0, 2, 4} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 2, 4}
    rwa [show ({0, 2, 4} : Finset (Fin 14)).map k145Aut9.toEmbedding = {0, 2, 12} by decide] at h1
  have s33 : h {2, 12} = h {0, 4} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 4}
    rwa [show ({0, 4} : Finset (Fin 14)).map k145Aut9.toEmbedding = {2, 12} by decide] at h1
  have s34 : h {0, 2, 3, 12} = h {0, 1, 3, 5} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 3, 5}
    rwa [show ({0, 1, 3, 5} : Finset (Fin 14)).map k145Aut7.toEmbedding = {0, 2, 3, 12} by decide] at h1
  have s35 : h {1, 2, 3, 7, 12} = h {0, 3, 4, 5, 9} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 3, 4, 5, 9}
    rwa [show ({0, 3, 4, 5, 9} : Finset (Fin 14)).map k145Aut9.toEmbedding = {1, 2, 3, 7, 12} by decide] at h1
  have s36 : h {0, 1, 2, 7, 12} = h {0, 1, 2, 4, 9} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 2, 4, 9}
    rwa [show ({0, 1, 2, 4, 9} : Finset (Fin 14)).map k145Aut12.toEmbedding = {0, 1, 2, 7, 12} by decide] at h1
  have s37 : h {1, 2, 7, 12} = h {0, 1, 4, 9} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 4, 9}
    rwa [show ({0, 1, 4, 9} : Finset (Fin 14)).map k145Aut12.toEmbedding = {1, 2, 7, 12} by decide] at h1
  have s38 : h {0, 1, 2, 3, 7, 12} = h {0, 2, 3, 4, 5, 9} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 2, 3, 4, 5, 9}
    rwa [show ({0, 2, 3, 4, 5, 9} : Finset (Fin 14)).map k145Aut9.toEmbedding = {0, 1, 2, 3, 7, 12} by decide] at h1
  have s39 : h {1, 2, 3, 6, 7, 10, 11, 12} = h {0, 1, 2, 5, 6, 7, 10, 11} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 5, 6, 7, 10, 11}
    rwa [show ({0, 1, 2, 5, 6, 7, 10, 11} : Finset (Fin 14)).map k145Aut7.toEmbedding = {1, 2, 3, 6, 7, 10, 11, 12} by decide] at h1
  have s40 : h {0, 1, 2, 6, 7, 10, 11, 12} = h {0, 1, 2, 4, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 2, 4, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 4, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut12.toEmbedding = {0, 1, 2, 6, 7, 10, 11, 12} by decide] at h1
  have s41 : h {1, 2, 6, 7, 10, 11, 12} = h {0, 1, 4, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 4, 5, 6, 9, 10}
    rwa [show ({0, 1, 4, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut12.toEmbedding = {1, 2, 6, 7, 10, 11, 12} by decide] at h1
  have s42 : h {0, 1, 2, 3, 6, 7, 10, 11, 12} = h {0, 1, 2, 3, 5, 6, 7, 10, 11} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 3, 5, 6, 7, 10, 11}
    rwa [show ({0, 1, 2, 3, 5, 6, 7, 10, 11} : Finset (Fin 14)).map k145Aut7.toEmbedding = {0, 1, 2, 3, 6, 7, 10, 11, 12} by decide] at h1
  have s43 : h {1, 2, 3, 5, 6, 7, 10, 11, 12} = h {0, 1, 2, 4, 5, 6, 9, 10, 11} := by
    have h1 := hinv k145Aut13 k145Aut13_isAut {0, 1, 2, 4, 5, 6, 9, 10, 11}
    rwa [show ({0, 1, 2, 4, 5, 6, 9, 10, 11} : Finset (Fin 14)).map k145Aut13.toEmbedding = {1, 2, 3, 5, 6, 7, 10, 11, 12} by decide] at h1
  have s44 : h {0, 1, 2, 5, 6, 7, 10, 11, 12} = h {0, 1, 2, 4, 5, 6, 9, 10, 11} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 2, 4, 5, 6, 9, 10, 11}
    rwa [show ({0, 1, 2, 4, 5, 6, 9, 10, 11} : Finset (Fin 14)).map k145Aut12.toEmbedding = {0, 1, 2, 5, 6, 7, 10, 11, 12} by decide] at h1
  have s45 : h {1, 2, 5, 6, 7, 10, 11, 12} = h {0, 1, 2, 5, 6, 7, 10, 11} := by
    have h1 := hinv k145Aut11 k145Aut11_isAut {0, 1, 2, 5, 6, 7, 10, 11}
    rwa [show ({0, 1, 2, 5, 6, 7, 10, 11} : Finset (Fin 14)).map k145Aut11.toEmbedding = {1, 2, 5, 6, 7, 10, 11, 12} by decide] at h1
  have s46 : h {0, 1, 2, 3, 5, 6, 7, 10, 11, 12} = h {0, 1, 2, 4, 5, 6, 7, 9, 10, 11} := by
    have h1 := hinv k145Aut14 k145Aut14_isAut {0, 1, 2, 4, 5, 6, 7, 9, 10, 11}
    rwa [show ({0, 1, 2, 4, 5, 6, 7, 9, 10, 11} : Finset (Fin 14)).map k145Aut14.toEmbedding = {0, 1, 2, 3, 5, 6, 7, 10, 11, 12} by decide] at h1
  have s47 : h {0, 4, 13} = h {0, 1, 5} := by
    have h1 := hinv k145Aut6 k145Aut6_isAut {0, 1, 5}
    rwa [show ({0, 1, 5} : Finset (Fin 14)).map k145Aut6.toEmbedding = {0, 4, 13} by decide] at h1
  have s48 : h {4, 13} = h {0, 5} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0, 5}
    rwa [show ({0, 5} : Finset (Fin 14)).map k145Aut2.toEmbedding = {4, 13} by decide] at h1
  have s49 : h {1, 2, 3, 7, 11, 12, 13} = h {0, 1, 2, 4, 5, 6, 10} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 4, 5, 6, 10}
    rwa [show ({0, 1, 2, 4, 5, 6, 10} : Finset (Fin 14)).map k145Aut7.toEmbedding = {1, 2, 3, 7, 11, 12, 13} by decide] at h1
  have c8 : h {0, 1, 2, 6, 7, 11, 12, 13} = h {0, 1, 2, 7, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s50 : h {0, 1, 2, 6, 7, 11, 12, 13} = h {0, 1, 2, 3, 4, 5, 9, 10} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 2, 3, 4, 5, 9, 10}
    rwa [show ({0, 1, 2, 3, 4, 5, 9, 10} : Finset (Fin 14)).map k145Aut12.toEmbedding = {0, 1, 2, 6, 7, 11, 12, 13} by decide] at h1
  have s51 : h {1, 2, 7, 11, 12, 13} = h {0, 1, 3, 4, 5, 9} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 3, 4, 5, 9}
    rwa [show ({0, 1, 3, 4, 5, 9} : Finset (Fin 14)).map k145Aut12.toEmbedding = {1, 2, 7, 11, 12, 13} by decide] at h1
  have c9 : h {0, 1, 2, 3, 6, 7, 8, 11, 12, 13} = h {0, 1, 2, 3, 7, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s52 : h {2, 3, 6, 7, 11, 12, 13} = h {0, 1, 2, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 1, 2, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut15.toEmbedding = {2, 3, 6, 7, 11, 12, 13} by decide] at h1
  have s53 : h {0, 2, 6, 7, 11, 12, 13} = h {0, 1, 5, 6, 7, 8, 10} := by
    have h1 := hinv k145Aut16 k145Aut16_isAut {0, 1, 5, 6, 7, 8, 10}
    rwa [show ({0, 1, 5, 6, 7, 8, 10} : Finset (Fin 14)).map k145Aut16.toEmbedding = {0, 2, 6, 7, 11, 12, 13} by decide] at h1
  have s54 : h {2, 6, 7, 11, 12, 13} = h {0, 1, 5, 6, 7, 10} := by
    have h1 := hinv k145Aut16 k145Aut16_isAut {0, 1, 5, 6, 7, 10}
    rwa [show ({0, 1, 5, 6, 7, 10} : Finset (Fin 14)).map k145Aut16.toEmbedding = {2, 6, 7, 11, 12, 13} by decide] at h1
  have s55 : h {0, 2, 3, 6, 7, 11, 12, 13} = h {0, 1, 2, 3, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 1, 2, 3, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 3, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut15.toEmbedding = {0, 2, 3, 6, 7, 11, 12, 13} by decide] at h1
  have s56 : h {1, 2, 3, 6, 7, 11, 12, 13} = h {0, 1, 2, 4, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 1, 2, 4, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 4, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut15.toEmbedding = {1, 2, 3, 6, 7, 11, 12, 13} by decide] at h1
  have s57 : h {1, 2, 6, 7, 11, 12, 13} = h {0, 1, 2, 4, 5, 9, 10} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 1, 2, 4, 5, 9, 10}
    rwa [show ({0, 1, 2, 4, 5, 9, 10} : Finset (Fin 14)).map k145Aut15.toEmbedding = {1, 2, 6, 7, 11, 12, 13} by decide] at h1
  have c10 : h {0, 1, 2, 3, 6, 7, 8, 11, 12, 13} = h {0, 1, 2, 3, 6, 7, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s58 : h {1, 2, 6, 11} = h {0, 4, 5, 9} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 4, 5, 9}
    rwa [show ({0, 4, 5, 9} : Finset (Fin 14)).map k145Aut15.toEmbedding = {1, 2, 6, 11} by decide] at h1
  have s59 : h {0, 1, 6, 11} = h {0, 1, 4, 9} := by
    have h1 := hinv k145Aut17 k145Aut17_isAut {0, 1, 4, 9}
    rwa [show ({0, 1, 4, 9} : Finset (Fin 14)).map k145Aut17.toEmbedding = {0, 1, 6, 11} by decide] at h1
  have s60 : h {1, 6, 11} = h {0, 4, 9} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 4, 9}
    rwa [show ({0, 4, 9} : Finset (Fin 14)).map k145Aut15.toEmbedding = {1, 6, 11} by decide] at h1
  have s61 : h {0, 1, 2, 6, 11} = h {0, 3, 4, 5, 9} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 3, 4, 5, 9}
    rwa [show ({0, 3, 4, 5, 9} : Finset (Fin 14)).map k145Aut15.toEmbedding = {0, 1, 2, 6, 11} by decide] at h1
  have s62 : h {1, 2, 6, 10, 11} = h {0, 1, 5, 6, 10} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 5, 6, 10}
    rwa [show ({0, 1, 5, 6, 10} : Finset (Fin 14)).map k145Aut12.toEmbedding = {1, 2, 6, 10, 11} by decide] at h1
  have s63 : h {0, 1, 6, 10, 11} = h {0, 1, 4, 5, 9} := by
    have h1 := hinv k145Aut17 k145Aut17_isAut {0, 1, 4, 5, 9}
    rwa [show ({0, 1, 4, 5, 9} : Finset (Fin 14)).map k145Aut17.toEmbedding = {0, 1, 6, 10, 11} by decide] at h1
  have s64 : h {1, 6, 10, 11} = h {0, 4, 5, 9} := by
    have h1 := hinv k145Aut16 k145Aut16_isAut {0, 4, 5, 9}
    rwa [show ({0, 4, 5, 9} : Finset (Fin 14)).map k145Aut16.toEmbedding = {1, 6, 10, 11} by decide] at h1
  have s65 : h {0, 1, 2, 6, 10, 11} = h {0, 1, 2, 5, 6, 10} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 2, 5, 6, 10}
    rwa [show ({0, 1, 2, 5, 6, 10} : Finset (Fin 14)).map k145Aut12.toEmbedding = {0, 1, 2, 6, 10, 11} by decide] at h1
  have s66 : h {1, 2, 6, 10, 11, 12} = h {0, 1, 2, 5, 6, 10} := by
    have h1 := hinv k145Aut18 k145Aut18_isAut {0, 1, 2, 5, 6, 10}
    rwa [show ({0, 1, 2, 5, 6, 10} : Finset (Fin 14)).map k145Aut18.toEmbedding = {1, 2, 6, 10, 11, 12} by decide] at h1
  have s67 : h {0, 1, 6, 10, 11, 12} = h {0, 1, 3, 4, 5, 9} := by
    have h1 := hinv k145Aut17 k145Aut17_isAut {0, 1, 3, 4, 5, 9}
    rwa [show ({0, 1, 3, 4, 5, 9} : Finset (Fin 14)).map k145Aut17.toEmbedding = {0, 1, 6, 10, 11, 12} by decide] at h1
  have s68 : h {1, 6, 10, 11, 12} = h {0, 3, 4, 5, 9} := by
    have h1 := hinv k145Aut17 k145Aut17_isAut {0, 3, 4, 5, 9}
    rwa [show ({0, 3, 4, 5, 9} : Finset (Fin 14)).map k145Aut17.toEmbedding = {1, 6, 10, 11, 12} by decide] at h1
  have s69 : h {0, 1, 2, 6, 10, 11, 12} = h {0, 1, 2, 4, 5, 6, 10} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 2, 4, 5, 6, 10}
    rwa [show ({0, 1, 2, 4, 5, 6, 10} : Finset (Fin 14)).map k145Aut12.toEmbedding = {0, 1, 2, 6, 10, 11, 12} by decide] at h1
  have s70 : h {2, 12, 13} = h {0, 1, 4} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 1, 4}
    rwa [show ({0, 1, 4} : Finset (Fin 14)).map k145Aut9.toEmbedding = {2, 12, 13} by decide] at h1
  have s71 : h {0, 12, 13} = h {0, 1, 2} := by
    have h1 := hinv k145Aut4 k145Aut4_isAut {0, 1, 2}
    rwa [show ({0, 1, 2} : Finset (Fin 14)).map k145Aut4.toEmbedding = {0, 12, 13} by decide] at h1
  have s72 : h {12, 13} = h {0, 1} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 1}
    rwa [show ({0, 1} : Finset (Fin 14)).map k145Aut9.toEmbedding = {12, 13} by decide] at h1
  have s73 : h {0, 2, 12, 13} = h {0, 1, 2, 4} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 1, 2, 4}
    rwa [show ({0, 1, 2, 4} : Finset (Fin 14)).map k145Aut9.toEmbedding = {0, 2, 12, 13} by decide] at h1
  have s74 : h {1, 2, 5, 6, 10, 11, 12, 13} = h {0, 1, 2, 3, 5, 6, 9, 10} := by
    have h1 := hinv k145Aut18 k145Aut18_isAut {0, 1, 2, 3, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 3, 5, 6, 9, 10} : Finset (Fin 14)).map k145Aut18.toEmbedding = {1, 2, 5, 6, 10, 11, 12, 13} by decide] at h1
  have s75 : h {0, 1, 5, 6, 10, 11, 12, 13} = h {0, 1, 2, 3, 4, 5, 9, 10} := by
    have h1 := hinv k145Aut17 k145Aut17_isAut {0, 1, 2, 3, 4, 5, 9, 10}
    rwa [show ({0, 1, 2, 3, 4, 5, 9, 10} : Finset (Fin 14)).map k145Aut17.toEmbedding = {0, 1, 5, 6, 10, 11, 12, 13} by decide] at h1
  have s76 : h {1, 5, 6, 10, 11, 12, 13} = h {0, 1, 5, 6, 7, 8, 10} := by
    have h1 := hinv k145Aut11 k145Aut11_isAut {0, 1, 5, 6, 7, 8, 10}
    rwa [show ({0, 1, 5, 6, 7, 8, 10} : Finset (Fin 14)).map k145Aut11.toEmbedding = {1, 5, 6, 10, 11, 12, 13} by decide] at h1
  have c11 : h {0, 1, 2, 5, 6, 7, 10, 11, 12, 13} = h {0, 1, 2, 5, 6, 10, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s77 : h {0, 1, 2, 5, 6, 7, 10, 11, 12, 13} = h {0, 1, 2, 3, 4, 5, 6, 9, 10, 11} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 2, 3, 4, 5, 6, 9, 10, 11}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 9, 10, 11} : Finset (Fin 14)).map k145Aut12.toEmbedding = {0, 1, 2, 5, 6, 7, 10, 11, 12, 13} by decide] at h1
  have s78 : h {1, 10} = h {0, 5} := by
    have h1 := hinv k145Aut17 k145Aut17_isAut {0, 5}
    rwa [show ({0, 5} : Finset (Fin 14)).map k145Aut17.toEmbedding = {1, 10} by decide] at h1
  have s79 : h {0, 10} = h {0, 4} := by
    have h1 := hinv k145Aut4 k145Aut4_isAut {0, 4}
    rwa [show ({0, 4} : Finset (Fin 14)).map k145Aut4.toEmbedding = {0, 10} by decide] at h1
  have s80 : h {0, 1, 10} = h {0, 1, 5} := by
    have h1 := hinv k145Aut17 k145Aut17_isAut {0, 1, 5}
    rwa [show ({0, 1, 5} : Finset (Fin 14)).map k145Aut17.toEmbedding = {0, 1, 10} by decide] at h1
  have s81 : h {1, 5, 10, 11} = h {0, 1, 5, 9} := by
    have h1 := hinv k145Aut18 k145Aut18_isAut {0, 1, 5, 9}
    rwa [show ({0, 1, 5, 9} : Finset (Fin 14)).map k145Aut18.toEmbedding = {1, 5, 10, 11} by decide] at h1
  have s82 : h {0, 5, 10, 11} = h {0, 1, 4, 9} := by
    have h1 := hinv k145Aut18 k145Aut18_isAut {0, 1, 4, 9}
    rwa [show ({0, 1, 4, 9} : Finset (Fin 14)).map k145Aut18.toEmbedding = {0, 5, 10, 11} by decide] at h1
  have s83 : h {5, 10, 11} = h {0, 1, 6} := by
    have h1 := hinv k145Aut19 k145Aut19_isAut {0, 1, 6}
    rwa [show ({0, 1, 6} : Finset (Fin 14)).map k145Aut19.toEmbedding = {5, 10, 11} by decide] at h1
  have s84 : h {0, 1, 5, 10, 11} = h {0, 1, 4, 5, 9} := by
    have h1 := hinv k145Aut18 k145Aut18_isAut {0, 1, 4, 5, 9}
    rwa [show ({0, 1, 4, 5, 9} : Finset (Fin 14)).map k145Aut18.toEmbedding = {0, 1, 5, 10, 11} by decide] at h1
  have s85 : h {1, 12} = h {0, 3} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 3}
    rwa [show ({0, 3} : Finset (Fin 14)).map k145Aut9.toEmbedding = {1, 12} by decide] at h1
  have s86 : h {0, 12} = h {0, 2} := by
    have h1 := hinv k145Aut4 k145Aut4_isAut {0, 2}
    rwa [show ({0, 2} : Finset (Fin 14)).map k145Aut4.toEmbedding = {0, 12} by decide] at h1
  have s87 : h {0, 1, 12} = h {0, 1, 3} := by
    have h1 := hinv k145Aut17 k145Aut17_isAut {0, 1, 3}
    rwa [show ({0, 1, 3} : Finset (Fin 14)).map k145Aut17.toEmbedding = {0, 1, 12} by decide] at h1
  have s88 : h {1, 2, 13} = h {0, 1, 3} := by
    have h1 := hinv k145Aut12 k145Aut12_isAut {0, 1, 3}
    rwa [show ({0, 1, 3} : Finset (Fin 14)).map k145Aut12.toEmbedding = {1, 2, 13} by decide] at h1
  have s89 : h {0, 2, 13} = h {0, 1, 3} := by
    have h1 := hinv k145Aut6 k145Aut6_isAut {0, 1, 3}
    rwa [show ({0, 1, 3} : Finset (Fin 14)).map k145Aut6.toEmbedding = {0, 2, 13} by decide] at h1
  have s90 : h {2, 13} = h {0, 3} := by
    have h1 := hinv k145Aut6 k145Aut6_isAut {0, 3}
    rwa [show ({0, 3} : Finset (Fin 14)).map k145Aut6.toEmbedding = {2, 13} by decide] at h1
  have s91 : h {0, 1, 2, 13} = h {0, 1, 2, 3} := by
    have h1 := hinv k145Aut6 k145Aut6_isAut {0, 1, 2, 3}
    rwa [show ({0, 1, 2, 3} : Finset (Fin 14)).map k145Aut6.toEmbedding = {0, 1, 2, 13} by decide] at h1
  have s92 : h {1, 3, 4, 13} = h {0, 1, 3, 5} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0, 1, 3, 5}
    rwa [show ({0, 1, 3, 5} : Finset (Fin 14)).map k145Aut2.toEmbedding = {1, 3, 4, 13} by decide] at h1
  have s93 : h {0, 3, 4, 13} = h {0, 1, 4, 5} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0, 1, 4, 5}
    rwa [show ({0, 1, 4, 5} : Finset (Fin 14)).map k145Aut2.toEmbedding = {0, 3, 4, 13} by decide] at h1
  have s94 : h {3, 4, 13} = h {0, 1, 5} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0, 1, 5}
    rwa [show ({0, 1, 5} : Finset (Fin 14)).map k145Aut2.toEmbedding = {3, 4, 13} by decide] at h1
  have s95 : h {0, 1, 3, 4, 13} = h {0, 1, 2, 4, 5} := by
    have h1 := hinv k145Aut6 k145Aut6_isAut {0, 1, 2, 4, 5}
    rwa [show ({0, 1, 2, 4, 5} : Finset (Fin 14)).map k145Aut6.toEmbedding = {0, 1, 3, 4, 13} by decide] at h1
  have s96 : h {1, 2, 3, 12, 13} = h {0, 1, 2, 4, 5} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 4, 5}
    rwa [show ({0, 1, 2, 4, 5} : Finset (Fin 14)).map k145Aut7.toEmbedding = {1, 2, 3, 12, 13} by decide] at h1
  have s97 : h {0, 2, 3, 12, 13} = h {0, 1, 2, 4, 5} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0, 1, 2, 4, 5}
    rwa [show ({0, 1, 2, 4, 5} : Finset (Fin 14)).map k145Aut9.toEmbedding = {0, 2, 3, 12, 13} by decide] at h1
  have s98 : h {2, 3, 12, 13} = h {0, 1, 4, 5} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 4, 5}
    rwa [show ({0, 1, 4, 5} : Finset (Fin 14)).map k145Aut7.toEmbedding = {2, 3, 12, 13} by decide] at h1
  have c12 : h {0, 1, 2, 3, 7, 8, 12, 13} = h {0, 1, 2, 3, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s99 : h {0, 1, 2, 3, 7, 8, 12, 13} = h {0, 1, 2, 3, 4, 5, 9, 10} := by
    have h1 := hinv k145Aut7 k145Aut7_isAut {0, 1, 2, 3, 4, 5, 9, 10}
    rwa [show ({0, 1, 2, 3, 4, 5, 9, 10} : Finset (Fin 14)).map k145Aut7.toEmbedding = {0, 1, 2, 3, 7, 8, 12, 13} by decide] at h1
  have s100 : h {1, 11, 12, 13} = h {0, 1, 2, 4} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 1, 2, 4}
    rwa [show ({0, 1, 2, 4} : Finset (Fin 14)).map k145Aut15.toEmbedding = {1, 11, 12, 13} by decide] at h1
  have s101 : h {0, 11, 12, 13} = h {0, 1, 2, 3} := by
    have h1 := hinv k145Aut4 k145Aut4_isAut {0, 1, 2, 3}
    rwa [show ({0, 1, 2, 3} : Finset (Fin 14)).map k145Aut4.toEmbedding = {0, 11, 12, 13} by decide] at h1
  have s102 : h {11, 12, 13} = h {0, 1, 2} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 1, 2}
    rwa [show ({0, 1, 2} : Finset (Fin 14)).map k145Aut15.toEmbedding = {11, 12, 13} by decide] at h1
  have c13 : h {0, 1, 6, 11, 12, 13} = h {0, 1, 11, 12, 13} := hh.eq_of_closure hv (by decide) (by decide)
  have s103 : h {0, 1, 6, 11, 12, 13} = h {0, 1, 2, 3, 4, 9} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0, 1, 2, 3, 4, 9}
    rwa [show ({0, 1, 2, 3, 4, 9} : Finset (Fin 14)).map k145Aut15.toEmbedding = {0, 1, 6, 11, 12, 13} by decide] at h1
  have s104 : h {13} = h {0} := by
    have h1 := hinv k145Aut6 k145Aut6_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut6.toEmbedding = {13} by decide] at h1
  have s105 : h {12} = h {0} := by
    have h1 := hinv k145Aut9 k145Aut9_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut9.toEmbedding = {12} by decide] at h1
  have s106 : h {11} = h {0} := by
    have h1 := hinv k145Aut15 k145Aut15_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut15.toEmbedding = {11} by decide] at h1
  have s107 : h {10} = h {0} := by
    have h1 := hinv k145Aut18 k145Aut18_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut18.toEmbedding = {10} by decide] at h1
  have s108 : h {9} = h {0} := by
    have h1 := hinv k145Aut20 k145Aut20_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut20.toEmbedding = {9} by decide] at h1
  have s109 : h {8} = h {0} := by
    have h1 := hinv k145Aut5 k145Aut5_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut5.toEmbedding = {8} by decide] at h1
  have s110 : h {7} = h {0} := by
    have h1 := hinv k145Aut8 k145Aut8_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut8.toEmbedding = {7} by decide] at h1
  have s111 : h {6} = h {0} := by
    have h1 := hinv k145Aut16 k145Aut16_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut16.toEmbedding = {6} by decide] at h1
  have s112 : h {5} = h {0} := by
    have h1 := hinv k145Aut11 k145Aut11_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut11.toEmbedding = {5} by decide] at h1
  have s113 : h {4} = h {0} := by
    have h1 := hinv k145Aut2 k145Aut2_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut2.toEmbedding = {4} by decide] at h1
  have s114 : h {3} = h {0} := by
    have h1 := hinv k145Aut1 k145Aut1_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut1.toEmbedding = {3} by decide] at h1
  have s115 : h {2} = h {0} := by
    have h1 := hinv k145Aut0 k145Aut0_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut0.toEmbedding = {2} by decide] at h1
  have s116 : h {1} = h {0} := by
    have h1 := hinv k145Aut13 k145Aut13_isAut {0}
    rwa [show ({0} : Finset (Fin 14)).map k145Aut13.toEmbedding = {1} by decide] at h1
  have h0 := hh.empty
  simp only [sum_fin_14]
  linear_combination (1 : ℝ) * e1 + (1 / 2 : ℝ) * e2 + (1 : ℝ) * e3 + (1 : ℝ) * e4 + (2 : ℝ) * e5 +
    (1 / 2 : ℝ) * e6 + (1 : ℝ) * e7 + (1 / 2 : ℝ) * e8 + (1 : ℝ) * e9 + (1 / 2 : ℝ) * e10 +
    (1 / 2 : ℝ) * e11 + (1 / 2 : ℝ) * e12 + (4 : ℝ) * e13 + (1 / 2 : ℝ) * e14 + (1 / 2 : ℝ) * e15 +
    (1 / 2 : ℝ) * e16 + (1 / 2 : ℝ) * e17 + (1 / 2 : ℝ) * e18 + (1 / 2 : ℝ) * e19 + (1 : ℝ) * e20 +
    (1 : ℝ) * e21 + (2 : ℝ) * e22 + (1 / 2 : ℝ) * e23 + (1 / 2 : ℝ) * e24 + (1 : ℝ) * e25 +
    (1 / 2 : ℝ) * e26 + (1 / 2 : ℝ) * e27 + (1 / 2 : ℝ) * e28 + (1 : ℝ) * e29 + (1 / 2 : ℝ) * e30 +
    (1 : ℝ) * e31 + (1 : ℝ) * e32 + (1 : ℝ) * c1 + (-1 / 2 : ℝ) * c2 + (1 / 2 : ℝ) * c3 +
    (1 : ℝ) * c4 + (-1 / 2 : ℝ) * c5 + (-1 / 2 : ℝ) * c8 + (1 / 2 : ℝ) * c9 + (1 / 2 : ℝ) * c10 +
    (1 / 2 : ℝ) * c11 + (1 / 2 : ℝ) * c12 + (1 : ℝ) * c13 + (1 : ℝ) * s1 + (1 : ℝ) * s2 +
    (-1 : ℝ) * s3 + (1 / 2 : ℝ) * s4 + (1 / 2 : ℝ) * s5 + (-1 / 2 : ℝ) * s6 + (-1 / 2 : ℝ) * s7 +
    (1 : ℝ) * s8 + (1 : ℝ) * s9 + (-1 : ℝ) * s10 + (-1 : ℝ) * s11 + (1 / 2 : ℝ) * s12 +
    (1 / 2 : ℝ) * s13 + (-1 / 2 : ℝ) * s14 + (-1 / 2 : ℝ) * s15 + (1 / 2 : ℝ) * s16 +
    (1 / 2 : ℝ) * s17 + (-1 / 2 : ℝ) * s18 + (-1 / 2 : ℝ) * s19 + (1 / 2 : ℝ) * s20 +
    (1 / 2 : ℝ) * s21 + (-1 / 2 : ℝ) * s22 + (-3 / 2 : ℝ) * s23 + (1 : ℝ) * s24 + (-1 : ℝ) * s25 +
    (1 / 2 : ℝ) * s26 + (1 : ℝ) * s27 + (-1 / 2 : ℝ) * s28 + (1 / 2 : ℝ) * c6 + (1 / 2 : ℝ) * s29 +
    (-1 / 2 : ℝ) * s30 + (1 / 2 : ℝ) * c7 + (1 : ℝ) * s31 + (1 : ℝ) * s32 + (-1 : ℝ) * s33 +
    (-1 : ℝ) * s34 + (1 : ℝ) * s35 + (1 : ℝ) * s36 + (-1 : ℝ) * s37 + (-1 : ℝ) * s38 +
    (1 / 2 : ℝ) * s39 + (1 / 2 : ℝ) * s40 + (-1 / 2 : ℝ) * s41 + (-1 / 2 : ℝ) * s42 +
    (1 / 2 : ℝ) * s43 + (1 / 2 : ℝ) * s44 + (-1 / 2 : ℝ) * s45 + (-1 / 2 : ℝ) * s46 +
    (1 / 2 : ℝ) * s47 + (-1 / 2 : ℝ) * s48 + (1 / 2 : ℝ) * s49 + (1 : ℝ) * s50 +
    (-1 / 2 : ℝ) * s51 + (1 / 2 : ℝ) * s52 + (1 / 2 : ℝ) * s53 + (-1 / 2 : ℝ) * s54 +
    (-1 / 2 : ℝ) * s55 + (1 / 2 : ℝ) * s56 + (-1 / 2 : ℝ) * s57 + (1 / 2 : ℝ) * s58 +
    (1 / 2 : ℝ) * s59 + (-1 / 2 : ℝ) * s60 + (-1 / 2 : ℝ) * s61 + (1 / 2 : ℝ) * s62 +
    (1 / 2 : ℝ) * s63 + (-1 / 2 : ℝ) * s64 + (-1 / 2 : ℝ) * s65 + (1 / 2 : ℝ) * s66 +
    (1 / 2 : ℝ) * s67 + (-1 / 2 : ℝ) * s68 + (-1 / 2 : ℝ) * s69 + (1 : ℝ) * s70 + (1 : ℝ) * s71 +
    (-1 : ℝ) * s72 + (-1 : ℝ) * s73 + (1 / 2 : ℝ) * s74 + (1 / 2 : ℝ) * s75 + (-1 / 2 : ℝ) * s76 +
    (-1 / 2 : ℝ) * s77 + (1 : ℝ) * s78 + (1 : ℝ) * s79 + (-1 : ℝ) * s80 + (1 / 2 : ℝ) * s81 +
    (1 / 2 : ℝ) * s82 + (-1 / 2 : ℝ) * s83 + (-1 / 2 : ℝ) * s84 + (2 : ℝ) * s85 + (2 : ℝ) * s86 +
    (-2 : ℝ) * s87 + (1 : ℝ) * s88 + (1 : ℝ) * s89 + (-1 : ℝ) * s90 + (-1 : ℝ) * s91 +
    (1 : ℝ) * s92 + (1 / 2 : ℝ) * s93 + (-1 / 2 : ℝ) * s94 + (-1 : ℝ) * s95 + (1 / 2 : ℝ) * s96 +
    (1 / 2 : ℝ) * s97 + (-1 / 2 : ℝ) * s98 + (-1 / 2 : ℝ) * s99 + (1 : ℝ) * s100 + (1 : ℝ) * s101 +
    (-1 : ℝ) * s102 + (-1 : ℝ) * s103 + (-1 / 2 : ℝ) * s104 + (-5 / 2 : ℝ) * s105 +
    (-1 / 2 : ℝ) * s106 + (-3 / 2 : ℝ) * s107 + (-1 / 2 : ℝ) * s108 + (-1 / 2 : ℝ) * s109 +
    (-1 / 2 : ℝ) * s110 + (-1 / 2 : ℝ) * s111 + (-1 / 2 : ℝ) * s112 + (-1 / 2 : ℝ) * s113 +
    (1 / 2 : ℝ) * s114 + (5 / 2 : ℝ) * s115 + (-1 / 2 : ℝ) * s116 + (-6 : ℝ) * h0

theorem rateBound_circularClique_14_5 : RateBound (nbhd (circularClique 14 5)) (1 / 2) := by
  rw [nbhd_circularClique_14_5]
  exact rateBound_k145

/-! ## Homomorphisms between circular cliques (Bondy–Hell) and odd cycles -/

/-- Adjacency in `K_{p/q}` between vertices `i < j`. -/
theorem circularClique_adj_of_lt {p q : ℕ} {i j : Fin p} (hij : i.val < j.val) :
    (circularClique p q).Adj i j ↔ q ≤ j.val - i.val ∧ j.val - i.val ≤ p - q := by
  have hj := j.isLt
  have h1 : ((j - i : Fin p) : ℕ) = j.val - i.val := Fin.coe_sub_iff_le.mpr (le_of_lt hij)
  have h2 : ((i - j : Fin p) : ℕ) = p + i.val - j.val := Fin.coe_sub_iff_lt.mpr hij
  simp only [circularClique, SimpleGraph.fromRel_adj, ne_eq, h1, h2]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · omega
  · intro h
    exact ⟨fun e => by rw [e] at hij; exact lt_irrefl _ hij, Or.inl h⟩

/-- The Bondy–Hell map `i ↦ ⌊p' i / p⌋` from `Fin p` to `Fin p'`. -/
def bondyHell (p p' : ℕ) (hp' : 0 < p') (i : Fin p) : Fin p' :=
  ⟨p' * i.val / p, by
    have hi := i.isLt
    have hp : 0 < p := by omega
    rw [Nat.div_lt_iff_lt_mul hp]
    nlinarith⟩

/-- The two inequalities behind the Bondy–Hell map. -/
theorem bondyHell_bounds {p q p' q' a d : ℕ} (hp : 0 < p) (h : p * q' ≤ p' * q)
    (hlo : q ≤ d) (hhi : d ≤ p - q) :
    p' * a / p + q' ≤ p' * (a + d) / p ∧ p' * (a + d) / p ≤ p' * a / p + (p' - q') := by
  obtain ⟨e, rfl⟩ : ∃ e, p = q + e := ⟨p - q, by omega⟩
  have hde : d ≤ e := by omega
  have hqe : q ≤ e := by omega
  constructor
  · have h1 : p' * a + (q + e) * q' ≤ p' * (a + d) := by
      nlinarith [Nat.mul_le_mul_left p' hlo]
    calc p' * a / (q + e) + q' = (p' * a + (q + e) * q') / (q + e) :=
          (Nat.add_mul_div_left _ _ hp).symm
      _ ≤ p' * (a + d) / (q + e) := Nat.div_le_div_right h1
  · have hq'p' : q' ≤ p' := by nlinarith
    obtain ⟨e', rfl⟩ : ∃ e', p' = q' + e' := ⟨p' - q', by omega⟩
    have h1 : (q' + e') * (a + d) ≤ (q' + e') * a + (q + e) * e' := by
      nlinarith [Nat.mul_le_mul_left (q' + e') hde]
    have he' : q' + e' - q' = e' := by omega
    rw [he']
    calc (q' + e') * (a + d) / (q + e) ≤ ((q' + e') * a + (q + e) * e') / (q + e) :=
          Nat.div_le_div_right h1
      _ = (q' + e') * a / (q + e) + e' := Nat.add_mul_div_left _ _ hp

theorem bondyHell_adj_of_lt {p q p' q' : ℕ} (hp' : 0 < p') (hq' : 0 < q') (h : p * q' ≤ p' * q)
    {i j : Fin p} (hij : i.val < j.val) (hadj : (circularClique p q).Adj i j) :
    (circularClique p' q').Adj (bondyHell p p' hp' i) (bondyHell p p' hp' j) := by
  rw [circularClique_adj_of_lt hij] at hadj
  have hp : 0 < p := by have := j.isLt; omega
  obtain ⟨d, hd⟩ : ∃ d, j.val = i.val + d := ⟨j.val - i.val, by omega⟩
  have hb := bondyHell_bounds (a := i.val) hp h (d := d) (by omega) (by omega)
  have hfi : (bondyHell p p' hp' i).val = p' * i.val / p := rfl
  have hfj : (bondyHell p p' hp' j).val = p' * (i.val + d) / p := by
    show p' * j.val / p = _
    rw [hd]
  have hlt : (bondyHell p p' hp' i).val < (bondyHell p p' hp' j).val := by
    rw [hfi, hfj]; omega
  rw [circularClique_adj_of_lt hlt, hfi, hfj]
  omega

/-- **Bondy–Hell.** If `p/q ≤ p'/q'` (with `q' ≥ 1`), then `i ↦ ⌊p' i / p⌋` is a homomorphism
`K_{p/q} → K_{p'/q'}`. -/
def circularCliqueHom (p q p' q' : ℕ) (hp' : 0 < p') (hq' : 0 < q') (h : p * q' ≤ p' * q) :
    circularClique p q →g circularClique p' q' where
  toFun := bondyHell p p' hp'
  map_rel' := by
    intro i j hadj
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact bondyHell_adj_of_lt hp' hq' h hlt hadj
    · exact absurd (Fin.ext heq) (SimpleGraph.ne_of_adj _ hadj)
    · exact (bondyHell_adj_of_lt hp' hq' h hgt hadj.symm).symm

/-- **Every circular clique `K_{p/q}` with `p/q ≤ 14/5` is good.** -/
theorem rateBound_circularClique_of_le {p q : ℕ} (h : p * 5 ≤ 14 * q) :
    RateBound (nbhd (circularClique p q)) (1 / 2) :=
  RateBound.of_graphHom (by norm_num) (circularCliqueHom p q 14 5 (by norm_num) (by norm_num) h)
    rateBound_circularClique_14_5

/-- The element `k` of `ℤ/(2k+1)`. -/
def kElt (k : ℕ) : Fin (2 * k + 1) := ⟨k, by omega⟩

/-- Multiplying by `k` in `ℤ/(2k+1)` turns a difference `1` into a difference `k`. -/
theorem kElt_mul_sub_val {k : ℕ} (hk : 1 ≤ k) {a b : Fin (2 * k + 1)}
    (h : (b - a).val = 1) : (kElt k * b - kElt k * a).val = k := by
  have h1 : b - a = 1 := by
    apply Fin.ext
    rw [h, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  rw [← mul_sub, h1, mul_one]
  rfl

/-- `C_{2k+1} → K_{(2k+1)/k}`, `i ↦ k i`. -/
def cycleToCircularClique (k : ℕ) (hk : 1 ≤ k) :
    SimpleGraph.cycleGraph (2 * k + 1) →g circularClique (2 * k + 1) k where
  toFun u := kElt k * u
  map_rel' := by
    intro u v huv
    rw [SimpleGraph.cycleGraph_adj'] at huv
    simp only [circularClique, SimpleGraph.fromRel_adj, ne_eq]
    rcases huv with h | h
    · have hk' := kElt_mul_sub_val hk h
      refine ⟨fun e => ?_, Or.inr ⟨by omega, by omega⟩⟩
      rw [e, sub_self, Fin.val_zero] at hk'
      omega
    · have hk' := kElt_mul_sub_val hk h
      refine ⟨fun e => ?_, Or.inl ⟨by omega, by omega⟩⟩
      rw [e, sub_self, Fin.val_zero] at hk'
      omega

/-- **Every odd cycle of length at least 5 is good.** -/
theorem rateBound_cycleGraph_odd {k : ℕ} (hk : 2 ≤ k) :
    RateBound (nbhd (SimpleGraph.cycleGraph (2 * k + 1))) (1 / 2) :=
  RateBound.of_graphHom (by norm_num)
    ((circularCliqueHom (2 * k + 1) k 14 5 (by norm_num) (by norm_num) (by omega)).comp
      (cycleToCircularClique k (by omega)))
    rateBound_circularClique_14_5

end MotionDepthCodes
