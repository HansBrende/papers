import MotionDepthCodes.Clebsch
import MotionDepthCodes.FinSums
import MotionDepthCodes.Symmetry

/-!
# `gn(Clebsch) = 10`

Every valid polymatroid on the Clebsch graph satisfies `h(V) ≤ (5/8) Σ_v h(v)`.
The polymatroid is first symmetrized over the automorphism group (order 1920).
The certificate then combines 54 orbit rows of elemental inequalities, closure
equalities and invariance equalities, with exact rational coefficients checked
by `linear_combination`. The generator is `tools/certificates.py`.

With the binary code of `MotionDepthCodes.Clebsch` this gives the exact value:
over any alphabet a storage code on the Clebsch graph has at most `|α|^10`
codewords, and a binary code attains `2^10`. The upper bound also shows that this
code is all of `ker (I + A)` over `GF(2)`, so `I + A` has rank `6` there.
-/

namespace MotionDepthCodes

open Finset
open scoped BigOperators
set_option autoImplicit false

/-- An automorphism used by the certificate. -/
def clebschAut0 : Equiv.Perm (Fin 16) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut0_isAut : IsAut clebschNbhd clebschAut0 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut1 : Equiv.Perm (Fin 16) where
  toFun := ![1, 3, 14, 12, 0, 2, 15, 13, 5, 7, 10, 8, 4, 6, 11, 9]
  invFun := ![4, 0, 5, 1, 12, 8, 13, 9, 11, 15, 10, 14, 3, 7, 2, 6]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut1_isAut : IsAut clebschNbhd clebschAut1 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut2 : Equiv.Perm (Fin 16) where
  toFun := ![1, 0, 14, 15, 3, 2, 12, 13, 5, 4, 10, 11, 7, 6, 8, 9]
  invFun := ![1, 0, 5, 4, 9, 8, 13, 12, 14, 15, 10, 11, 6, 7, 2, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut2_isAut : IsAut clebschNbhd clebschAut2 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut3 : Equiv.Perm (Fin 16) where
  toFun := ![1, 3, 9, 11, 14, 12, 6, 4, 0, 2, 8, 10, 15, 13, 7, 5]
  invFun := ![8, 0, 9, 1, 7, 15, 6, 14, 10, 2, 11, 3, 5, 13, 4, 12]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut3_isAut : IsAut clebschNbhd clebschAut3 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut4 : Equiv.Perm (Fin 16) where
  toFun := ![1, 0, 9, 8, 14, 15, 6, 7, 3, 2, 11, 10, 12, 13, 4, 5]
  invFun := ![1, 0, 9, 8, 14, 15, 6, 7, 3, 2, 11, 10, 12, 13, 4, 5]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut4_isAut : IsAut clebschNbhd clebschAut4 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut5 : Equiv.Perm (Fin 16) where
  toFun := ![1, 9, 14, 6, 0, 8, 15, 7, 3, 11, 12, 4, 2, 10, 13, 5]
  invFun := ![4, 0, 12, 8, 11, 15, 3, 7, 5, 1, 13, 9, 10, 14, 2, 6]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut5_isAut : IsAut clebschNbhd clebschAut5 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut6 : Equiv.Perm (Fin 16) where
  toFun := ![1, 3, 5, 7, 9, 11, 13, 15, 14, 12, 10, 8, 6, 4, 2, 0]
  invFun := ![15, 0, 14, 1, 13, 2, 12, 3, 11, 4, 10, 5, 9, 6, 8, 7]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut6_isAut : IsAut clebschNbhd clebschAut6 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut7 : Equiv.Perm (Fin 16) where
  toFun := ![1, 0, 5, 4, 9, 8, 13, 12, 14, 15, 10, 11, 6, 7, 2, 3]
  invFun := ![1, 0, 14, 15, 3, 2, 12, 13, 5, 4, 10, 11, 7, 6, 8, 9]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut7_isAut : IsAut clebschNbhd clebschAut7 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut8 : Equiv.Perm (Fin 16) where
  toFun := ![1, 5, 9, 13, 14, 10, 6, 2, 0, 4, 8, 12, 15, 11, 7, 3]
  invFun := ![8, 0, 7, 15, 9, 1, 6, 14, 10, 2, 5, 13, 11, 3, 4, 12]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut8_isAut : IsAut clebschNbhd clebschAut8 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut9 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15]
  invFun := ![0, 8, 1, 9, 2, 10, 3, 11, 4, 12, 5, 13, 6, 14, 7, 15]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut9_isAut : IsAut clebschNbhd clebschAut9 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut10 : Equiv.Perm (Fin 16) where
  toFun := ![2, 0, 13, 15, 3, 1, 12, 14, 6, 4, 9, 11, 7, 5, 8, 10]
  invFun := ![1, 5, 0, 4, 9, 13, 8, 12, 14, 10, 15, 11, 6, 2, 7, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut10_isAut : IsAut clebschNbhd clebschAut10 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut11 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 15, 13, 1, 3, 14, 12, 4, 6, 11, 9, 5, 7, 10, 8]
  invFun := ![0, 4, 1, 5, 8, 12, 9, 13, 15, 11, 14, 10, 7, 3, 6, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut11_isAut : IsAut clebschNbhd clebschAut11 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut12 : Equiv.Perm (Fin 16) where
  toFun := ![3, 7, 11, 15, 12, 8, 4, 0, 1, 5, 9, 13, 14, 10, 6, 2]
  invFun := ![7, 8, 15, 0, 6, 9, 14, 1, 5, 10, 13, 2, 4, 11, 12, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut12_isAut : IsAut clebschNbhd clebschAut12 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut13 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 15, 11, 7, 3, 1, 5, 9, 13, 14, 10, 6, 2]
  invFun := ![0, 8, 15, 7, 1, 9, 14, 6, 2, 10, 13, 5, 3, 11, 12, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut13_isAut : IsAut clebschNbhd clebschAut13 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut14 : Equiv.Perm (Fin 16) where
  toFun := ![4, 0, 11, 15, 12, 8, 3, 7, 5, 1, 10, 14, 13, 9, 2, 6]
  invFun := ![1, 9, 14, 6, 0, 8, 15, 7, 5, 13, 10, 2, 4, 12, 11, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut14_isAut : IsAut clebschNbhd clebschAut14 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut15 : Equiv.Perm (Fin 16) where
  toFun := ![11, 3, 9, 1, 10, 2, 8, 0, 15, 7, 13, 5, 14, 6, 12, 4]
  invFun := ![7, 3, 5, 1, 15, 11, 13, 9, 6, 2, 4, 0, 14, 10, 12, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut15_isAut : IsAut clebschNbhd clebschAut15 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut16 : Equiv.Perm (Fin 16) where
  toFun := ![8, 0, 7, 15, 9, 1, 6, 14, 10, 2, 5, 13, 11, 3, 4, 12]
  invFun := ![1, 5, 9, 13, 14, 10, 6, 2, 0, 4, 8, 12, 15, 11, 7, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut16_isAut : IsAut clebschNbhd clebschAut16 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut17 : Equiv.Perm (Fin 16) where
  toFun := ![11, 9, 10, 8, 15, 13, 14, 12, 3, 1, 2, 0, 7, 5, 6, 4]
  invFun := ![11, 9, 10, 8, 15, 13, 14, 12, 3, 1, 2, 0, 7, 5, 6, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut17_isAut : IsAut clebschNbhd clebschAut17 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut18 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 8, 9, 10, 11, 15, 14, 13, 12, 7, 6, 5, 4]
  invFun := ![0, 1, 2, 3, 15, 14, 13, 12, 4, 5, 6, 7, 11, 10, 9, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut18_isAut : IsAut clebschNbhd clebschAut18 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut19 : Equiv.Perm (Fin 16) where
  toFun := ![3, 11, 7, 15, 2, 10, 6, 14, 1, 9, 5, 13, 0, 8, 4, 12]
  invFun := ![12, 8, 4, 0, 14, 10, 6, 2, 13, 9, 5, 1, 15, 11, 7, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut19_isAut : IsAut clebschNbhd clebschAut19 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut20 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 4, 11, 2, 13, 6, 9, 1, 14, 5, 10, 3, 12, 7, 8]
  invFun := ![0, 8, 4, 12, 2, 10, 6, 14, 15, 7, 11, 3, 13, 5, 9, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut20_isAut : IsAut clebschNbhd clebschAut20 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut21 : Equiv.Perm (Fin 16) where
  toFun := ![11, 3, 10, 2, 15, 7, 14, 6, 4, 12, 5, 13, 0, 8, 1, 9]
  invFun := ![12, 14, 3, 1, 8, 10, 7, 5, 13, 15, 2, 0, 9, 11, 6, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut21_isAut : IsAut clebschNbhd clebschAut21 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut22 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 1, 3, 8, 10, 9, 11, 15, 13, 14, 12, 7, 5, 6, 4]
  invFun := ![0, 2, 1, 3, 15, 13, 14, 12, 4, 6, 5, 7, 11, 9, 10, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut22_isAut : IsAut clebschNbhd clebschAut22 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut23 : Equiv.Perm (Fin 16) where
  toFun := ![13, 2, 5, 10, 12, 3, 4, 11, 15, 0, 7, 8, 14, 1, 6, 9]
  invFun := ![9, 13, 1, 5, 6, 2, 14, 10, 11, 15, 3, 7, 4, 0, 12, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut23_isAut : IsAut clebschNbhd clebschAut23 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut24 : Equiv.Perm (Fin 16) where
  toFun := ![13, 2, 5, 10, 15, 0, 7, 8, 12, 3, 4, 11, 14, 1, 6, 9]
  invFun := ![5, 13, 1, 9, 10, 2, 14, 6, 7, 15, 3, 11, 8, 0, 12, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut24_isAut : IsAut clebschNbhd clebschAut24 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut25 : Equiv.Perm (Fin 16) where
  toFun := ![2, 13, 0, 15, 3, 12, 1, 14, 10, 5, 8, 7, 11, 4, 9, 6]
  invFun := ![2, 6, 0, 4, 13, 9, 15, 11, 10, 14, 8, 12, 5, 1, 7, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut25_isAut : IsAut clebschNbhd clebschAut25 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut26 : Equiv.Perm (Fin 16) where
  toFun := ![3, 11, 7, 15, 12, 4, 8, 0, 1, 9, 5, 13, 14, 6, 10, 2]
  invFun := ![7, 8, 15, 0, 5, 10, 13, 2, 6, 9, 14, 1, 4, 11, 12, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut26_isAut : IsAut clebschNbhd clebschAut26 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut27 : Equiv.Perm (Fin 16) where
  toFun := ![11, 3, 4, 12, 15, 7, 0, 8, 9, 1, 6, 14, 13, 5, 2, 10]
  invFun := ![6, 9, 14, 1, 2, 13, 10, 5, 7, 8, 15, 0, 3, 12, 11, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut27_isAut : IsAut clebschNbhd clebschAut27 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut28 : Equiv.Perm (Fin 16) where
  toFun := ![11, 4, 3, 12, 15, 0, 7, 8, 9, 6, 1, 14, 13, 2, 5, 10]
  invFun := ![5, 10, 13, 2, 1, 14, 9, 6, 7, 8, 15, 0, 3, 12, 11, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut28_isAut : IsAut clebschNbhd clebschAut28 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut29 : Equiv.Perm (Fin 16) where
  toFun := ![3, 11, 7, 15, 2, 10, 6, 14, 12, 4, 8, 0, 13, 5, 9, 1]
  invFun := ![11, 15, 4, 0, 9, 13, 6, 2, 10, 14, 5, 1, 8, 12, 7, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut29_isAut : IsAut clebschNbhd clebschAut29 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut30 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 15, 11, 8, 12, 7, 3, 2, 6, 13, 9, 10, 14, 5, 1]
  invFun := ![0, 15, 8, 7, 1, 14, 9, 6, 4, 11, 12, 3, 5, 10, 13, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut30_isAut : IsAut clebschNbhd clebschAut30 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut31 : Equiv.Perm (Fin 16) where
  toFun := ![3, 2, 1, 0, 12, 13, 14, 15, 11, 10, 9, 8, 4, 5, 6, 7]
  invFun := ![3, 2, 1, 0, 12, 13, 14, 15, 11, 10, 9, 8, 4, 5, 6, 7]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut31_isAut : IsAut clebschNbhd clebschAut31 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut32 : Equiv.Perm (Fin 16) where
  toFun := ![11, 10, 15, 14, 3, 2, 7, 6, 4, 5, 0, 1, 12, 13, 8, 9]
  invFun := ![10, 11, 5, 4, 8, 9, 7, 6, 14, 15, 1, 0, 12, 13, 3, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut32_isAut : IsAut clebschNbhd clebschAut32 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut33 : Equiv.Perm (Fin 16) where
  toFun := ![14, 15, 1, 0, 10, 11, 5, 4, 6, 7, 9, 8, 2, 3, 13, 12]
  invFun := ![3, 2, 12, 13, 7, 6, 8, 9, 11, 10, 4, 5, 15, 14, 0, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut33_isAut : IsAut clebschNbhd clebschAut33 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut34 : Equiv.Perm (Fin 16) where
  toFun := ![14, 10, 15, 11, 1, 5, 0, 4, 6, 2, 7, 3, 9, 13, 8, 12]
  invFun := ![6, 4, 9, 11, 7, 5, 8, 10, 14, 12, 1, 3, 15, 13, 0, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut34_isAut : IsAut clebschNbhd clebschAut34 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut35 : Equiv.Perm (Fin 16) where
  toFun := ![14, 1, 15, 0, 12, 3, 13, 2, 10, 5, 11, 4, 8, 7, 9, 6]
  invFun := ![3, 1, 7, 5, 11, 9, 15, 13, 12, 14, 8, 10, 4, 6, 0, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut35_isAut : IsAut clebschNbhd clebschAut35 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut36 : Equiv.Perm (Fin 16) where
  toFun := ![10, 11, 2, 3, 14, 15, 6, 7, 5, 4, 13, 12, 1, 0, 9, 8]
  invFun := ![13, 12, 2, 3, 9, 8, 6, 7, 15, 14, 0, 1, 11, 10, 4, 5]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut36_isAut : IsAut clebschNbhd clebschAut36 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut37 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 8, 10, 4, 6, 12, 14, 15, 13, 7, 5, 11, 9, 3, 1]
  invFun := ![0, 15, 1, 14, 4, 11, 5, 10, 2, 13, 3, 12, 6, 9, 7, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut37_isAut : IsAut clebschNbhd clebschAut37 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut38 : Equiv.Perm (Fin 16) where
  toFun := ![10, 14, 11, 15, 2, 6, 3, 7, 5, 1, 4, 0, 13, 9, 12, 8]
  invFun := ![11, 9, 4, 6, 10, 8, 5, 7, 15, 13, 0, 2, 14, 12, 1, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut38_isAut : IsAut clebschNbhd clebschAut38 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut39 : Equiv.Perm (Fin 16) where
  toFun := ![2, 0, 13, 15, 3, 1, 12, 14, 10, 8, 5, 7, 11, 9, 4, 6]
  invFun := ![1, 5, 0, 4, 14, 10, 15, 11, 9, 13, 8, 12, 6, 2, 7, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut39_isAut : IsAut clebschNbhd clebschAut39 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut40 : Equiv.Perm (Fin 16) where
  toFun := ![15, 11, 0, 4, 14, 10, 1, 5, 7, 3, 8, 12, 6, 2, 9, 13]
  invFun := ![2, 6, 13, 9, 3, 7, 12, 8, 10, 14, 5, 1, 11, 15, 4, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut40_isAut : IsAut clebschNbhd clebschAut40 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut41 : Equiv.Perm (Fin 16) where
  toFun := ![11, 10, 15, 14, 4, 5, 0, 1, 3, 2, 7, 6, 12, 13, 8, 9]
  invFun := ![6, 7, 9, 8, 4, 5, 11, 10, 14, 15, 1, 0, 12, 13, 3, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut41_isAut : IsAut clebschNbhd clebschAut41 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut42 : Equiv.Perm (Fin 16) where
  toFun := ![11, 15, 4, 0, 10, 14, 5, 1, 3, 7, 12, 8, 2, 6, 13, 9]
  invFun := ![3, 7, 12, 8, 2, 6, 13, 9, 11, 15, 4, 0, 10, 14, 5, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut42_isAut : IsAut clebschNbhd clebschAut42 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut43 : Equiv.Perm (Fin 16) where
  toFun := ![10, 11, 14, 15, 2, 3, 6, 7, 5, 4, 1, 0, 13, 12, 9, 8]
  invFun := ![11, 10, 4, 5, 9, 8, 6, 7, 15, 14, 0, 1, 13, 12, 2, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut43_isAut : IsAut clebschNbhd clebschAut43 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut44 : Equiv.Perm (Fin 16) where
  toFun := ![14, 1, 10, 5, 15, 0, 11, 4, 6, 9, 2, 13, 7, 8, 3, 12]
  invFun := ![5, 1, 10, 14, 7, 3, 8, 12, 13, 9, 2, 6, 15, 11, 0, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut44_isAut : IsAut clebschNbhd clebschAut44 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut45 : Equiv.Perm (Fin 16) where
  toFun := ![10, 14, 11, 15, 5, 1, 4, 0, 2, 6, 3, 7, 13, 9, 12, 8]
  invFun := ![7, 5, 8, 10, 6, 4, 9, 11, 15, 13, 0, 2, 14, 12, 1, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut45_isAut : IsAut clebschNbhd clebschAut45 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut46 : Equiv.Perm (Fin 16) where
  toFun := ![1, 14, 0, 15, 5, 10, 4, 11, 3, 12, 2, 13, 7, 8, 6, 9]
  invFun := ![2, 0, 10, 8, 6, 4, 14, 12, 13, 15, 5, 7, 9, 11, 1, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut46_isAut : IsAut clebschNbhd clebschAut46 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut47 : Equiv.Perm (Fin 16) where
  toFun := ![5, 1, 7, 3, 13, 9, 15, 11, 10, 14, 8, 12, 2, 6, 0, 4]
  invFun := ![14, 1, 12, 3, 15, 0, 13, 2, 10, 5, 8, 7, 11, 4, 9, 6]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut47_isAut : IsAut clebschNbhd clebschAut47 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut48 : Equiv.Perm (Fin 16) where
  toFun := ![1, 14, 0, 15, 5, 10, 4, 11, 9, 6, 8, 7, 13, 2, 12, 3]
  invFun := ![2, 0, 13, 15, 6, 4, 9, 11, 10, 8, 5, 7, 14, 12, 1, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut48_isAut : IsAut clebschNbhd clebschAut48 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut49 : Equiv.Perm (Fin 16) where
  toFun := ![10, 11, 14, 15, 8, 9, 12, 13, 5, 4, 1, 0, 7, 6, 3, 2]
  invFun := ![11, 10, 15, 14, 9, 8, 13, 12, 4, 5, 0, 1, 6, 7, 2, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut49_isAut : IsAut clebschNbhd clebschAut49 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut50 : Equiv.Perm (Fin 16) where
  toFun := ![14, 10, 15, 11, 6, 2, 7, 3, 1, 5, 0, 4, 9, 13, 8, 12]
  invFun := ![10, 8, 5, 7, 11, 9, 4, 6, 14, 12, 1, 3, 15, 13, 0, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut50_isAut : IsAut clebschNbhd clebschAut50 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut51 : Equiv.Perm (Fin 16) where
  toFun := ![15, 7, 11, 3, 14, 6, 10, 2, 13, 5, 9, 1, 12, 4, 8, 0]
  invFun := ![15, 11, 7, 3, 13, 9, 5, 1, 14, 10, 6, 2, 12, 8, 4, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut51_isAut : IsAut clebschNbhd clebschAut51 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut52 : Equiv.Perm (Fin 16) where
  toFun := ![14, 1, 6, 9, 10, 5, 2, 13, 15, 0, 7, 8, 11, 4, 3, 12]
  invFun := ![9, 1, 6, 14, 13, 5, 2, 10, 11, 3, 4, 12, 15, 7, 0, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut52_isAut : IsAut clebschNbhd clebschAut52 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut53 : Equiv.Perm (Fin 16) where
  toFun := ![11, 15, 10, 14, 3, 7, 2, 6, 4, 0, 5, 1, 12, 8, 13, 9]
  invFun := ![9, 11, 6, 4, 8, 10, 7, 5, 13, 15, 2, 0, 12, 14, 3, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut53_isAut : IsAut clebschNbhd clebschAut53 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut54 : Equiv.Perm (Fin 16) where
  toFun := ![15, 11, 14, 10, 0, 4, 1, 5, 7, 3, 6, 2, 8, 12, 9, 13]
  invFun := ![4, 6, 11, 9, 5, 7, 10, 8, 12, 14, 3, 1, 13, 15, 2, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut54_isAut : IsAut clebschNbhd clebschAut54 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut55 : Equiv.Perm (Fin 16) where
  toFun := ![15, 11, 7, 3, 0, 4, 8, 12, 14, 10, 6, 2, 1, 5, 9, 13]
  invFun := ![4, 12, 11, 3, 5, 13, 10, 2, 6, 14, 9, 1, 7, 15, 8, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut55_isAut : IsAut clebschNbhd clebschAut55 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut56 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 1, 14, 4, 11, 5, 10, 2, 13, 3, 12, 6, 9, 7, 8]
  invFun := ![0, 2, 8, 10, 4, 6, 12, 14, 15, 13, 7, 5, 11, 9, 3, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut56_isAut : IsAut clebschNbhd clebschAut56 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut57 : Equiv.Perm (Fin 16) where
  toFun := ![11, 15, 3, 7, 10, 14, 2, 6, 9, 13, 1, 5, 8, 12, 0, 4]
  invFun := ![14, 10, 6, 2, 15, 11, 7, 3, 12, 8, 4, 0, 13, 9, 5, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut57_isAut : IsAut clebschNbhd clebschAut57 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut58 : Equiv.Perm (Fin 16) where
  toFun := ![15, 0, 7, 8, 14, 1, 6, 9, 11, 4, 3, 12, 10, 5, 2, 13]
  invFun := ![1, 5, 14, 10, 9, 13, 6, 2, 3, 7, 12, 8, 11, 15, 4, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut58_isAut : IsAut clebschNbhd clebschAut58 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut59 : Equiv.Perm (Fin 16) where
  toFun := ![15, 11, 13, 9, 7, 3, 5, 1, 14, 10, 12, 8, 6, 2, 4, 0]
  invFun := ![15, 7, 13, 5, 14, 6, 12, 4, 11, 3, 9, 1, 10, 2, 8, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut59_isAut : IsAut clebschNbhd clebschAut59 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut60 : Equiv.Perm (Fin 16) where
  toFun := ![7, 15, 6, 14, 8, 0, 9, 1, 3, 11, 2, 10, 12, 4, 13, 5]
  invFun := ![5, 7, 10, 8, 13, 15, 2, 0, 4, 6, 11, 9, 12, 14, 3, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut60_isAut : IsAut clebschNbhd clebschAut60 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut61 : Equiv.Perm (Fin 16) where
  toFun := ![12, 4, 14, 6, 13, 5, 15, 7, 3, 11, 1, 9, 2, 10, 0, 8]
  invFun := ![14, 10, 12, 8, 1, 5, 3, 7, 15, 11, 13, 9, 0, 4, 2, 6]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut61_isAut : IsAut clebschNbhd clebschAut61 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut62 : Equiv.Perm (Fin 16) where
  toFun := ![15, 14, 7, 6, 13, 12, 5, 4, 11, 10, 3, 2, 9, 8, 1, 0]
  invFun := ![15, 14, 11, 10, 7, 6, 3, 2, 13, 12, 9, 8, 5, 4, 1, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut62_isAut : IsAut clebschNbhd clebschAut62 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut63 : Equiv.Perm (Fin 16) where
  toFun := ![7, 15, 3, 11, 6, 14, 2, 10, 8, 0, 12, 4, 9, 1, 13, 5]
  invFun := ![9, 13, 6, 2, 11, 15, 4, 0, 8, 12, 7, 3, 10, 14, 5, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut63_isAut : IsAut clebschNbhd clebschAut63 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut64 : Equiv.Perm (Fin 16) where
  toFun := ![14, 15, 6, 7, 10, 11, 2, 3, 12, 13, 4, 5, 8, 9, 0, 1]
  invFun := ![14, 15, 6, 7, 10, 11, 2, 3, 12, 13, 4, 5, 8, 9, 0, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut64_isAut : IsAut clebschNbhd clebschAut64 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut65 : Equiv.Perm (Fin 16) where
  toFun := ![13, 12, 15, 14, 9, 8, 11, 10, 2, 3, 0, 1, 6, 7, 4, 5]
  invFun := ![10, 11, 8, 9, 14, 15, 12, 13, 5, 4, 7, 6, 1, 0, 3, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut65_isAut : IsAut clebschNbhd clebschAut65 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut66 : Equiv.Perm (Fin 16) where
  toFun := ![15, 13, 0, 2, 11, 9, 4, 6, 14, 12, 1, 3, 10, 8, 5, 7]
  invFun := ![2, 10, 3, 11, 6, 14, 7, 15, 13, 5, 12, 4, 9, 1, 8, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut66_isAut : IsAut clebschNbhd clebschAut66 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut67 : Equiv.Perm (Fin 16) where
  toFun := ![13, 15, 9, 11, 12, 14, 8, 10, 2, 0, 6, 4, 3, 1, 7, 5]
  invFun := ![9, 13, 8, 12, 11, 15, 10, 14, 6, 2, 7, 3, 4, 0, 5, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut67_isAut : IsAut clebschNbhd clebschAut67 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut68 : Equiv.Perm (Fin 16) where
  toFun := ![1, 3, 0, 2, 14, 12, 15, 13, 9, 11, 8, 10, 6, 4, 7, 5]
  invFun := ![2, 0, 3, 1, 13, 15, 12, 14, 10, 8, 11, 9, 5, 7, 4, 6]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut68_isAut : IsAut clebschNbhd clebschAut68 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut69 : Equiv.Perm (Fin 16) where
  toFun := ![2, 0, 13, 15, 6, 4, 9, 11, 10, 8, 5, 7, 14, 12, 1, 3]
  invFun := ![1, 14, 0, 15, 5, 10, 4, 11, 9, 6, 8, 7, 13, 2, 12, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut69_isAut : IsAut clebschNbhd clebschAut69 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut70 : Equiv.Perm (Fin 16) where
  toFun := ![14, 6, 15, 7, 1, 9, 0, 8, 10, 2, 11, 3, 5, 13, 4, 12]
  invFun := ![6, 4, 9, 11, 14, 12, 1, 3, 7, 5, 8, 10, 15, 13, 0, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut70_isAut : IsAut clebschNbhd clebschAut70 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut71 : Equiv.Perm (Fin 16) where
  toFun := ![2, 3, 6, 7, 10, 11, 14, 15, 0, 1, 4, 5, 8, 9, 12, 13]
  invFun := ![8, 9, 0, 1, 10, 11, 2, 3, 12, 13, 4, 5, 14, 15, 6, 7]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut71_isAut : IsAut clebschNbhd clebschAut71 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut72 : Equiv.Perm (Fin 16) where
  toFun := ![14, 6, 12, 4, 15, 7, 13, 5, 10, 2, 8, 0, 11, 3, 9, 1]
  invFun := ![11, 15, 9, 13, 3, 7, 1, 5, 10, 14, 8, 12, 2, 6, 0, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut72_isAut : IsAut clebschNbhd clebschAut72 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut73 : Equiv.Perm (Fin 16) where
  toFun := ![6, 2, 14, 10, 4, 0, 12, 8, 7, 3, 15, 11, 5, 1, 13, 9]
  invFun := ![5, 13, 1, 9, 4, 12, 0, 8, 7, 15, 3, 11, 6, 14, 2, 10]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut73_isAut : IsAut clebschNbhd clebschAut73 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut74 : Equiv.Perm (Fin 16) where
  toFun := ![6, 2, 7, 3, 14, 10, 15, 11, 9, 13, 8, 12, 1, 5, 0, 4]
  invFun := ![14, 12, 1, 3, 15, 13, 0, 2, 10, 8, 5, 7, 11, 9, 4, 6]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut74_isAut : IsAut clebschNbhd clebschAut74 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut75 : Equiv.Perm (Fin 16) where
  toFun := ![2, 0, 10, 8, 6, 4, 14, 12, 13, 15, 5, 7, 9, 11, 1, 3]
  invFun := ![1, 14, 0, 15, 5, 10, 4, 11, 3, 12, 2, 13, 7, 8, 6, 9]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut75_isAut : IsAut clebschNbhd clebschAut75 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut76 : Equiv.Perm (Fin 16) where
  toFun := ![14, 12, 10, 8, 15, 13, 11, 9, 6, 4, 2, 0, 7, 5, 3, 1]
  invFun := ![11, 15, 10, 14, 9, 13, 8, 12, 3, 7, 2, 6, 1, 5, 0, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut76_isAut : IsAut clebschNbhd clebschAut76 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut77 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 1, 14, 8, 7, 9, 6, 2, 13, 3, 12, 10, 5, 11, 4]
  invFun := ![0, 2, 8, 10, 15, 13, 7, 5, 4, 6, 12, 14, 11, 9, 3, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut77_isAut : IsAut clebschNbhd clebschAut77 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut78 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 2, 6, 10, 14, 15, 11, 7, 3, 13, 9, 5, 1]
  invFun := ![0, 15, 4, 11, 1, 14, 5, 10, 2, 13, 6, 9, 3, 12, 7, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut78_isAut : IsAut clebschNbhd clebschAut78 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut79 : Equiv.Perm (Fin 16) where
  toFun := ![11, 15, 9, 13, 10, 14, 8, 12, 3, 7, 1, 5, 2, 6, 0, 4]
  invFun := ![14, 10, 12, 8, 15, 11, 13, 9, 6, 2, 4, 0, 7, 3, 5, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut79_isAut : IsAut clebschNbhd clebschAut79 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut80 : Equiv.Perm (Fin 16) where
  toFun := ![15, 11, 13, 9, 14, 10, 12, 8, 0, 4, 2, 6, 1, 5, 3, 7]
  invFun := ![8, 12, 10, 14, 9, 13, 11, 15, 7, 3, 5, 1, 6, 2, 4, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut80_isAut : IsAut clebschNbhd clebschAut80 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut81 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 15, 14, 13, 12, 8, 9, 10, 11, 7, 6, 5, 4]
  invFun := ![0, 1, 2, 3, 15, 14, 13, 12, 8, 9, 10, 11, 7, 6, 5, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut81_isAut : IsAut clebschNbhd clebschAut81 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut82 : Equiv.Perm (Fin 16) where
  toFun := ![15, 11, 7, 3, 13, 9, 5, 1, 14, 10, 6, 2, 12, 8, 4, 0]
  invFun := ![15, 7, 11, 3, 14, 6, 10, 2, 13, 5, 9, 1, 12, 4, 8, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut82_isAut : IsAut clebschNbhd clebschAut82 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut83 : Equiv.Perm (Fin 16) where
  toFun := ![15, 0, 13, 2, 14, 1, 12, 3, 11, 4, 9, 6, 10, 5, 8, 7]
  invFun := ![1, 5, 3, 7, 9, 13, 11, 15, 14, 10, 12, 8, 6, 2, 4, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut83_isAut : IsAut clebschNbhd clebschAut83 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut84 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 4, 11, 1, 14, 5, 10, 2, 13, 6, 9, 3, 12, 7, 8]
  invFun := ![0, 4, 8, 12, 2, 6, 10, 14, 15, 11, 7, 3, 13, 9, 5, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut84_isAut : IsAut clebschNbhd clebschAut84 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut85 : Equiv.Perm (Fin 16) where
  toFun := ![10, 14, 5, 1, 11, 15, 4, 0, 2, 6, 13, 9, 3, 7, 12, 8]
  invFun := ![7, 3, 8, 12, 6, 2, 9, 13, 15, 11, 0, 4, 14, 10, 1, 5]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut85_isAut : IsAut clebschNbhd clebschAut85 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut86 : Equiv.Perm (Fin 16) where
  toFun := ![11, 4, 10, 5, 3, 12, 2, 13, 15, 0, 14, 1, 7, 8, 6, 9]
  invFun := ![9, 11, 6, 4, 1, 3, 14, 12, 13, 15, 2, 0, 5, 7, 10, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut86_isAut : IsAut clebschNbhd clebschAut86 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut87 : Equiv.Perm (Fin 16) where
  toFun := ![14, 15, 6, 7, 12, 13, 4, 5, 10, 11, 2, 3, 8, 9, 0, 1]
  invFun := ![14, 15, 10, 11, 6, 7, 2, 3, 12, 13, 8, 9, 4, 5, 0, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut87_isAut : IsAut clebschNbhd clebschAut87 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut88 : Equiv.Perm (Fin 16) where
  toFun := ![14, 10, 15, 11, 1, 5, 0, 4, 12, 8, 13, 9, 3, 7, 2, 6]
  invFun := ![6, 4, 14, 12, 7, 5, 15, 13, 9, 11, 1, 3, 8, 10, 0, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut88_isAut : IsAut clebschNbhd clebschAut88 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut89 : Equiv.Perm (Fin 16) where
  toFun := ![11, 15, 10, 14, 9, 13, 8, 12, 4, 0, 5, 1, 6, 2, 7, 3]
  invFun := ![9, 11, 13, 15, 8, 10, 12, 14, 6, 4, 2, 0, 7, 5, 3, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut89_isAut : IsAut clebschNbhd clebschAut89 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut90 : Equiv.Perm (Fin 16) where
  toFun := ![4, 11, 0, 15, 5, 10, 1, 14, 12, 3, 8, 7, 13, 2, 9, 6]
  invFun := ![2, 6, 13, 9, 0, 4, 15, 11, 10, 14, 5, 1, 8, 12, 7, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut90_isAut : IsAut clebschNbhd clebschAut90 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut91 : Equiv.Perm (Fin 16) where
  toFun := ![14, 10, 12, 8, 15, 11, 13, 9, 1, 5, 3, 7, 0, 4, 2, 6]
  invFun := ![12, 8, 14, 10, 13, 9, 15, 11, 3, 7, 1, 5, 2, 6, 0, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut91_isAut : IsAut clebschNbhd clebschAut91 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut92 : Equiv.Perm (Fin 16) where
  toFun := ![3, 7, 1, 5, 12, 8, 14, 10, 11, 15, 9, 13, 4, 0, 6, 2]
  invFun := ![13, 2, 15, 0, 12, 3, 14, 1, 5, 10, 7, 8, 4, 11, 6, 9]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut92_isAut : IsAut clebschNbhd clebschAut92 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut93 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 4, 5, 15, 14, 11, 10, 8, 9, 12, 13, 7, 6, 3, 2]
  invFun := ![0, 1, 15, 14, 2, 3, 13, 12, 8, 9, 7, 6, 10, 11, 5, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut93_isAut : IsAut clebschNbhd clebschAut93 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut94 : Equiv.Perm (Fin 16) where
  toFun := ![11, 4, 9, 6, 10, 5, 8, 7, 15, 0, 13, 2, 14, 1, 12, 3]
  invFun := ![9, 13, 11, 15, 1, 5, 3, 7, 6, 2, 4, 0, 14, 10, 12, 8]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut94_isAut : IsAut clebschNbhd clebschAut94 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut95 : Equiv.Perm (Fin 16) where
  toFun := ![9, 11, 8, 10, 13, 15, 12, 14, 6, 4, 7, 5, 2, 0, 3, 1]
  invFun := ![13, 15, 12, 14, 9, 11, 8, 10, 2, 0, 3, 1, 6, 4, 7, 5]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut95_isAut : IsAut clebschNbhd clebschAut95 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut96 : Equiv.Perm (Fin 16) where
  toFun := ![15, 14, 7, 6, 11, 10, 3, 2, 13, 12, 5, 4, 9, 8, 1, 0]
  invFun := ![15, 14, 7, 6, 11, 10, 3, 2, 13, 12, 5, 4, 9, 8, 1, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut96_isAut : IsAut clebschNbhd clebschAut96 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut97 : Equiv.Perm (Fin 16) where
  toFun := ![12, 14, 4, 6, 8, 10, 0, 2, 13, 15, 5, 7, 9, 11, 1, 3]
  invFun := ![6, 14, 7, 15, 2, 10, 3, 11, 4, 12, 5, 13, 0, 8, 1, 9]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut97_isAut : IsAut clebschNbhd clebschAut97 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut98 : Equiv.Perm (Fin 16) where
  toFun := ![14, 12, 15, 13, 6, 4, 7, 5, 10, 8, 11, 9, 2, 0, 3, 1]
  invFun := ![13, 15, 12, 14, 5, 7, 4, 6, 9, 11, 8, 10, 1, 3, 0, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut98_isAut : IsAut clebschNbhd clebschAut98 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut99 : Equiv.Perm (Fin 16) where
  toFun := ![15, 13, 14, 12, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2, 0]
  invFun := ![15, 13, 14, 12, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut99_isAut : IsAut clebschNbhd clebschAut99 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut100 : Equiv.Perm (Fin 16) where
  toFun := ![11, 9, 10, 8, 15, 13, 14, 12, 4, 6, 5, 7, 0, 2, 1, 3]
  invFun := ![12, 14, 13, 15, 8, 10, 9, 11, 3, 1, 2, 0, 7, 5, 6, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut100_isAut : IsAut clebschNbhd clebschAut100 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut101 : Equiv.Perm (Fin 16) where
  toFun := ![13, 15, 12, 14, 9, 11, 8, 10, 5, 7, 4, 6, 1, 3, 0, 2]
  invFun := ![14, 12, 15, 13, 10, 8, 11, 9, 6, 4, 7, 5, 2, 0, 3, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut101_isAut : IsAut clebschNbhd clebschAut101 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut102 : Equiv.Perm (Fin 16) where
  toFun := ![11, 15, 4, 0, 10, 14, 5, 1, 9, 13, 6, 2, 8, 12, 7, 3]
  invFun := ![3, 7, 11, 15, 2, 6, 10, 14, 12, 8, 4, 0, 13, 9, 5, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut102_isAut : IsAut clebschNbhd clebschAut102 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut103 : Equiv.Perm (Fin 16) where
  toFun := ![11, 10, 15, 14, 4, 5, 0, 1, 9, 8, 13, 12, 6, 7, 2, 3]
  invFun := ![6, 7, 14, 15, 4, 5, 12, 13, 9, 8, 1, 0, 11, 10, 3, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut103_isAut : IsAut clebschNbhd clebschAut103 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut104 : Equiv.Perm (Fin 16) where
  toFun := ![8, 9, 12, 13, 10, 11, 14, 15, 0, 1, 4, 5, 2, 3, 6, 7]
  invFun := ![8, 9, 12, 13, 10, 11, 14, 15, 0, 1, 4, 5, 2, 3, 6, 7]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut104_isAut : IsAut clebschNbhd clebschAut104 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut105 : Equiv.Perm (Fin 16) where
  toFun := ![2, 0, 3, 1, 10, 8, 11, 9, 13, 15, 12, 14, 5, 7, 4, 6]
  invFun := ![1, 3, 0, 2, 14, 12, 15, 13, 5, 7, 4, 6, 10, 8, 11, 9]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut105_isAut : IsAut clebschNbhd clebschAut105 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut106 : Equiv.Perm (Fin 16) where
  toFun := ![8, 9, 12, 13, 10, 11, 14, 15, 7, 6, 3, 2, 5, 4, 1, 0]
  invFun := ![15, 14, 11, 10, 13, 12, 9, 8, 0, 1, 4, 5, 2, 3, 6, 7]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut106_isAut : IsAut clebschNbhd clebschAut106 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut107 : Equiv.Perm (Fin 16) where
  toFun := ![6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13, 1, 0, 3, 2]
  invFun := ![13, 12, 15, 14, 2, 3, 0, 1, 5, 4, 7, 6, 10, 11, 8, 9]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut107_isAut : IsAut clebschNbhd clebschAut107 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut108 : Equiv.Perm (Fin 16) where
  toFun := ![5, 1, 13, 9, 4, 0, 12, 8, 7, 3, 15, 11, 6, 2, 14, 10]
  invFun := ![5, 1, 13, 9, 4, 0, 12, 8, 7, 3, 15, 11, 6, 2, 14, 10]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut108_isAut : IsAut clebschNbhd clebschAut108 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut109 : Equiv.Perm (Fin 16) where
  toFun := ![9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut109_isAut : IsAut clebschNbhd clebschAut109 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut110 : Equiv.Perm (Fin 16) where
  toFun := ![7, 15, 3, 11, 5, 13, 1, 9, 6, 14, 2, 10, 4, 12, 0, 8]
  invFun := ![14, 6, 10, 2, 12, 4, 8, 0, 15, 7, 11, 3, 13, 5, 9, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut110_isAut : IsAut clebschNbhd clebschAut110 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut111 : Equiv.Perm (Fin 16) where
  toFun := ![15, 0, 7, 8, 11, 4, 3, 12, 13, 2, 5, 10, 9, 6, 1, 14]
  invFun := ![1, 14, 9, 6, 5, 10, 13, 2, 3, 12, 11, 4, 7, 8, 15, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut111_isAut : IsAut clebschNbhd clebschAut111 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut112 : Equiv.Perm (Fin 16) where
  toFun := ![15, 7, 11, 3, 13, 5, 9, 1, 0, 8, 4, 12, 2, 10, 6, 14]
  invFun := ![8, 7, 12, 3, 10, 5, 14, 1, 9, 6, 13, 2, 11, 4, 15, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut112_isAut : IsAut clebschNbhd clebschAut112 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut113 : Equiv.Perm (Fin 16) where
  toFun := ![14, 12, 15, 13, 1, 3, 0, 2, 6, 4, 7, 5, 9, 11, 8, 10]
  invFun := ![6, 4, 7, 5, 9, 11, 8, 10, 14, 12, 15, 13, 1, 3, 0, 2]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut113_isAut : IsAut clebschNbhd clebschAut113 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut114 : Equiv.Perm (Fin 16) where
  toFun := ![13, 15, 2, 0, 12, 14, 3, 1, 5, 7, 10, 8, 4, 6, 11, 9]
  invFun := ![3, 7, 2, 6, 12, 8, 13, 9, 11, 15, 10, 14, 4, 0, 5, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut114_isAut : IsAut clebschNbhd clebschAut114 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut115 : Equiv.Perm (Fin 16) where
  toFun := ![15, 14, 0, 1, 13, 12, 2, 3, 7, 6, 8, 9, 5, 4, 10, 11]
  invFun := ![2, 3, 6, 7, 13, 12, 9, 8, 10, 11, 14, 15, 5, 4, 1, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut115_isAut : IsAut clebschNbhd clebschAut115 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut116 : Equiv.Perm (Fin 16) where
  toFun := ![5, 1, 4, 0, 7, 3, 6, 2, 13, 9, 12, 8, 15, 11, 14, 10]
  invFun := ![3, 1, 7, 5, 2, 0, 6, 4, 11, 9, 15, 13, 10, 8, 14, 12]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut116_isAut : IsAut clebschNbhd clebschAut116 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut117 : Equiv.Perm (Fin 16) where
  toFun := ![13, 15, 5, 7, 9, 11, 1, 3, 12, 14, 4, 6, 8, 10, 0, 2]
  invFun := ![14, 6, 15, 7, 10, 2, 11, 3, 12, 4, 13, 5, 8, 0, 9, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut117_isAut : IsAut clebschNbhd clebschAut117 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut118 : Equiv.Perm (Fin 16) where
  toFun := ![7, 15, 3, 11, 5, 13, 1, 9, 8, 0, 12, 4, 10, 2, 14, 6]
  invFun := ![9, 6, 13, 2, 11, 4, 15, 0, 8, 7, 12, 3, 10, 5, 14, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut118_isAut : IsAut clebschNbhd clebschAut118 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut119 : Equiv.Perm (Fin 16) where
  toFun := ![9, 13, 8, 12, 11, 15, 10, 14, 1, 5, 0, 4, 3, 7, 2, 6]
  invFun := ![10, 8, 14, 12, 11, 9, 15, 13, 2, 0, 6, 4, 3, 1, 7, 5]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut119_isAut : IsAut clebschNbhd clebschAut119 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut120 : Equiv.Perm (Fin 16) where
  toFun := ![13, 9, 12, 8, 15, 11, 14, 10, 2, 6, 3, 7, 0, 4, 1, 5]
  invFun := ![12, 14, 8, 10, 13, 15, 9, 11, 3, 1, 7, 5, 2, 0, 6, 4]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut120_isAut : IsAut clebschNbhd clebschAut120 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut121 : Equiv.Perm (Fin 16) where
  toFun := ![9, 8, 13, 12, 11, 10, 15, 14, 1, 0, 5, 4, 3, 2, 7, 6]
  invFun := ![9, 8, 13, 12, 11, 10, 15, 14, 1, 0, 5, 4, 3, 2, 7, 6]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut121_isAut : IsAut clebschNbhd clebschAut121 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut122 : Equiv.Perm (Fin 16) where
  toFun := ![9, 11, 13, 15, 1, 3, 5, 7, 8, 10, 12, 14, 0, 2, 4, 6]
  invFun := ![12, 4, 13, 5, 14, 6, 15, 7, 8, 0, 9, 1, 10, 2, 11, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut122_isAut : IsAut clebschNbhd clebschAut122 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut123 : Equiv.Perm (Fin 16) where
  toFun := ![15, 11, 13, 9, 14, 10, 12, 8, 7, 3, 5, 1, 6, 2, 4, 0]
  invFun := ![15, 11, 13, 9, 14, 10, 12, 8, 7, 3, 5, 1, 6, 2, 4, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut123_isAut : IsAut clebschNbhd clebschAut123 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut124 : Equiv.Perm (Fin 16) where
  toFun := ![9, 13, 11, 15, 1, 5, 3, 7, 8, 12, 10, 14, 0, 4, 2, 6]
  invFun := ![12, 4, 14, 6, 13, 5, 15, 7, 8, 0, 10, 2, 9, 1, 11, 3]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut124_isAut : IsAut clebschNbhd clebschAut124 := by
  decide

/-- An automorphism used by the certificate. -/
def clebschAut125 : Equiv.Perm (Fin 16) where
  toFun := ![15, 13, 11, 9, 14, 12, 10, 8, 7, 5, 3, 1, 6, 4, 2, 0]
  invFun := ![15, 11, 14, 10, 13, 9, 12, 8, 7, 3, 6, 2, 5, 1, 4, 0]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem clebschAut125_isAut : IsAut clebschNbhd clebschAut125 := by
  decide

set_option maxHeartbeats 40000000 in
/-- **The rate bound `5/8` for the Clebsch graph.** -/
theorem rateBound_clebsch : RateBound clebschNbhd (5 / 8) := by
  apply RateBound.of_invariant
  intro h hh hv hinv
  have e1 : h {0, 1, 5, 7, 9, 10, 11, 12, 13, 15} + h {5, 7, 9, 10, 11, 12, 13, 15} ≤ h {0, 5, 7, 9, 10, 11, 12, 13, 15} + h {1, 5, 7, 9, 10, 11, 12, 13, 15} := hh.elemental (by decide) (by decide)
  have e2 : h {0, 1, 7, 9, 10, 11, 12, 13, 15} + h {7, 9, 10, 11, 12, 13, 15} ≤ h {0, 7, 9, 10, 11, 12, 13, 15} + h {1, 7, 9, 10, 11, 12, 13, 15} := hh.elemental (by decide) (by decide)
  have e3 : h {0, 1, 8, 11, 12, 13, 15} + h {8, 11, 12, 13, 15} ≤ h {0, 8, 11, 12, 13, 15} + h {1, 8, 11, 12, 13, 15} := hh.elemental (by decide) (by decide)
  have e4 : h {0, 1, 7, 11, 12, 13, 15} + h {7, 11, 12, 13, 15} ≤ h {0, 7, 11, 12, 13, 15} + h {1, 7, 11, 12, 13, 15} := hh.elemental (by decide) (by decide)
  have e5 : h {0, 1, 2, 5, 9, 12, 15} + h {2, 5, 9, 12, 15} ≤ h {0, 2, 5, 9, 12, 15} + h {1, 2, 5, 9, 12, 15} := hh.elemental (by decide) (by decide)
  have e6 : h {0, 1, 12, 13, 15} + h {12, 13, 15} ≤ h {0, 12, 13, 15} + h {1, 12, 13, 15} := hh.elemental (by decide) (by decide)
  have e7 : h {0, 1, 7, 11, 13, 15} + h {7, 11, 13, 15} ≤ h {0, 7, 11, 13, 15} + h {1, 7, 11, 13, 15} := hh.elemental (by decide) (by decide)
  have e8 : h {0, 1, 9, 10, 12, 15} + h {9, 10, 12, 15} ≤ h {0, 9, 10, 12, 15} + h {1, 9, 10, 12, 15} := hh.elemental (by decide) (by decide)
  have e9 : h {0, 1, 12, 15} + h {12, 15} ≤ h {0, 12, 15} + h {1, 12, 15} := hh.elemental (by decide) (by decide)
  have e10 : h {0, 1, 13} + h {13} ≤ h {0, 13} + h {1, 13} := hh.elemental (by decide) (by decide)
  have e11 : h {0, 1, 3, 4, 6, 7, 8, 10, 11, 13, 14, 15} + h {1, 4, 6, 7, 8, 10, 11, 13, 14, 15} ≤ h {0, 1, 4, 6, 7, 8, 10, 11, 13, 14, 15} + h {1, 3, 4, 6, 7, 8, 10, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e12 : h {0, 2, 3, 5, 7, 8, 9, 11, 12, 14, 15} + h {2, 5, 7, 8, 9, 11, 12, 14, 15} ≤ h {0, 2, 5, 7, 8, 9, 11, 12, 14, 15} + h {2, 3, 5, 7, 8, 9, 11, 12, 14, 15} := hh.elemental (by decide) (by decide)
  have e13 : h {0, 2, 3, 5, 8, 9, 11, 12, 14, 15} + h {2, 5, 8, 9, 11, 12, 14, 15} ≤ h {0, 2, 5, 8, 9, 11, 12, 14, 15} + h {2, 3, 5, 8, 9, 11, 12, 14, 15} := hh.elemental (by decide) (by decide)
  have e14 : h {0, 1, 3, 4, 6, 8, 10, 11, 13, 14, 15} + h {1, 4, 6, 8, 10, 11, 13, 14, 15} ≤ h {0, 1, 4, 6, 8, 10, 11, 13, 14, 15} + h {1, 3, 4, 6, 8, 10, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e15 : h {0, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15} + h {4, 7, 9, 10, 11, 12, 13, 14, 15} ≤ h {0, 4, 7, 9, 10, 11, 12, 13, 14, 15} + h {3, 4, 7, 9, 10, 11, 12, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e16 : h {0, 2, 3, 5, 7, 9, 11, 12, 14, 15} + h {2, 5, 7, 9, 11, 12, 14, 15} ≤ h {0, 2, 5, 7, 9, 11, 12, 14, 15} + h {2, 3, 5, 7, 9, 11, 12, 14, 15} := hh.elemental (by decide) (by decide)
  have e17 : h {0, 3, 6, 10, 12, 13, 14, 15} + h {6, 10, 12, 13, 14, 15} ≤ h {0, 6, 10, 12, 13, 14, 15} + h {3, 6, 10, 12, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e18 : h {0, 3, 4, 7, 9, 10, 11, 13, 14, 15} + h {4, 7, 9, 10, 11, 13, 14, 15} ≤ h {0, 4, 7, 9, 10, 11, 13, 14, 15} + h {3, 4, 7, 9, 10, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e19 : h {0, 1, 3, 4, 7, 8, 10, 11, 13, 14, 15} + h {1, 4, 7, 8, 10, 11, 13, 14, 15} ≤ h {0, 1, 4, 7, 8, 10, 11, 13, 14, 15} + h {1, 3, 4, 7, 8, 10, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e20 : h {0, 3, 5, 8, 10, 11, 13, 14, 15} + h {5, 8, 10, 11, 13, 14, 15} ≤ h {0, 5, 8, 10, 11, 13, 14, 15} + h {3, 5, 8, 10, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e21 : h {0, 3, 4, 8, 10, 11, 13, 14, 15} + h {4, 8, 10, 11, 13, 14, 15} ≤ h {0, 4, 8, 10, 11, 13, 14, 15} + h {3, 4, 8, 10, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e22 : h {0, 3, 4, 7, 10, 11, 13, 14, 15} + h {4, 7, 10, 11, 13, 14, 15} ≤ h {0, 4, 7, 10, 11, 13, 14, 15} + h {3, 4, 7, 10, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e23 : h {0, 1, 3, 4, 6, 10, 11, 13, 14, 15} + h {1, 4, 6, 10, 11, 13, 14, 15} ≤ h {0, 1, 4, 6, 10, 11, 13, 14, 15} + h {1, 3, 4, 6, 10, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e24 : h {0, 3, 7, 11, 13, 14, 15} + h {7, 11, 13, 14, 15} ≤ h {0, 7, 11, 13, 14, 15} + h {3, 7, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e25 : h {0, 3, 11, 13, 14, 15} + h {11, 13, 14, 15} ≤ h {0, 11, 13, 14, 15} + h {3, 11, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e26 : h {0, 3, 9, 10, 13, 14, 15} + h {9, 10, 13, 14, 15} ≤ h {0, 9, 10, 13, 14, 15} + h {3, 9, 10, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e27 : h {0, 3, 4, 6, 8, 10, 13, 14, 15} + h {4, 6, 8, 10, 13, 14, 15} ≤ h {0, 4, 6, 8, 10, 13, 14, 15} + h {3, 4, 6, 8, 10, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e28 : h {0, 3, 6, 8, 10, 13, 14, 15} + h {6, 8, 10, 13, 14, 15} ≤ h {0, 6, 8, 10, 13, 14, 15} + h {3, 6, 8, 10, 13, 14, 15} := hh.elemental (by decide) (by decide)
  have e29 : h {0, 2, 3, 5, 6, 8, 11, 12, 14, 15} + h {2, 5, 6, 8, 11, 12, 14, 15} ≤ h {0, 2, 5, 6, 8, 11, 12, 14, 15} + h {2, 3, 5, 6, 8, 11, 12, 14, 15} := hh.elemental (by decide) (by decide)
  have e30 : h {0, 2, 3, 5, 6, 8, 11, 14, 15} + h {2, 5, 6, 8, 11, 14, 15} ≤ h {0, 2, 5, 6, 8, 11, 14, 15} + h {2, 3, 5, 6, 8, 11, 14, 15} := hh.elemental (by decide) (by decide)
  have e31 : h {0, 2, 3, 9, 11, 12, 14, 15} + h {2, 9, 11, 12, 14, 15} ≤ h {0, 2, 9, 11, 12, 14, 15} + h {2, 3, 9, 11, 12, 14, 15} := hh.elemental (by decide) (by decide)
  have e32 : h {0, 2, 3, 7, 11, 12, 14, 15} + h {2, 7, 11, 12, 14, 15} ≤ h {0, 2, 7, 11, 12, 14, 15} + h {2, 3, 7, 11, 12, 14, 15} := hh.elemental (by decide) (by decide)
  have e33 : h {0, 3, 5, 6, 11, 12, 14, 15} + h {5, 6, 11, 12, 14, 15} ≤ h {0, 5, 6, 11, 12, 14, 15} + h {3, 5, 6, 11, 12, 14, 15} := hh.elemental (by decide) (by decide)
  have e34 : h {0, 3, 5, 6, 10, 11, 14, 15} + h {5, 6, 10, 11, 14, 15} ≤ h {0, 5, 6, 10, 11, 14, 15} + h {3, 5, 6, 10, 11, 14, 15} := hh.elemental (by decide) (by decide)
  have e35 : h {0, 3, 7, 9, 11, 14, 15} + h {7, 9, 11, 14, 15} ≤ h {0, 7, 9, 11, 14, 15} + h {3, 7, 9, 11, 14, 15} := hh.elemental (by decide) (by decide)
  have e36 : h {0, 2, 3, 5, 11, 14, 15} + h {2, 5, 11, 14, 15} ≤ h {0, 2, 5, 11, 14, 15} + h {2, 3, 5, 11, 14, 15} := hh.elemental (by decide) (by decide)
  have e37 : h {0, 3, 11, 14, 15} + h {11, 14, 15} ≤ h {0, 11, 14, 15} + h {3, 11, 14, 15} := hh.elemental (by decide) (by decide)
  have e38 : h {0, 3, 5, 6, 9, 10, 14, 15} + h {5, 6, 9, 10, 14, 15} ≤ h {0, 5, 6, 9, 10, 14, 15} + h {3, 5, 6, 9, 10, 14, 15} := hh.elemental (by decide) (by decide)
  have e39 : h {0, 3, 5, 9, 10, 14, 15} + h {5, 9, 10, 14, 15} ≤ h {0, 5, 9, 10, 14, 15} + h {3, 5, 9, 10, 14, 15} := hh.elemental (by decide) (by decide)
  have e40 : h {0, 3, 5, 10, 14, 15} + h {5, 10, 14, 15} ≤ h {0, 5, 10, 14, 15} + h {3, 5, 10, 14, 15} := hh.elemental (by decide) (by decide)
  have e41 : h {0, 3, 4, 10, 14, 15} + h {4, 10, 14, 15} ≤ h {0, 4, 10, 14, 15} + h {3, 4, 10, 14, 15} := hh.elemental (by decide) (by decide)
  have e42 : h {0, 2, 3, 10, 14, 15} + h {2, 10, 14, 15} ≤ h {0, 2, 10, 14, 15} + h {2, 3, 10, 14, 15} := hh.elemental (by decide) (by decide)
  have e43 : h {0, 3, 10, 14, 15} + h {10, 14, 15} ≤ h {0, 10, 14, 15} + h {3, 10, 14, 15} := hh.elemental (by decide) (by decide)
  have e44 : h {0, 2, 3, 11, 12, 15} + h {2, 11, 12, 15} ≤ h {0, 2, 11, 12, 15} + h {2, 3, 11, 12, 15} := hh.elemental (by decide) (by decide)
  have e45 : h {0, 3, 11, 12, 15} + h {11, 12, 15} ≤ h {0, 11, 12, 15} + h {3, 11, 12, 15} := hh.elemental (by decide) (by decide)
  have e46 : h {0, 2, 3, 5, 10, 12, 15} + h {2, 5, 10, 12, 15} ≤ h {0, 2, 5, 10, 12, 15} + h {2, 3, 5, 10, 12, 15} := hh.elemental (by decide) (by decide)
  have e47 : h {0, 2, 3, 11, 15} + h {2, 11, 15} ≤ h {0, 2, 11, 15} + h {2, 3, 11, 15} := hh.elemental (by decide) (by decide)
  have e48 : h {0, 3, 9, 10, 15} + h {9, 10, 15} ≤ h {0, 9, 10, 15} + h {3, 9, 10, 15} := hh.elemental (by decide) (by decide)
  have e49 : h {0, 3, 4, 8, 15} + h {4, 8, 15} ≤ h {0, 4, 8, 15} + h {3, 4, 8, 15} := hh.elemental (by decide) (by decide)
  have e50 : h {0, 2, 3, 15} + h {2, 15} ≤ h {0, 2, 15} + h {2, 3, 15} := hh.elemental (by decide) (by decide)
  have e51 : h {0, 3, 5, 9, 14} + h {5, 9, 14} ≤ h {0, 5, 9, 14} + h {3, 5, 9, 14} := hh.elemental (by decide) (by decide)
  have e52 : h {0, 3, 9, 14} + h {9, 14} ≤ h {0, 9, 14} + h {3, 9, 14} := hh.elemental (by decide) (by decide)
  have e53 : h {0, 3, 14} + h {14} ≤ h {0, 14} + h {3, 14} := hh.elemental (by decide) (by decide)
  have e54 : h {0, 3} + h ∅ ≤ h {0} + h {3} := hh.elemental (by decide) (by decide)
  have s1 : h {0, 3} = h {1, 2} := by
    have h1 := hinv clebschAut0 clebschAut0_isAut {1, 2}
    rwa [show ({1, 2} : Finset (Fin 16)).map clebschAut0.toEmbedding = {0, 3} by decide] at h1
  have s2 : h {3, 14} = h {1, 2} := by
    have h1 := hinv clebschAut1 clebschAut1_isAut {1, 2}
    rwa [show ({1, 2} : Finset (Fin 16)).map clebschAut1.toEmbedding = {3, 14} by decide] at h1
  have s3 : h {0, 14} = h {1, 2} := by
    have h1 := hinv clebschAut2 clebschAut2_isAut {1, 2}
    rwa [show ({1, 2} : Finset (Fin 16)).map clebschAut2.toEmbedding = {0, 14} by decide] at h1
  have s4 : h {0, 3, 14} = h {1, 2, 4} := by
    have h1 := hinv clebschAut1 clebschAut1_isAut {1, 2, 4}
    rwa [show ({1, 2, 4} : Finset (Fin 16)).map clebschAut1.toEmbedding = {0, 3, 14} by decide] at h1
  have s5 : h {3, 9, 14} = h {1, 2, 4} := by
    have h1 := hinv clebschAut3 clebschAut3_isAut {1, 2, 4}
    rwa [show ({1, 2, 4} : Finset (Fin 16)).map clebschAut3.toEmbedding = {3, 9, 14} by decide] at h1
  have s6 : h {0, 9, 14} = h {1, 2, 4} := by
    have h1 := hinv clebschAut4 clebschAut4_isAut {1, 2, 4}
    rwa [show ({1, 2, 4} : Finset (Fin 16)).map clebschAut4.toEmbedding = {0, 9, 14} by decide] at h1
  have s7 : h {9, 14} = h {1, 2} := by
    have h1 := hinv clebschAut5 clebschAut5_isAut {1, 2}
    rwa [show ({1, 2} : Finset (Fin 16)).map clebschAut5.toEmbedding = {9, 14} by decide] at h1
  have s8 : h {0, 3, 9, 14} = h {1, 2, 4, 8} := by
    have h1 := hinv clebschAut3 clebschAut3_isAut {1, 2, 4, 8}
    rwa [show ({1, 2, 4, 8} : Finset (Fin 16)).map clebschAut3.toEmbedding = {0, 3, 9, 14} by decide] at h1
  have s9 : h {3, 5, 9, 14} = h {1, 2, 4, 8} := by
    have h1 := hinv clebschAut6 clebschAut6_isAut {1, 2, 4, 8}
    rwa [show ({1, 2, 4, 8} : Finset (Fin 16)).map clebschAut6.toEmbedding = {3, 5, 9, 14} by decide] at h1
  have s10 : h {0, 5, 9, 14} = h {1, 2, 4, 8} := by
    have h1 := hinv clebschAut7 clebschAut7_isAut {1, 2, 4, 8}
    rwa [show ({1, 2, 4, 8} : Finset (Fin 16)).map clebschAut7.toEmbedding = {0, 5, 9, 14} by decide] at h1
  have s11 : h {5, 9, 14} = h {1, 2, 4} := by
    have h1 := hinv clebschAut8 clebschAut8_isAut {1, 2, 4}
    rwa [show ({1, 2, 4} : Finset (Fin 16)).map clebschAut8.toEmbedding = {5, 9, 14} by decide] at h1
  have c1 : h {0, 1, 3, 5, 9, 14} = h {0, 3, 5, 9, 14} := hh.eq_of_closure hv (by decide) (by decide)
  have s12 : h {0, 1, 3, 5, 9, 14} = h {0, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut9 clebschAut9_isAut {0, 7, 8, 9, 10, 12}
    rwa [show ({0, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut9.toEmbedding = {0, 1, 3, 5, 9, 14} by decide] at h1
  have s13 : h {2, 3, 15} = h {0, 3, 4} := by
    have h1 := hinv clebschAut10 clebschAut10_isAut {0, 3, 4}
    rwa [show ({0, 3, 4} : Finset (Fin 16)).map clebschAut10.toEmbedding = {2, 3, 15} by decide] at h1
  have s14 : h {0, 2, 15} = h {0, 1, 2} := by
    have h1 := hinv clebschAut11 clebschAut11_isAut {0, 1, 2}
    rwa [show ({0, 1, 2} : Finset (Fin 16)).map clebschAut11.toEmbedding = {0, 2, 15} by decide] at h1
  have s15 : h {2, 15} = h {1, 2} := by
    have h1 := hinv clebschAut11 clebschAut11_isAut {1, 2}
    rwa [show ({1, 2} : Finset (Fin 16)).map clebschAut11.toEmbedding = {2, 15} by decide] at h1
  have s16 : h {0, 2, 3, 15} = h {0, 1, 3, 4} := by
    have h1 := hinv clebschAut10 clebschAut10_isAut {0, 1, 3, 4}
    rwa [show ({0, 1, 3, 4} : Finset (Fin 16)).map clebschAut10.toEmbedding = {0, 2, 3, 15} by decide] at h1
  have s17 : h {3, 4, 8, 15} = h {0, 3, 5, 6} := by
    have h1 := hinv clebschAut12 clebschAut12_isAut {0, 3, 5, 6}
    rwa [show ({0, 3, 5, 6} : Finset (Fin 16)).map clebschAut12.toEmbedding = {3, 4, 8, 15} by decide] at h1
  have s18 : h {0, 4, 8, 15} = h {0, 1, 2, 4} := by
    have h1 := hinv clebschAut13 clebschAut13_isAut {0, 1, 2, 4}
    rwa [show ({0, 1, 2, 4} : Finset (Fin 16)).map clebschAut13.toEmbedding = {0, 4, 8, 15} by decide] at h1
  have s19 : h {4, 8, 15} = h {1, 2, 4} := by
    have h1 := hinv clebschAut13 clebschAut13_isAut {1, 2, 4}
    rwa [show ({1, 2, 4} : Finset (Fin 16)).map clebschAut13.toEmbedding = {4, 8, 15} by decide] at h1
  have s20 : h {0, 3, 4, 8, 15} = h {0, 1, 3, 5, 6} := by
    have h1 := hinv clebschAut14 clebschAut14_isAut {0, 1, 3, 5, 6}
    rwa [show ({0, 1, 3, 5, 6} : Finset (Fin 16)).map clebschAut14.toEmbedding = {0, 3, 4, 8, 15} by decide] at h1
  have s21 : h {3, 9, 10, 15} = h {1, 2, 4, 8} := by
    have h1 := hinv clebschAut15 clebschAut15_isAut {1, 2, 4, 8}
    rwa [show ({1, 2, 4, 8} : Finset (Fin 16)).map clebschAut15.toEmbedding = {3, 9, 10, 15} by decide] at h1
  have s22 : h {0, 9, 10, 15} = h {1, 3, 4, 8} := by
    have h1 := hinv clebschAut16 clebschAut16_isAut {1, 3, 4, 8}
    rwa [show ({1, 3, 4, 8} : Finset (Fin 16)).map clebschAut16.toEmbedding = {0, 9, 10, 15} by decide] at h1
  have s23 : h {9, 10, 15} = h {1, 2, 4} := by
    have h1 := hinv clebschAut17 clebschAut17_isAut {1, 2, 4}
    rwa [show ({1, 2, 4} : Finset (Fin 16)).map clebschAut17.toEmbedding = {9, 10, 15} by decide] at h1
  have s24 : h {0, 3, 9, 10, 15} = h {0, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut18 clebschAut18_isAut {0, 3, 5, 6, 8}
    rwa [show ({0, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut18.toEmbedding = {0, 3, 9, 10, 15} by decide] at h1
  have s25 : h {2, 3, 11, 15} = h {0, 1, 3, 4} := by
    have h1 := hinv clebschAut19 clebschAut19_isAut {0, 1, 3, 4}
    rwa [show ({0, 1, 3, 4} : Finset (Fin 16)).map clebschAut19.toEmbedding = {2, 3, 11, 15} by decide] at h1
  have s26 : h {0, 2, 11, 15} = h {0, 1, 3, 4} := by
    have h1 := hinv clebschAut20 clebschAut20_isAut {0, 1, 3, 4}
    rwa [show ({0, 1, 3, 4} : Finset (Fin 16)).map clebschAut20.toEmbedding = {0, 2, 11, 15} by decide] at h1
  have s27 : h {2, 11, 15} = h {0, 3, 4} := by
    have h1 := hinv clebschAut21 clebschAut21_isAut {0, 3, 4}
    rwa [show ({0, 3, 4} : Finset (Fin 16)).map clebschAut21.toEmbedding = {2, 11, 15} by decide] at h1
  have s28 : h {0, 2, 3, 11, 15} = h {0, 1, 3, 7, 8} := by
    have h1 := hinv clebschAut22 clebschAut22_isAut {0, 1, 3, 7, 8}
    rwa [show ({0, 1, 3, 7, 8} : Finset (Fin 16)).map clebschAut22.toEmbedding = {0, 2, 3, 11, 15} by decide] at h1
  have s29 : h {2, 3, 5, 10, 12, 15} = h {1, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut23 clebschAut23_isAut {1, 2, 3, 4, 5, 8}
    rwa [show ({1, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut23.toEmbedding = {2, 3, 5, 10, 12, 15} by decide] at h1
  have s30 : h {0, 2, 5, 10, 12, 15} = h {1, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut24 clebschAut24_isAut {1, 2, 3, 4, 5, 8}
    rwa [show ({1, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut24.toEmbedding = {0, 2, 5, 10, 12, 15} by decide] at h1
  have s31 : h {2, 5, 10, 12, 15} = h {1, 2, 3, 4, 8} := by
    have h1 := hinv clebschAut23 clebschAut23_isAut {1, 2, 3, 4, 8}
    rwa [show ({1, 2, 3, 4, 8} : Finset (Fin 16)).map clebschAut23.toEmbedding = {2, 5, 10, 12, 15} by decide] at h1
  have s32 : h {0, 2, 3, 5, 10, 12, 15} = h {0, 2, 3, 4, 5, 8, 9} := by
    have h1 := hinv clebschAut25 clebschAut25_isAut {0, 2, 3, 4, 5, 8, 9}
    rwa [show ({0, 2, 3, 4, 5, 8, 9} : Finset (Fin 16)).map clebschAut25.toEmbedding = {0, 2, 3, 5, 10, 12, 15} by decide] at h1
  have s33 : h {3, 11, 12, 15} = h {0, 1, 3, 4} := by
    have h1 := hinv clebschAut26 clebschAut26_isAut {0, 1, 3, 4}
    rwa [show ({0, 1, 3, 4} : Finset (Fin 16)).map clebschAut26.toEmbedding = {3, 11, 12, 15} by decide] at h1
  have s34 : h {0, 11, 12, 15} = h {1, 2, 3, 4} := by
    have h1 := hinv clebschAut14 clebschAut14_isAut {1, 2, 3, 4}
    rwa [show ({1, 2, 3, 4} : Finset (Fin 16)).map clebschAut14.toEmbedding = {0, 11, 12, 15} by decide] at h1
  have s35 : h {11, 12, 15} = h {0, 3, 4} := by
    have h1 := hinv clebschAut27 clebschAut27_isAut {0, 3, 4}
    rwa [show ({0, 3, 4} : Finset (Fin 16)).map clebschAut27.toEmbedding = {11, 12, 15} by decide] at h1
  have s36 : h {0, 3, 11, 12, 15} = h {0, 2, 3, 4, 5} := by
    have h1 := hinv clebschAut28 clebschAut28_isAut {0, 2, 3, 4, 5}
    rwa [show ({0, 2, 3, 4, 5} : Finset (Fin 16)).map clebschAut28.toEmbedding = {0, 3, 11, 12, 15} by decide] at h1
  have s37 : h {2, 3, 11, 12, 15} = h {0, 1, 3, 4, 8} := by
    have h1 := hinv clebschAut29 clebschAut29_isAut {0, 1, 3, 4, 8}
    rwa [show ({0, 1, 3, 4, 8} : Finset (Fin 16)).map clebschAut29.toEmbedding = {2, 3, 11, 12, 15} by decide] at h1
  have s38 : h {0, 2, 11, 12, 15} = h {0, 2, 3, 5, 8} := by
    have h1 := hinv clebschAut30 clebschAut30_isAut {0, 2, 3, 5, 8}
    rwa [show ({0, 2, 3, 5, 8} : Finset (Fin 16)).map clebschAut30.toEmbedding = {0, 2, 11, 12, 15} by decide] at h1
  have s39 : h {2, 11, 12, 15} = h {1, 3, 4, 8} := by
    have h1 := hinv clebschAut29 clebschAut29_isAut {1, 3, 4, 8}
    rwa [show ({1, 3, 4, 8} : Finset (Fin 16)).map clebschAut29.toEmbedding = {2, 11, 12, 15} by decide] at h1
  have s40 : h {0, 2, 3, 11, 12, 15} = h {0, 1, 3, 4, 7, 8} := by
    have h1 := hinv clebschAut31 clebschAut31_isAut {0, 1, 3, 4, 7, 8}
    rwa [show ({0, 1, 3, 4, 7, 8} : Finset (Fin 16)).map clebschAut31.toEmbedding = {0, 2, 3, 11, 12, 15} by decide] at h1
  have s41 : h {3, 10, 14, 15} = h {1, 2, 3, 4} := by
    have h1 := hinv clebschAut32 clebschAut32_isAut {1, 2, 3, 4}
    rwa [show ({1, 2, 3, 4} : Finset (Fin 16)).map clebschAut32.toEmbedding = {3, 10, 14, 15} by decide] at h1
  have s42 : h {0, 10, 14, 15} = h {0, 1, 3, 4} := by
    have h1 := hinv clebschAut33 clebschAut33_isAut {0, 1, 3, 4}
    rwa [show ({0, 1, 3, 4} : Finset (Fin 16)).map clebschAut33.toEmbedding = {0, 10, 14, 15} by decide] at h1
  have s43 : h {10, 14, 15} = h {0, 1, 2} := by
    have h1 := hinv clebschAut34 clebschAut34_isAut {0, 1, 2}
    rwa [show ({0, 1, 2} : Finset (Fin 16)).map clebschAut34.toEmbedding = {10, 14, 15} by decide] at h1
  have s44 : h {0, 3, 10, 14, 15} = h {0, 2, 3, 5, 8} := by
    have h1 := hinv clebschAut35 clebschAut35_isAut {0, 2, 3, 5, 8}
    rwa [show ({0, 2, 3, 5, 8} : Finset (Fin 16)).map clebschAut35.toEmbedding = {0, 3, 10, 14, 15} by decide] at h1
  have s45 : h {2, 3, 10, 14, 15} = h {0, 2, 3, 4, 5} := by
    have h1 := hinv clebschAut36 clebschAut36_isAut {0, 2, 3, 4, 5}
    rwa [show ({0, 2, 3, 4, 5} : Finset (Fin 16)).map clebschAut36.toEmbedding = {2, 3, 10, 14, 15} by decide] at h1
  have s46 : h {0, 2, 10, 14, 15} = h {0, 1, 3, 7, 8} := by
    have h1 := hinv clebschAut37 clebschAut37_isAut {0, 1, 3, 7, 8}
    rwa [show ({0, 1, 3, 7, 8} : Finset (Fin 16)).map clebschAut37.toEmbedding = {0, 2, 10, 14, 15} by decide] at h1
  have s47 : h {2, 10, 14, 15} = h {0, 1, 3, 4} := by
    have h1 := hinv clebschAut38 clebschAut38_isAut {0, 1, 3, 4}
    rwa [show ({0, 1, 3, 4} : Finset (Fin 16)).map clebschAut38.toEmbedding = {2, 10, 14, 15} by decide] at h1
  have s48 : h {0, 2, 3, 10, 14, 15} = h {0, 1, 3, 4, 7, 8} := by
    have h1 := hinv clebschAut39 clebschAut39_isAut {0, 1, 3, 4, 7, 8}
    rwa [show ({0, 1, 3, 4, 7, 8} : Finset (Fin 16)).map clebschAut39.toEmbedding = {0, 2, 3, 10, 14, 15} by decide] at h1
  have s49 : h {3, 4, 10, 14, 15} = h {1, 2, 3, 4, 8} := by
    have h1 := hinv clebschAut32 clebschAut32_isAut {1, 2, 3, 4, 8}
    rwa [show ({1, 2, 3, 4, 8} : Finset (Fin 16)).map clebschAut32.toEmbedding = {3, 4, 10, 14, 15} by decide] at h1
  have s50 : h {0, 4, 10, 14, 15} = h {0, 2, 3, 4, 5} := by
    have h1 := hinv clebschAut40 clebschAut40_isAut {0, 2, 3, 4, 5}
    rwa [show ({0, 2, 3, 4, 5} : Finset (Fin 16)).map clebschAut40.toEmbedding = {0, 4, 10, 14, 15} by decide] at h1
  have s51 : h {4, 10, 14, 15} = h {1, 2, 3, 4} := by
    have h1 := hinv clebschAut41 clebschAut41_isAut {1, 2, 3, 4}
    rwa [show ({1, 2, 3, 4} : Finset (Fin 16)).map clebschAut41.toEmbedding = {4, 10, 14, 15} by decide] at h1
  have s52 : h {0, 3, 4, 10, 14, 15} = h {1, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut42 clebschAut42_isAut {1, 2, 3, 4, 5, 8}
    rwa [show ({1, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut42.toEmbedding = {0, 3, 4, 10, 14, 15} by decide] at h1
  have s53 : h {3, 5, 10, 14, 15} = h {0, 2, 3, 5, 8} := by
    have h1 := hinv clebschAut43 clebschAut43_isAut {0, 2, 3, 5, 8}
    rwa [show ({0, 2, 3, 5, 8} : Finset (Fin 16)).map clebschAut43.toEmbedding = {3, 5, 10, 14, 15} by decide] at h1
  have s54 : h {0, 5, 10, 14, 15} = h {0, 2, 3, 4, 5} := by
    have h1 := hinv clebschAut44 clebschAut44_isAut {0, 2, 3, 4, 5}
    rwa [show ({0, 2, 3, 4, 5} : Finset (Fin 16)).map clebschAut44.toEmbedding = {0, 5, 10, 14, 15} by decide] at h1
  have s55 : h {5, 10, 14, 15} = h {0, 1, 3, 4} := by
    have h1 := hinv clebschAut45 clebschAut45_isAut {0, 1, 3, 4}
    rwa [show ({0, 1, 3, 4} : Finset (Fin 16)).map clebschAut45.toEmbedding = {5, 10, 14, 15} by decide] at h1
  have s56 : h {0, 3, 5, 10, 14, 15} = h {1, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut46 clebschAut46_isAut {1, 2, 3, 4, 5, 8}
    rwa [show ({1, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut46.toEmbedding = {0, 3, 5, 10, 14, 15} by decide] at h1
  have s57 : h {3, 5, 9, 10, 14, 15} = h {0, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut47 clebschAut47_isAut {0, 3, 5, 6, 8, 9}
    rwa [show ({0, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut47.toEmbedding = {3, 5, 9, 10, 14, 15} by decide] at h1
  have s58 : h {0, 5, 9, 10, 14, 15} = h {1, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut48 clebschAut48_isAut {1, 2, 3, 4, 5, 8}
    rwa [show ({1, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut48.toEmbedding = {0, 5, 9, 10, 14, 15} by decide] at h1
  have s59 : h {5, 9, 10, 14, 15} = h {0, 2, 3, 5, 8} := by
    have h1 := hinv clebschAut49 clebschAut49_isAut {0, 2, 3, 5, 8}
    rwa [show ({0, 2, 3, 5, 8} : Finset (Fin 16)).map clebschAut49.toEmbedding = {5, 9, 10, 14, 15} by decide] at h1
  have c2 : h {0, 1, 3, 5, 9, 10, 14, 15} = h {0, 3, 5, 9, 10, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s60 : h {0, 1, 3, 5, 9, 10, 14, 15} = h {0, 1, 2, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut50 clebschAut50_isAut {0, 1, 2, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut50.toEmbedding = {0, 1, 3, 5, 9, 10, 14, 15} by decide] at h1
  have s61 : h {3, 5, 6, 9, 10, 14, 15} = h {0, 3, 4, 5, 6, 9, 10} := by
    have h1 := hinv clebschAut51 clebschAut51_isAut {0, 3, 4, 5, 6, 9, 10}
    rwa [show ({0, 3, 4, 5, 6, 9, 10} : Finset (Fin 16)).map clebschAut51.toEmbedding = {3, 5, 6, 9, 10, 14, 15} by decide] at h1
  have s62 : h {0, 5, 6, 9, 10, 14, 15} = h {0, 2, 3, 4, 5, 8, 9} := by
    have h1 := hinv clebschAut44 clebschAut44_isAut {0, 2, 3, 4, 5, 8, 9}
    rwa [show ({0, 2, 3, 4, 5, 8, 9} : Finset (Fin 16)).map clebschAut44.toEmbedding = {0, 5, 6, 9, 10, 14, 15} by decide] at h1
  have s63 : h {5, 6, 9, 10, 14, 15} = h {0, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut52 clebschAut52_isAut {0, 2, 3, 4, 5, 8}
    rwa [show ({0, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut52.toEmbedding = {5, 6, 9, 10, 14, 15} by decide] at h1
  have c3 : h {0, 1, 3, 5, 6, 9, 10, 14, 15} = h {0, 3, 5, 6, 9, 10, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s64 : h {0, 1, 3, 5, 6, 9, 10, 14, 15} = h {0, 1, 2, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut50 clebschAut50_isAut {0, 1, 2, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut50.toEmbedding = {0, 1, 3, 5, 6, 9, 10, 14, 15} by decide] at h1
  have s65 : h {3, 11, 14, 15} = h {0, 1, 3, 4} := by
    have h1 := hinv clebschAut53 clebschAut53_isAut {0, 1, 3, 4}
    rwa [show ({0, 1, 3, 4} : Finset (Fin 16)).map clebschAut53.toEmbedding = {3, 11, 14, 15} by decide] at h1
  have s66 : h {0, 11, 14, 15} = h {0, 1, 2, 4} := by
    have h1 := hinv clebschAut40 clebschAut40_isAut {0, 1, 2, 4}
    rwa [show ({0, 1, 2, 4} : Finset (Fin 16)).map clebschAut40.toEmbedding = {0, 11, 14, 15} by decide] at h1
  have s67 : h {11, 14, 15} = h {0, 1, 2} := by
    have h1 := hinv clebschAut54 clebschAut54_isAut {0, 1, 2}
    rwa [show ({0, 1, 2} : Finset (Fin 16)).map clebschAut54.toEmbedding = {11, 14, 15} by decide] at h1
  have s68 : h {0, 3, 11, 14, 15} = h {0, 1, 3, 4, 8} := by
    have h1 := hinv clebschAut55 clebschAut55_isAut {0, 1, 3, 4, 8}
    rwa [show ({0, 1, 3, 4, 8} : Finset (Fin 16)).map clebschAut55.toEmbedding = {0, 3, 11, 14, 15} by decide] at h1
  have s69 : h {2, 3, 5, 11, 14, 15} = h {1, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut36 clebschAut36_isAut {1, 2, 3, 4, 5, 8}
    rwa [show ({1, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut36.toEmbedding = {2, 3, 5, 11, 14, 15} by decide] at h1
  have s70 : h {0, 2, 5, 11, 14, 15} = h {0, 1, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut56 clebschAut56_isAut {0, 1, 3, 5, 6, 8}
    rwa [show ({0, 1, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut56.toEmbedding = {0, 2, 5, 11, 14, 15} by decide] at h1
  have s71 : h {2, 5, 11, 14, 15} = h {1, 2, 3, 4, 8} := by
    have h1 := hinv clebschAut38 clebschAut38_isAut {1, 2, 3, 4, 8}
    rwa [show ({1, 2, 3, 4, 8} : Finset (Fin 16)).map clebschAut38.toEmbedding = {2, 5, 11, 14, 15} by decide] at h1
  have s72 : h {0, 2, 3, 5, 11, 14, 15} = h {0, 2, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut41 clebschAut41_isAut {0, 2, 3, 5, 6, 8, 9}
    rwa [show ({0, 2, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut41.toEmbedding = {0, 2, 3, 5, 11, 14, 15} by decide] at h1
  have s73 : h {3, 7, 9, 11, 14, 15} = h {0, 1, 2, 3, 5, 8} := by
    have h1 := hinv clebschAut57 clebschAut57_isAut {0, 1, 2, 3, 5, 8}
    rwa [show ({0, 1, 2, 3, 5, 8} : Finset (Fin 16)).map clebschAut57.toEmbedding = {3, 7, 9, 11, 14, 15} by decide] at h1
  have s74 : h {0, 7, 9, 11, 14, 15} = h {0, 1, 2, 4, 7, 8} := by
    have h1 := hinv clebschAut58 clebschAut58_isAut {0, 1, 2, 4, 7, 8}
    rwa [show ({0, 1, 2, 4, 7, 8} : Finset (Fin 16)).map clebschAut58.toEmbedding = {0, 7, 9, 11, 14, 15} by decide] at h1
  have s75 : h {7, 9, 11, 14, 15} = h {0, 1, 3, 4, 8} := by
    have h1 := hinv clebschAut59 clebschAut59_isAut {0, 1, 3, 4, 8}
    rwa [show ({0, 1, 3, 4, 8} : Finset (Fin 16)).map clebschAut59.toEmbedding = {7, 9, 11, 14, 15} by decide] at h1
  have s76 : h {0, 3, 7, 9, 11, 14, 15} = h {0, 1, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut60 clebschAut60_isAut {0, 1, 3, 5, 6, 8, 9}
    rwa [show ({0, 1, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut60.toEmbedding = {0, 3, 7, 9, 11, 14, 15} by decide] at h1
  have s77 : h {3, 5, 6, 10, 11, 14, 15} = h {0, 1, 2, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut38 clebschAut38_isAut {0, 1, 2, 3, 5, 6, 8}
    rwa [show ({0, 1, 2, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut38.toEmbedding = {3, 5, 6, 10, 11, 14, 15} by decide] at h1
  have s78 : h {0, 5, 6, 10, 11, 14, 15} = h {0, 1, 2, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut34 clebschAut34_isAut {0, 1, 2, 3, 5, 6, 8}
    rwa [show ({0, 1, 2, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut34.toEmbedding = {0, 5, 6, 10, 11, 14, 15} by decide] at h1
  have s79 : h {5, 6, 10, 11, 14, 15} = h {0, 1, 2, 3, 5, 8} := by
    have h1 := hinv clebschAut34 clebschAut34_isAut {0, 1, 2, 3, 5, 8}
    rwa [show ({0, 1, 2, 3, 5, 8} : Finset (Fin 16)).map clebschAut34.toEmbedding = {5, 6, 10, 11, 14, 15} by decide] at h1
  have s80 : h {0, 3, 5, 6, 10, 11, 14, 15} = h {0, 1, 2, 3, 4, 7, 9, 10} := by
    have h1 := hinv clebschAut32 clebschAut32_isAut {0, 1, 2, 3, 4, 7, 9, 10}
    rwa [show ({0, 1, 2, 3, 4, 7, 9, 10} : Finset (Fin 16)).map clebschAut32.toEmbedding = {0, 3, 5, 6, 10, 11, 14, 15} by decide] at h1
  have s81 : h {3, 5, 6, 11, 12, 14, 15} = h {0, 2, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut61 clebschAut61_isAut {0, 2, 3, 5, 6, 8, 9}
    rwa [show ({0, 2, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut61.toEmbedding = {3, 5, 6, 11, 12, 14, 15} by decide] at h1
  have c4 : h {0, 4, 5, 6, 11, 12, 14, 15} = h {0, 5, 6, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s82 : h {0, 4, 5, 6, 11, 12, 14, 15} = h {0, 1, 3, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut53 clebschAut53_isAut {0, 1, 3, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 3, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut53.toEmbedding = {0, 4, 5, 6, 11, 12, 14, 15} by decide] at h1
  have s83 : h {5, 6, 11, 12, 14, 15} = h {0, 1, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut62 clebschAut62_isAut {0, 1, 3, 5, 6, 8}
    rwa [show ({0, 1, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut62.toEmbedding = {5, 6, 11, 12, 14, 15} by decide] at h1
  have c5 : h {0, 3, 4, 5, 6, 11, 12, 14, 15} = h {0, 3, 5, 6, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s84 : h {0, 3, 4, 5, 6, 11, 12, 14, 15} = h {0, 1, 3, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut53 clebschAut53_isAut {0, 1, 3, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 3, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut53.toEmbedding = {0, 3, 4, 5, 6, 11, 12, 14, 15} by decide] at h1
  have s85 : h {2, 3, 7, 11, 12, 14, 15} = h {0, 1, 2, 3, 4, 7, 8} := by
    have h1 := hinv clebschAut29 clebschAut29_isAut {0, 1, 2, 3, 4, 7, 8}
    rwa [show ({0, 1, 2, 3, 4, 7, 8} : Finset (Fin 16)).map clebschAut29.toEmbedding = {2, 3, 7, 11, 12, 14, 15} by decide] at h1
  have s86 : h {0, 2, 7, 11, 12, 14, 15} = h {0, 1, 3, 5, 6, 9, 10} := by
    have h1 := hinv clebschAut63 clebschAut63_isAut {0, 1, 3, 5, 6, 9, 10}
    rwa [show ({0, 1, 3, 5, 6, 9, 10} : Finset (Fin 16)).map clebschAut63.toEmbedding = {0, 2, 7, 11, 12, 14, 15} by decide] at h1
  have s87 : h {2, 7, 11, 12, 14, 15} = h {0, 1, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut64 clebschAut64_isAut {0, 1, 3, 5, 6, 8}
    rwa [show ({0, 1, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut64.toEmbedding = {2, 7, 11, 12, 14, 15} by decide] at h1
  have s88 : h {0, 2, 3, 7, 11, 12, 14, 15} = h {0, 1, 2, 3, 5, 6, 9, 10} := by
    have h1 := hinv clebschAut63 clebschAut63_isAut {0, 1, 2, 3, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 3, 5, 6, 9, 10} : Finset (Fin 16)).map clebschAut63.toEmbedding = {0, 2, 3, 7, 11, 12, 14, 15} by decide] at h1
  have s89 : h {2, 3, 9, 11, 12, 14, 15} = h {1, 2, 3, 4, 6, 8, 9} := by
    have h1 := hinv clebschAut65 clebschAut65_isAut {1, 2, 3, 4, 6, 8, 9}
    rwa [show ({1, 2, 3, 4, 6, 8, 9} : Finset (Fin 16)).map clebschAut65.toEmbedding = {2, 3, 9, 11, 12, 14, 15} by decide] at h1
  have s90 : h {0, 2, 9, 11, 12, 14, 15} = h {0, 2, 3, 4, 5, 8, 9} := by
    have h1 := hinv clebschAut66 clebschAut66_isAut {0, 2, 3, 4, 5, 8, 9}
    rwa [show ({0, 2, 3, 4, 5, 8, 9} : Finset (Fin 16)).map clebschAut66.toEmbedding = {0, 2, 9, 11, 12, 14, 15} by decide] at h1
  have s91 : h {2, 9, 11, 12, 14, 15} = h {1, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut67 clebschAut67_isAut {1, 2, 3, 4, 5, 8}
    rwa [show ({1, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut67.toEmbedding = {2, 9, 11, 12, 14, 15} by decide] at h1
  have s92 : h {0, 2, 3, 9, 11, 12, 14, 15} = h {1, 2, 3, 4, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut68 clebschAut68_isAut {1, 2, 3, 4, 5, 6, 8, 9}
    rwa [show ({1, 2, 3, 4, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut68.toEmbedding = {0, 2, 3, 9, 11, 12, 14, 15} by decide] at h1
  have c6 : h {2, 3, 5, 6, 7, 8, 10, 11, 14, 15} = h {2, 3, 5, 6, 8, 11, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s93 : h {2, 3, 5, 6, 7, 8, 10, 11, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 11, 12} := by
    have h1 := hinv clebschAut57 clebschAut57_isAut {0, 1, 2, 3, 4, 5, 6, 7, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 11, 12} : Finset (Fin 16)).map clebschAut57.toEmbedding = {2, 3, 5, 6, 7, 8, 10, 11, 14, 15} by decide] at h1
  have c7 : h {0, 2, 5, 6, 8, 10, 11, 14, 15} = h {0, 2, 5, 6, 8, 11, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s94 : h {0, 2, 5, 6, 8, 10, 11, 14, 15} = h {0, 1, 3, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut69 clebschAut69_isAut {0, 1, 3, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 3, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut69.toEmbedding = {0, 2, 5, 6, 8, 10, 11, 14, 15} by decide] at h1
  have c8 : h {2, 5, 6, 8, 10, 11, 14, 15} = h {2, 5, 6, 8, 11, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s95 : h {2, 5, 6, 8, 10, 11, 14, 15} = h {0, 1, 2, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut70 clebschAut70_isAut {0, 1, 2, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut70.toEmbedding = {2, 5, 6, 8, 10, 11, 14, 15} by decide] at h1
  have c9 : h {0, 2, 3, 5, 6, 7, 8, 10, 11, 14, 15} = h {0, 2, 3, 5, 6, 8, 11, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s96 : h {0, 2, 3, 5, 6, 7, 8, 10, 11, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} := by
    have h1 := hinv clebschAut71 clebschAut71_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} : Finset (Fin 16)).map clebschAut71.toEmbedding = {0, 2, 3, 5, 6, 7, 8, 10, 11, 14, 15} by decide] at h1
  have c10 : h {2, 3, 5, 6, 7, 8, 10, 11, 12, 14, 15} = h {2, 3, 5, 6, 8, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s97 : h {2, 3, 5, 6, 7, 8, 10, 11, 12, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} := by
    have h1 := hinv clebschAut64 clebschAut64_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} : Finset (Fin 16)).map clebschAut64.toEmbedding = {2, 3, 5, 6, 7, 8, 10, 11, 12, 14, 15} by decide] at h1
  have c11 : h {0, 2, 4, 5, 6, 8, 10, 11, 12, 14, 15} = h {0, 2, 5, 6, 8, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s98 : h {0, 2, 4, 5, 6, 8, 10, 11, 12, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} := by
    have h1 := hinv clebschAut37 clebschAut37_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} : Finset (Fin 16)).map clebschAut37.toEmbedding = {0, 2, 4, 5, 6, 8, 10, 11, 12, 14, 15} by decide] at h1
  have c12 : h {2, 5, 6, 8, 10, 11, 12, 14, 15} = h {2, 5, 6, 8, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s99 : h {2, 5, 6, 8, 10, 11, 12, 14, 15} = h {0, 1, 2, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut72 clebschAut72_isAut {0, 1, 2, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut72.toEmbedding = {2, 5, 6, 8, 10, 11, 12, 14, 15} by decide] at h1
  have c13 : h {0, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15} = h {0, 2, 3, 5, 6, 8, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s100 : h {0, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by
    have h1 := hinv clebschAut73 clebschAut73_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} : Finset (Fin 16)).map clebschAut73.toEmbedding = {0, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15} by decide] at h1
  have s101 : h {3, 6, 8, 10, 13, 14, 15} = h {0, 3, 4, 5, 6, 9, 10} := by
    have h1 := hinv clebschAut74 clebschAut74_isAut {0, 3, 4, 5, 6, 9, 10}
    rwa [show ({0, 3, 4, 5, 6, 9, 10} : Finset (Fin 16)).map clebschAut74.toEmbedding = {3, 6, 8, 10, 13, 14, 15} by decide] at h1
  have s102 : h {0, 6, 8, 10, 13, 14, 15} = h {1, 2, 3, 4, 6, 8, 9} := by
    have h1 := hinv clebschAut75 clebschAut75_isAut {1, 2, 3, 4, 6, 8, 9}
    rwa [show ({1, 2, 3, 4, 6, 8, 9} : Finset (Fin 16)).map clebschAut75.toEmbedding = {0, 6, 8, 10, 13, 14, 15} by decide] at h1
  have s103 : h {6, 8, 10, 13, 14, 15} = h {0, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut76 clebschAut76_isAut {0, 2, 3, 4, 5, 8}
    rwa [show ({0, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut76.toEmbedding = {6, 8, 10, 13, 14, 15} by decide] at h1
  have c14 : h {0, 2, 3, 6, 8, 10, 13, 14, 15} = h {0, 3, 6, 8, 10, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s104 : h {0, 2, 3, 6, 8, 10, 13, 14, 15} = h {0, 1, 3, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut77 clebschAut77_isAut {0, 1, 3, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 3, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut77.toEmbedding = {0, 2, 3, 6, 8, 10, 13, 14, 15} by decide] at h1
  have c15 : h {3, 4, 6, 8, 10, 12, 13, 14, 15} = h {3, 4, 6, 8, 10, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s105 : h {3, 4, 6, 8, 10, 12, 13, 14, 15} = h {0, 1, 2, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut64 clebschAut64_isAut {0, 1, 2, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut64.toEmbedding = {3, 4, 6, 8, 10, 12, 13, 14, 15} by decide] at h1
  have s106 : h {0, 4, 6, 8, 10, 13, 14, 15} = h {1, 2, 3, 4, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut75 clebschAut75_isAut {1, 2, 3, 4, 5, 6, 8, 9}
    rwa [show ({1, 2, 3, 4, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut75.toEmbedding = {0, 4, 6, 8, 10, 13, 14, 15} by decide] at h1
  have s107 : h {4, 6, 8, 10, 13, 14, 15} = h {0, 2, 3, 4, 5, 8, 9} := by
    have h1 := hinv clebschAut76 clebschAut76_isAut {0, 2, 3, 4, 5, 8, 9}
    rwa [show ({0, 2, 3, 4, 5, 8, 9} : Finset (Fin 16)).map clebschAut76.toEmbedding = {4, 6, 8, 10, 13, 14, 15} by decide] at h1
  have c16 : h {0, 2, 3, 4, 6, 8, 10, 12, 13, 14, 15} = h {0, 3, 4, 6, 8, 10, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s108 : h {0, 2, 3, 4, 6, 8, 10, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} := by
    have h1 := hinv clebschAut78 clebschAut78_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} : Finset (Fin 16)).map clebschAut78.toEmbedding = {0, 2, 3, 4, 6, 8, 10, 12, 13, 14, 15} by decide] at h1
  have s109 : h {3, 9, 10, 13, 14, 15} = h {1, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut79 clebschAut79_isAut {1, 2, 3, 4, 5, 8}
    rwa [show ({1, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut79.toEmbedding = {3, 9, 10, 13, 14, 15} by decide] at h1
  have s110 : h {0, 9, 10, 13, 14, 15} = h {0, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut80 clebschAut80_isAut {0, 2, 3, 4, 5, 8}
    rwa [show ({0, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut80.toEmbedding = {0, 9, 10, 13, 14, 15} by decide] at h1
  have s111 : h {9, 10, 13, 14, 15} = h {0, 2, 3, 4, 5} := by
    have h1 := hinv clebschAut80 clebschAut80_isAut {0, 2, 3, 4, 5}
    rwa [show ({0, 2, 3, 4, 5} : Finset (Fin 16)).map clebschAut80.toEmbedding = {9, 10, 13, 14, 15} by decide] at h1
  have s112 : h {0, 3, 9, 10, 13, 14, 15} = h {0, 3, 4, 5, 6, 9, 10} := by
    have h1 := hinv clebschAut81 clebschAut81_isAut {0, 3, 4, 5, 6, 9, 10}
    rwa [show ({0, 3, 4, 5, 6, 9, 10} : Finset (Fin 16)).map clebschAut81.toEmbedding = {0, 3, 9, 10, 13, 14, 15} by decide] at h1
  have s113 : h {3, 11, 13, 14, 15} = h {0, 1, 3, 4, 8} := by
    have h1 := hinv clebschAut82 clebschAut82_isAut {0, 1, 3, 4, 8}
    rwa [show ({0, 1, 3, 4, 8} : Finset (Fin 16)).map clebschAut82.toEmbedding = {3, 11, 13, 14, 15} by decide] at h1
  have s114 : h {0, 11, 13, 14, 15} = h {0, 1, 2, 4, 8} := by
    have h1 := hinv clebschAut66 clebschAut66_isAut {0, 1, 2, 4, 8}
    rwa [show ({0, 1, 2, 4, 8} : Finset (Fin 16)).map clebschAut66.toEmbedding = {0, 11, 13, 14, 15} by decide] at h1
  have s115 : h {11, 13, 14, 15} = h {0, 1, 2, 4} := by
    have h1 := hinv clebschAut80 clebschAut80_isAut {0, 1, 2, 4}
    rwa [show ({0, 1, 2, 4} : Finset (Fin 16)).map clebschAut80.toEmbedding = {11, 13, 14, 15} by decide] at h1
  have s116 : h {0, 3, 11, 13, 14, 15} = h {0, 1, 2, 4, 7, 8} := by
    have h1 := hinv clebschAut83 clebschAut83_isAut {0, 1, 2, 4, 7, 8}
    rwa [show ({0, 1, 2, 4, 7, 8} : Finset (Fin 16)).map clebschAut83.toEmbedding = {0, 3, 11, 13, 14, 15} by decide] at h1
  have s117 : h {3, 7, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 8} := by
    have h1 := hinv clebschAut51 clebschAut51_isAut {0, 1, 2, 3, 4, 8}
    rwa [show ({0, 1, 2, 3, 4, 8} : Finset (Fin 16)).map clebschAut51.toEmbedding = {3, 7, 11, 13, 14, 15} by decide] at h1
  have s118 : h {0, 7, 11, 13, 14, 15} = h {0, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut15 clebschAut15_isAut {0, 7, 8, 9, 10, 12}
    rwa [show ({0, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut15.toEmbedding = {0, 7, 11, 13, 14, 15} by decide] at h1
  have s119 : h {7, 11, 13, 14, 15} = h {0, 1, 2, 4, 8} := by
    have h1 := hinv clebschAut51 clebschAut51_isAut {0, 1, 2, 4, 8}
    rwa [show ({0, 1, 2, 4, 8} : Finset (Fin 16)).map clebschAut51.toEmbedding = {7, 11, 13, 14, 15} by decide] at h1
  have s120 : h {0, 3, 7, 11, 13, 14, 15} = h {0, 1, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut15 clebschAut15_isAut {0, 1, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut15.toEmbedding = {0, 3, 7, 11, 13, 14, 15} by decide] at h1
  have s121 : h {1, 3, 4, 6, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 5, 6, 9, 10, 12} := by
    have h1 := hinv clebschAut38 clebschAut38_isAut {0, 1, 2, 3, 5, 6, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 5, 6, 9, 10, 12} : Finset (Fin 16)).map clebschAut38.toEmbedding = {1, 3, 4, 6, 10, 11, 13, 14, 15} by decide] at h1
  have s122 : h {0, 1, 4, 6, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 7, 9, 10} := by
    have h1 := hinv clebschAut84 clebschAut84_isAut {0, 1, 2, 3, 4, 5, 7, 9, 10}
    rwa [show ({0, 1, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 16)).map clebschAut84.toEmbedding = {0, 1, 4, 6, 10, 11, 13, 14, 15} by decide] at h1
  have s123 : h {1, 4, 6, 10, 11, 13, 14, 15} = h {0, 1, 3, 4, 5, 6, 9, 10} := by
    have h1 := hinv clebschAut85 clebschAut85_isAut {0, 1, 3, 4, 5, 6, 9, 10}
    rwa [show ({0, 1, 3, 4, 5, 6, 9, 10} : Finset (Fin 16)).map clebschAut85.toEmbedding = {1, 4, 6, 10, 11, 13, 14, 15} by decide] at h1
  have c17 : h {0, 1, 2, 3, 4, 6, 10, 11, 13, 14, 15} = h {0, 1, 3, 4, 6, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s124 : h {0, 1, 2, 3, 4, 6, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut56 clebschAut56_isAut {0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut56.toEmbedding = {0, 1, 2, 3, 4, 6, 10, 11, 13, 14, 15} by decide] at h1
  have s125 : h {3, 4, 7, 10, 11, 13, 14, 15} = h {0, 1, 3, 4, 5, 7, 9, 10} := by
    have h1 := hinv clebschAut36 clebschAut36_isAut {0, 1, 3, 4, 5, 7, 9, 10}
    rwa [show ({0, 1, 3, 4, 5, 7, 9, 10} : Finset (Fin 16)).map clebschAut36.toEmbedding = {3, 4, 7, 10, 11, 13, 14, 15} by decide] at h1
  have s126 : h {0, 4, 7, 10, 11, 13, 14, 15} = h {0, 1, 2, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut86 clebschAut86_isAut {0, 1, 2, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut86.toEmbedding = {0, 4, 7, 10, 11, 13, 14, 15} by decide] at h1
  have s127 : h {4, 7, 10, 11, 13, 14, 15} = h {0, 1, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut87 clebschAut87_isAut {0, 1, 3, 5, 6, 8, 9}
    rwa [show ({0, 1, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut87.toEmbedding = {4, 7, 10, 11, 13, 14, 15} by decide] at h1
  have s128 : h {0, 3, 4, 7, 10, 11, 13, 14, 15} = h {0, 1, 2, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut86 clebschAut86_isAut {0, 1, 2, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut86.toEmbedding = {0, 3, 4, 7, 10, 11, 13, 14, 15} by decide] at h1
  have c18 : h {3, 4, 8, 10, 11, 12, 13, 14, 15} = h {3, 4, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s129 : h {3, 4, 8, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut88 clebschAut88_isAut {0, 1, 2, 3, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut88.toEmbedding = {3, 4, 8, 10, 11, 12, 13, 14, 15} by decide] at h1
  have s130 : h {0, 4, 8, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut89 clebschAut89_isAut {0, 1, 2, 3, 5, 6, 8, 9}
    rwa [show ({0, 1, 2, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut89.toEmbedding = {0, 4, 8, 10, 11, 13, 14, 15} by decide] at h1
  have s131 : h {4, 8, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut89 clebschAut89_isAut {0, 1, 2, 3, 5, 6, 8}
    rwa [show ({0, 1, 2, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut89.toEmbedding = {4, 8, 10, 11, 13, 14, 15} by decide] at h1
  have c19 : h {0, 3, 4, 8, 10, 11, 12, 13, 14, 15} = h {0, 3, 4, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s132 : h {0, 3, 4, 8, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 5, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut90 clebschAut90_isAut {0, 1, 2, 3, 5, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 5, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut90.toEmbedding = {0, 3, 4, 8, 10, 11, 12, 13, 14, 15} by decide] at h1
  have s133 : h {3, 5, 8, 10, 11, 13, 14, 15} = h {0, 1, 3, 4, 5, 6, 9, 10} := by
    have h1 := hinv clebschAut91 clebschAut91_isAut {0, 1, 3, 4, 5, 6, 9, 10}
    rwa [show ({0, 1, 3, 4, 5, 6, 9, 10} : Finset (Fin 16)).map clebschAut91.toEmbedding = {3, 5, 8, 10, 11, 13, 14, 15} by decide] at h1
  have s134 : h {0, 5, 8, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 5, 6, 9, 10} := by
    have h1 := hinv clebschAut88 clebschAut88_isAut {0, 1, 2, 3, 5, 6, 9, 10}
    rwa [show ({0, 1, 2, 3, 5, 6, 9, 10} : Finset (Fin 16)).map clebschAut88.toEmbedding = {0, 5, 8, 10, 11, 13, 14, 15} by decide] at h1
  have s135 : h {5, 8, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 7, 8} := by
    have h1 := hinv clebschAut49 clebschAut49_isAut {0, 1, 2, 3, 4, 7, 8}
    rwa [show ({0, 1, 2, 3, 4, 7, 8} : Finset (Fin 16)).map clebschAut49.toEmbedding = {5, 8, 10, 11, 13, 14, 15} by decide] at h1
  have s136 : h {0, 3, 5, 8, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 5, 6, 9, 10, 12} := by
    have h1 := hinv clebschAut88 clebschAut88_isAut {0, 1, 2, 3, 5, 6, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 5, 6, 9, 10, 12} : Finset (Fin 16)).map clebschAut88.toEmbedding = {0, 3, 5, 8, 10, 11, 13, 14, 15} by decide] at h1
  have c20 : h {1, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} = h {1, 3, 4, 7, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s137 : h {1, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12} := by
    have h1 := hinv clebschAut92 clebschAut92_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12} : Finset (Fin 16)).map clebschAut92.toEmbedding = {1, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c21 : h {0, 1, 4, 5, 7, 8, 10, 11, 13, 14, 15} = h {0, 1, 4, 7, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s138 : h {0, 1, 4, 5, 7, 8, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} := by
    have h1 := hinv clebschAut93 clebschAut93_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} : Finset (Fin 16)).map clebschAut93.toEmbedding = {0, 1, 4, 5, 7, 8, 10, 11, 13, 14, 15} by decide] at h1
  have c22 : h {1, 4, 5, 7, 8, 10, 11, 13, 14, 15} = h {1, 4, 7, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s139 : h {1, 4, 5, 7, 8, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut49 clebschAut49_isAut {0, 1, 2, 3, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut49.toEmbedding = {1, 4, 5, 7, 8, 10, 11, 13, 14, 15} by decide] at h1
  have c23 : h {0, 1, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} = h {0, 1, 3, 4, 7, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s140 : h {0, 1, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by
    have h1 := hinv clebschAut14 clebschAut14_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} : Finset (Fin 16)).map clebschAut14.toEmbedding = {0, 1, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} by decide] at h1
  have s141 : h {3, 4, 7, 9, 10, 11, 13, 14, 15} = h {0, 1, 2, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut62 clebschAut62_isAut {0, 1, 2, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut62.toEmbedding = {3, 4, 7, 9, 10, 11, 13, 14, 15} by decide] at h1
  have s142 : h {0, 4, 7, 9, 10, 11, 13, 14, 15} = h {0, 1, 2, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut94 clebschAut94_isAut {0, 1, 2, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut94.toEmbedding = {0, 4, 7, 9, 10, 11, 13, 14, 15} by decide] at h1
  have s143 : h {4, 7, 9, 10, 11, 13, 14, 15} = h {0, 1, 3, 4, 5, 7, 9, 10} := by
    have h1 := hinv clebschAut95 clebschAut95_isAut {0, 1, 3, 4, 5, 7, 9, 10}
    rwa [show ({0, 1, 3, 4, 5, 7, 9, 10} : Finset (Fin 16)).map clebschAut95.toEmbedding = {4, 7, 9, 10, 11, 13, 14, 15} by decide] at h1
  have s144 : h {0, 3, 4, 7, 9, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 6, 7, 10, 11, 12, 13} := by
    have h1 := hinv clebschAut12 clebschAut12_isAut {0, 1, 2, 3, 6, 7, 10, 11, 12, 13}
    rwa [show ({0, 1, 2, 3, 6, 7, 10, 11, 12, 13} : Finset (Fin 16)).map clebschAut12.toEmbedding = {0, 3, 4, 7, 9, 10, 11, 13, 14, 15} by decide] at h1
  have s145 : h {3, 6, 10, 12, 13, 14, 15} = h {0, 1, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut96 clebschAut96_isAut {0, 1, 3, 5, 6, 8, 9}
    rwa [show ({0, 1, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut96.toEmbedding = {3, 6, 10, 12, 13, 14, 15} by decide] at h1
  have s146 : h {0, 6, 10, 12, 13, 14, 15} = h {0, 1, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut97 clebschAut97_isAut {0, 1, 3, 5, 6, 8, 9}
    rwa [show ({0, 1, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut97.toEmbedding = {0, 6, 10, 12, 13, 14, 15} by decide] at h1
  have s147 : h {6, 10, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 8} := by
    have h1 := hinv clebschAut98 clebschAut98_isAut {0, 1, 2, 3, 4, 8}
    rwa [show ({0, 1, 2, 3, 4, 8} : Finset (Fin 16)).map clebschAut98.toEmbedding = {6, 10, 12, 13, 14, 15} by decide] at h1
  have c24 : h {0, 2, 3, 6, 10, 12, 13, 14, 15} = h {0, 3, 6, 10, 12, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s148 : h {0, 2, 3, 6, 10, 12, 13, 14, 15} = h {0, 1, 2, 3, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut65 clebschAut65_isAut {0, 1, 2, 3, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut65.toEmbedding = {0, 2, 3, 6, 10, 12, 13, 14, 15} by decide] at h1
  have c25 : h {2, 3, 5, 7, 9, 11, 12, 13, 14, 15} = h {2, 3, 5, 7, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s149 : h {2, 3, 5, 7, 9, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut51 clebschAut51_isAut {0, 1, 2, 3, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut51.toEmbedding = {2, 3, 5, 7, 9, 11, 12, 13, 14, 15} by decide] at h1
  have c26 : h {0, 2, 5, 7, 9, 11, 12, 13, 14, 15} = h {0, 2, 5, 7, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s150 : h {0, 2, 5, 7, 9, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 6, 7, 10, 11, 12, 13} := by
    have h1 := hinv clebschAut10 clebschAut10_isAut {0, 1, 2, 3, 6, 7, 10, 11, 12, 13}
    rwa [show ({0, 1, 2, 3, 6, 7, 10, 11, 12, 13} : Finset (Fin 16)).map clebschAut10.toEmbedding = {0, 2, 5, 7, 9, 11, 12, 13, 14, 15} by decide] at h1
  have c27 : h {2, 5, 7, 9, 11, 12, 13, 14, 15} = h {2, 5, 7, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s151 : h {2, 5, 7, 9, 11, 12, 13, 14, 15} = h {0, 1, 2, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut51 clebschAut51_isAut {0, 1, 2, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut51.toEmbedding = {2, 5, 7, 9, 11, 12, 13, 14, 15} by decide] at h1
  have c28 : h {0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 15} = h {0, 2, 3, 5, 7, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s152 : h {0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13} := by
    have h1 := hinv clebschAut10 clebschAut10_isAut {0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13} : Finset (Fin 16)).map clebschAut10.toEmbedding = {0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 15} by decide] at h1
  have s153 : h {3, 4, 7, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut99 clebschAut99_isAut {0, 1, 2, 3, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut99.toEmbedding = {3, 4, 7, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c29 : h {0, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 4, 7, 9, 10, 11, 12, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s154 : h {0, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} := by
    have h1 := hinv clebschAut100 clebschAut100_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} : Finset (Fin 16)).map clebschAut100.toEmbedding = {0, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have s155 : h {4, 7, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 7, 9, 10} := by
    have h1 := hinv clebschAut101 clebschAut101_isAut {0, 1, 2, 3, 4, 5, 7, 9, 10}
    rwa [show ({0, 1, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 16)).map clebschAut101.toEmbedding = {4, 7, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c30 : h {0, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s156 : h {0, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13} := by
    have h1 := hinv clebschAut12 clebschAut12_isAut {0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13} : Finset (Fin 16)).map clebschAut12.toEmbedding = {0, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c31 : h {1, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15} = h {1, 3, 4, 6, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s157 : h {1, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13} := by
    have h1 := hinv clebschAut3 clebschAut3_isAut {0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13} : Finset (Fin 16)).map clebschAut3.toEmbedding = {1, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c32 : h {0, 1, 4, 6, 8, 9, 10, 11, 13, 14, 15} = h {0, 1, 4, 6, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s158 : h {0, 1, 4, 6, 8, 9, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut102 clebschAut102_isAut {0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut102.toEmbedding = {0, 1, 4, 6, 8, 9, 10, 11, 13, 14, 15} by decide] at h1
  have c33 : h {1, 4, 6, 8, 9, 10, 11, 13, 14, 15} = h {1, 4, 6, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s159 : h {1, 4, 6, 8, 9, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut103 clebschAut103_isAut {0, 1, 2, 3, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut103.toEmbedding = {1, 4, 6, 8, 9, 10, 11, 13, 14, 15} by decide] at h1
  have c34 : h {0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 3, 4, 6, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s160 : h {0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
    have h1 := hinv clebschAut3 clebschAut3_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset (Fin 16)).map clebschAut3.toEmbedding = {0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c35 : h {2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15} = h {2, 3, 5, 8, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s161 : h {2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} := by
    have h1 := hinv clebschAut79 clebschAut79_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} : Finset (Fin 16)).map clebschAut79.toEmbedding = {2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c36 : h {0, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 2, 5, 8, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s162 : h {0, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} := by
    have h1 := hinv clebschAut104 clebschAut104_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} : Finset (Fin 16)).map clebschAut104.toEmbedding = {0, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c37 : h {2, 5, 8, 9, 10, 11, 12, 13, 14, 15} = h {2, 5, 8, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s163 : h {2, 5, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 11, 12} := by
    have h1 := hinv clebschAut79 clebschAut79_isAut {0, 1, 2, 3, 4, 5, 6, 7, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 11, 12} : Finset (Fin 16)).map clebschAut79.toEmbedding = {2, 5, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c38 : h {0, 1, 2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 2, 3, 5, 8, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s164 : h {0, 1, 2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by
    have h1 := hinv clebschAut105 clebschAut105_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} : Finset (Fin 16)).map clebschAut105.toEmbedding = {0, 1, 2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c39 : h {2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {2, 3, 5, 7, 8, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s165 : h {2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12} := by
    have h1 := hinv clebschAut79 clebschAut79_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12} : Finset (Fin 16)).map clebschAut79.toEmbedding = {2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c40 : h {0, 2, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 2, 5, 7, 8, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s166 : h {0, 2, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13} := by
    have h1 := hinv clebschAut17 clebschAut17_isAut {0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13} : Finset (Fin 16)).map clebschAut17.toEmbedding = {0, 2, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c41 : h {2, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {2, 5, 7, 8, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s167 : h {2, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} := by
    have h1 := hinv clebschAut106 clebschAut106_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12} : Finset (Fin 16)).map clebschAut106.toEmbedding = {2, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c42 : h {0, 1, 2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 2, 3, 5, 7, 8, 9, 11, 12, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s168 : h {0, 1, 2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
    have h1 := hinv clebschAut17 clebschAut17_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset (Fin 16)).map clebschAut17.toEmbedding = {0, 1, 2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c43 : h {1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {1, 3, 4, 6, 7, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s169 : h {1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
    have h1 := hinv clebschAut6 clebschAut6_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset (Fin 16)).map clebschAut6.toEmbedding = {1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} by decide] at h1
  have c44 : h {0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15} = h {0, 1, 4, 6, 7, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s170 : h {0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by
    have h1 := hinv clebschAut48 clebschAut48_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} : Finset (Fin 16)).map clebschAut48.toEmbedding = {0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15} by decide] at h1
  have c45 : h {1, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15} = h {1, 4, 6, 7, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s171 : h {1, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12} := by
    have h1 := hinv clebschAut107 clebschAut107_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12} : Finset (Fin 16)).map clebschAut107.toEmbedding = {1, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15} by decide] at h1
  have c46 : h univ = h {0, 1, 3, 4, 6, 7, 8, 10, 11, 13, 14, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s172 : h {1, 13} = h {1, 2} := by
    have h1 := hinv clebschAut108 clebschAut108_isAut {1, 2}
    rwa [show ({1, 2} : Finset (Fin 16)).map clebschAut108.toEmbedding = {1, 13} by decide] at h1
  have s173 : h {0, 13} = h {1, 2} := by
    have h1 := hinv clebschAut10 clebschAut10_isAut {1, 2}
    rwa [show ({1, 2} : Finset (Fin 16)).map clebschAut10.toEmbedding = {0, 13} by decide] at h1
  have s174 : h {0, 1, 13} = h {0, 3, 4} := by
    have h1 := hinv clebschAut11 clebschAut11_isAut {0, 3, 4}
    rwa [show ({0, 3, 4} : Finset (Fin 16)).map clebschAut11.toEmbedding = {0, 1, 13} by decide] at h1
  have s175 : h {1, 12, 15} = h {1, 2, 4} := by
    have h1 := hinv clebschAut35 clebschAut35_isAut {1, 2, 4}
    rwa [show ({1, 2, 4} : Finset (Fin 16)).map clebschAut35.toEmbedding = {1, 12, 15} by decide] at h1
  have s176 : h {0, 12, 15} = h {0, 3, 4} := by
    have h1 := hinv clebschAut13 clebschAut13_isAut {0, 3, 4}
    rwa [show ({0, 3, 4} : Finset (Fin 16)).map clebschAut13.toEmbedding = {0, 12, 15} by decide] at h1
  have s177 : h {12, 15} = h {1, 2} := by
    have h1 := hinv clebschAut65 clebschAut65_isAut {1, 2}
    rwa [show ({1, 2} : Finset (Fin 16)).map clebschAut65.toEmbedding = {12, 15} by decide] at h1
  have s178 : h {0, 1, 12, 15} = h {1, 2, 3, 4} := by
    have h1 := hinv clebschAut35 clebschAut35_isAut {1, 2, 3, 4}
    rwa [show ({1, 2, 3, 4} : Finset (Fin 16)).map clebschAut35.toEmbedding = {0, 1, 12, 15} by decide] at h1
  have s179 : h {1, 9, 10, 12, 15} = h {0, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut109 clebschAut109_isAut {0, 3, 5, 6, 8}
    rwa [show ({0, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut109.toEmbedding = {1, 9, 10, 12, 15} by decide] at h1
  have s180 : h {0, 9, 10, 12, 15} = h {0, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut80 clebschAut80_isAut {0, 3, 5, 6, 8}
    rwa [show ({0, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut80.toEmbedding = {0, 9, 10, 12, 15} by decide] at h1
  have s181 : h {9, 10, 12, 15} = h {0, 3, 5, 6} := by
    have h1 := hinv clebschAut49 clebschAut49_isAut {0, 3, 5, 6}
    rwa [show ({0, 3, 5, 6} : Finset (Fin 16)).map clebschAut49.toEmbedding = {9, 10, 12, 15} by decide] at h1
  have s182 : h {0, 1, 9, 10, 12, 15} = h {0, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut109 clebschAut109_isAut {0, 3, 5, 6, 8, 9}
    rwa [show ({0, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut109.toEmbedding = {0, 1, 9, 10, 12, 15} by decide] at h1
  have s183 : h {1, 7, 11, 13, 15} = h {0, 1, 3, 5, 6} := by
    have h1 := hinv clebschAut110 clebschAut110_isAut {0, 1, 3, 5, 6}
    rwa [show ({0, 1, 3, 5, 6} : Finset (Fin 16)).map clebschAut110.toEmbedding = {1, 7, 11, 13, 15} by decide] at h1
  have s184 : h {0, 7, 11, 13, 15} = h {0, 1, 2, 4, 8} := by
    have h1 := hinv clebschAut111 clebschAut111_isAut {0, 1, 2, 4, 8}
    rwa [show ({0, 1, 2, 4, 8} : Finset (Fin 16)).map clebschAut111.toEmbedding = {0, 7, 11, 13, 15} by decide] at h1
  have s185 : h {7, 11, 13, 15} = h {0, 1, 2, 4} := by
    have h1 := hinv clebschAut59 clebschAut59_isAut {0, 1, 2, 4}
    rwa [show ({0, 1, 2, 4} : Finset (Fin 16)).map clebschAut59.toEmbedding = {7, 11, 13, 15} by decide] at h1
  have s186 : h {0, 1, 7, 11, 13, 15} = h {0, 1, 2, 4, 7, 8} := by
    have h1 := hinv clebschAut112 clebschAut112_isAut {0, 1, 2, 4, 7, 8}
    rwa [show ({0, 1, 2, 4, 7, 8} : Finset (Fin 16)).map clebschAut112.toEmbedding = {0, 1, 7, 11, 13, 15} by decide] at h1
  have s187 : h {1, 12, 13, 15} = h {1, 2, 3, 4} := by
    have h1 := hinv clebschAut113 clebschAut113_isAut {1, 2, 3, 4}
    rwa [show ({1, 2, 3, 4} : Finset (Fin 16)).map clebschAut113.toEmbedding = {1, 12, 13, 15} by decide] at h1
  have s188 : h {0, 12, 13, 15} = h {0, 1, 3, 4} := by
    have h1 := hinv clebschAut114 clebschAut114_isAut {0, 1, 3, 4}
    rwa [show ({0, 1, 3, 4} : Finset (Fin 16)).map clebschAut114.toEmbedding = {0, 12, 13, 15} by decide] at h1
  have s189 : h {12, 13, 15} = h {0, 1, 2} := by
    have h1 := hinv clebschAut65 clebschAut65_isAut {0, 1, 2}
    rwa [show ({0, 1, 2} : Finset (Fin 16)).map clebschAut65.toEmbedding = {12, 13, 15} by decide] at h1
  have s190 : h {0, 1, 12, 13, 15} = h {0, 2, 3, 4, 5} := by
    have h1 := hinv clebschAut115 clebschAut115_isAut {0, 2, 3, 4, 5}
    rwa [show ({0, 2, 3, 4, 5} : Finset (Fin 16)).map clebschAut115.toEmbedding = {0, 1, 12, 13, 15} by decide] at h1
  have c47 : h {1, 2, 5, 9, 12, 13, 15} = h {1, 2, 5, 9, 12, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s191 : h {1, 2, 5, 9, 12, 13, 15} = h {0, 1, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut116 clebschAut116_isAut {0, 1, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut116.toEmbedding = {1, 2, 5, 9, 12, 13, 15} by decide] at h1
  have c48 : h {0, 2, 5, 9, 12, 13, 15} = h {0, 2, 5, 9, 12, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s192 : h {0, 2, 5, 9, 12, 13, 15} = h {0, 1, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut75 clebschAut75_isAut {0, 1, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut75.toEmbedding = {0, 2, 5, 9, 12, 13, 15} by decide] at h1
  have c49 : h {2, 5, 9, 12, 13, 15} = h {2, 5, 9, 12, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s193 : h {2, 5, 9, 12, 13, 15} = h {0, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut51 clebschAut51_isAut {0, 7, 8, 9, 10, 12}
    rwa [show ({0, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut51.toEmbedding = {2, 5, 9, 12, 13, 15} by decide] at h1
  have c50 : h {0, 1, 2, 5, 9, 12, 13, 15} = h {0, 1, 2, 5, 9, 12, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s194 : h {0, 1, 2, 5, 9, 12, 13, 15} = h {0, 1, 3, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut105 clebschAut105_isAut {0, 1, 3, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 3, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut105.toEmbedding = {0, 1, 2, 5, 9, 12, 13, 15} by decide] at h1
  have s195 : h {1, 7, 11, 12, 13, 15} = h {0, 1, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut117 clebschAut117_isAut {0, 1, 3, 5, 6, 8}
    rwa [show ({0, 1, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut117.toEmbedding = {1, 7, 11, 12, 13, 15} by decide] at h1
  have s196 : h {0, 7, 11, 12, 13, 15} = h {0, 1, 2, 4, 7, 8} := by
    have h1 := hinv clebschAut111 clebschAut111_isAut {0, 1, 2, 4, 7, 8}
    rwa [show ({0, 1, 2, 4, 7, 8} : Finset (Fin 16)).map clebschAut111.toEmbedding = {0, 7, 11, 12, 13, 15} by decide] at h1
  have s197 : h {7, 11, 12, 13, 15} = h {0, 1, 3, 4, 8} := by
    have h1 := hinv clebschAut99 clebschAut99_isAut {0, 1, 3, 4, 8}
    rwa [show ({0, 1, 3, 4, 8} : Finset (Fin 16)).map clebschAut99.toEmbedding = {7, 11, 12, 13, 15} by decide] at h1
  have s198 : h {0, 1, 7, 11, 12, 13, 15} = h {0, 1, 3, 5, 6, 9, 10} := by
    have h1 := hinv clebschAut118 clebschAut118_isAut {0, 1, 3, 5, 6, 9, 10}
    rwa [show ({0, 1, 3, 5, 6, 9, 10} : Finset (Fin 16)).map clebschAut118.toEmbedding = {0, 1, 7, 11, 12, 13, 15} by decide] at h1
  have s199 : h {1, 8, 11, 12, 13, 15} = h {1, 2, 3, 4, 5, 8} := by
    have h1 := hinv clebschAut119 clebschAut119_isAut {1, 2, 3, 4, 5, 8}
    rwa [show ({1, 2, 3, 4, 5, 8} : Finset (Fin 16)).map clebschAut119.toEmbedding = {1, 8, 11, 12, 13, 15} by decide] at h1
  have s200 : h {0, 8, 11, 12, 13, 15} = h {0, 1, 3, 4, 7, 8} := by
    have h1 := hinv clebschAut111 clebschAut111_isAut {0, 1, 3, 4, 7, 8}
    rwa [show ({0, 1, 3, 4, 7, 8} : Finset (Fin 16)).map clebschAut111.toEmbedding = {0, 8, 11, 12, 13, 15} by decide] at h1
  have s201 : h {8, 11, 12, 13, 15} = h {0, 2, 3, 4, 5} := by
    have h1 := hinv clebschAut120 clebschAut120_isAut {0, 2, 3, 4, 5}
    rwa [show ({0, 2, 3, 4, 5} : Finset (Fin 16)).map clebschAut120.toEmbedding = {8, 11, 12, 13, 15} by decide] at h1
  have s202 : h {0, 1, 8, 11, 12, 13, 15} = h {1, 2, 3, 4, 6, 8, 9} := by
    have h1 := hinv clebschAut121 clebschAut121_isAut {1, 2, 3, 4, 6, 8, 9}
    rwa [show ({1, 2, 3, 4, 6, 8, 9} : Finset (Fin 16)).map clebschAut121.toEmbedding = {0, 1, 8, 11, 12, 13, 15} by decide] at h1
  have s203 : h {1, 7, 9, 10, 11, 12, 13, 15} = h {0, 1, 2, 3, 4, 7, 9, 10} := by
    have h1 := hinv clebschAut59 clebschAut59_isAut {0, 1, 2, 3, 4, 7, 9, 10}
    rwa [show ({0, 1, 2, 3, 4, 7, 9, 10} : Finset (Fin 16)).map clebschAut59.toEmbedding = {1, 7, 9, 10, 11, 12, 13, 15} by decide] at h1
  have c51 : h {0, 7, 8, 9, 10, 11, 12, 13, 15} = h {0, 7, 9, 10, 11, 12, 13, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s204 : h {0, 7, 8, 9, 10, 11, 12, 13, 15} = h {0, 1, 2, 3, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut122 clebschAut122_isAut {0, 1, 2, 3, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut122.toEmbedding = {0, 7, 8, 9, 10, 11, 12, 13, 15} by decide] at h1
  have s205 : h {7, 9, 10, 11, 12, 13, 15} = h {0, 1, 2, 3, 5, 6, 8} := by
    have h1 := hinv clebschAut123 clebschAut123_isAut {0, 1, 2, 3, 5, 6, 8}
    rwa [show ({0, 1, 2, 3, 5, 6, 8} : Finset (Fin 16)).map clebschAut123.toEmbedding = {7, 9, 10, 11, 12, 13, 15} by decide] at h1
  have c52 : h {0, 1, 7, 8, 9, 10, 11, 12, 13, 15} = h {0, 1, 7, 9, 10, 11, 12, 13, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s206 : h {0, 1, 7, 8, 9, 10, 11, 12, 13, 15} = h {0, 1, 2, 3, 4, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut122 clebschAut122_isAut {0, 1, 2, 3, 4, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 4, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut122.toEmbedding = {0, 1, 7, 8, 9, 10, 11, 12, 13, 15} by decide] at h1
  have s207 : h {1, 5, 7, 9, 10, 11, 12, 13, 15} = h {0, 1, 2, 3, 4, 5, 7, 9, 10} := by
    have h1 := hinv clebschAut124 clebschAut124_isAut {0, 1, 2, 3, 4, 5, 7, 9, 10}
    rwa [show ({0, 1, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 16)).map clebschAut124.toEmbedding = {1, 5, 7, 9, 10, 11, 12, 13, 15} by decide] at h1
  have c53 : h {0, 5, 7, 8, 9, 10, 11, 12, 13, 15} = h {0, 5, 7, 9, 10, 11, 12, 13, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s208 : h {0, 5, 7, 8, 9, 10, 11, 12, 13, 15} = h {0, 1, 2, 3, 5, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut124 clebschAut124_isAut {0, 1, 2, 3, 5, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 5, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut124.toEmbedding = {0, 5, 7, 8, 9, 10, 11, 12, 13, 15} by decide] at h1
  have s209 : h {5, 7, 9, 10, 11, 12, 13, 15} = h {0, 1, 2, 3, 5, 6, 8, 9} := by
    have h1 := hinv clebschAut125 clebschAut125_isAut {0, 1, 2, 3, 5, 6, 8, 9}
    rwa [show ({0, 1, 2, 3, 5, 6, 8, 9} : Finset (Fin 16)).map clebschAut125.toEmbedding = {5, 7, 9, 10, 11, 12, 13, 15} by decide] at h1
  have c54 : h {0, 1, 5, 7, 8, 9, 10, 11, 12, 13, 15} = h {0, 1, 5, 7, 9, 10, 11, 12, 13, 15} := hh.eq_of_closure hv (by decide) (by decide)
  have s210 : h {0, 1, 5, 7, 8, 9, 10, 11, 12, 13, 15} = h {0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12} := by
    have h1 := hinv clebschAut124 clebschAut124_isAut {0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12}
    rwa [show ({0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12} : Finset (Fin 16)).map clebschAut124.toEmbedding = {0, 1, 5, 7, 8, 9, 10, 11, 12, 13, 15} by decide] at h1
  have s211 : h {15} = h {0} := by
    have h1 := hinv clebschAut40 clebschAut40_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut40.toEmbedding = {15} by decide] at h1
  have s212 : h {14} = h {0} := by
    have h1 := hinv clebschAut33 clebschAut33_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut33.toEmbedding = {14} by decide] at h1
  have s213 : h {13} = h {0} := by
    have h1 := hinv clebschAut23 clebschAut23_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut23.toEmbedding = {13} by decide] at h1
  have s214 : h {12} = h {0} := by
    have h1 := hinv clebschAut61 clebschAut61_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut61.toEmbedding = {12} by decide] at h1
  have s215 : h {11} = h {0} := by
    have h1 := hinv clebschAut15 clebschAut15_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut15.toEmbedding = {11} by decide] at h1
  have s216 : h {10} = h {0} := by
    have h1 := hinv clebschAut36 clebschAut36_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut36.toEmbedding = {10} by decide] at h1
  have s217 : h {9} = h {0} := by
    have h1 := hinv clebschAut95 clebschAut95_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut95.toEmbedding = {9} by decide] at h1
  have s218 : h {8} = h {0} := by
    have h1 := hinv clebschAut16 clebschAut16_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut16.toEmbedding = {8} by decide] at h1
  have s219 : h {7} = h {0} := by
    have h1 := hinv clebschAut60 clebschAut60_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut60.toEmbedding = {7} by decide] at h1
  have s220 : h {6} = h {0} := by
    have h1 := hinv clebschAut73 clebschAut73_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut73.toEmbedding = {6} by decide] at h1
  have s221 : h {5} = h {0} := by
    have h1 := hinv clebschAut47 clebschAut47_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut47.toEmbedding = {5} by decide] at h1
  have s222 : h {4} = h {0} := by
    have h1 := hinv clebschAut14 clebschAut14_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut14.toEmbedding = {4} by decide] at h1
  have s223 : h {3} = h {0} := by
    have h1 := hinv clebschAut12 clebschAut12_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut12.toEmbedding = {3} by decide] at h1
  have s224 : h {2} = h {0} := by
    have h1 := hinv clebschAut10 clebschAut10_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut10.toEmbedding = {2} by decide] at h1
  have s225 : h {1} = h {0} := by
    have h1 := hinv clebschAut0 clebschAut0_isAut {0}
    rwa [show ({0} : Finset (Fin 16)).map clebschAut0.toEmbedding = {1} by decide] at h1
  have h0 := hh.empty
  simp only [sum_fin_16]
  linear_combination (1 / 5 : ℝ) * e1 + (1 / 5 : ℝ) * e2 + (6 / 5 : ℝ) * e3 + (1 / 5 : ℝ) * e4 +
    (1 / 5 : ℝ) * e5 + (2 / 5 : ℝ) * e6 + (1 / 5 : ℝ) * e7 + (1 / 5 : ℝ) * e8 + (16 / 5 : ℝ) * e9 +
    (4 : ℝ) * e10 + (1 : ℝ) * e11 + (3 / 5 : ℝ) * e12 + (2 / 5 : ℝ) * e13 + (2 / 5 : ℝ) * e14 +
    (2 / 5 : ℝ) * e15 + (3 / 5 : ℝ) * e16 + (2 / 5 : ℝ) * e17 + (3 / 5 : ℝ) * e18 +
    (2 / 5 : ℝ) * e19 + (1 / 5 : ℝ) * e20 + (1 / 5 : ℝ) * e21 + (3 / 5 : ℝ) * e22 +
    (1 / 5 : ℝ) * e23 + (2 / 5 : ℝ) * e24 + (1 / 5 : ℝ) * e25 + (1 : ℝ) * e26 + (1 : ℝ) * e27 +
    (1 / 5 : ℝ) * e28 + (1 / 5 : ℝ) * e29 + (2 / 5 : ℝ) * e30 + (1 : ℝ) * e31 + (1 / 5 : ℝ) * e32 +
    (1 / 5 : ℝ) * e33 + (1 / 5 : ℝ) * e34 + (1 / 5 : ℝ) * e35 + (1 / 5 : ℝ) * e36 +
    (1 / 5 : ℝ) * e37 + (4 / 5 : ℝ) * e38 + (1 / 5 : ℝ) * e39 + (11 / 5 : ℝ) * e40 + (1 : ℝ) * e41 +
    (4 / 5 : ℝ) * e42 + (12 / 5 : ℝ) * e43 + (2 / 5 : ℝ) * e44 + (7 / 5 : ℝ) * e45 +
    (4 / 5 : ℝ) * e46 + (4 / 5 : ℝ) * e47 + (2 / 5 : ℝ) * e48 + (1 / 5 : ℝ) * e49 + (3 : ℝ) * e50 +
    (1 / 5 : ℝ) * e51 + (4 / 5 : ℝ) * e52 + (4 : ℝ) * e53 + (9 : ℝ) * e54 + (1 / 5 : ℝ) * c1 +
    (1 / 5 : ℝ) * c2 + (4 / 5 : ℝ) * c3 + (-1 / 5 : ℝ) * c4 + (1 / 5 : ℝ) * c5 + (-2 / 5 : ℝ) * c6 +
    (-2 / 5 : ℝ) * c7 + (2 / 5 : ℝ) * c8 + (2 / 5 : ℝ) * c9 + (-1 / 5 : ℝ) * c10 +
    (-1 / 5 : ℝ) * c11 + (1 / 5 : ℝ) * c12 + (1 / 5 : ℝ) * c13 + (1 / 5 : ℝ) * c14 +
    (-1 : ℝ) * c15 + (1 : ℝ) * c16 + (1 / 5 : ℝ) * c17 + (-1 / 5 : ℝ) * c18 + (1 / 5 : ℝ) * c19 +
    (-2 / 5 : ℝ) * c20 + (-2 / 5 : ℝ) * c21 + (2 / 5 : ℝ) * c22 + (2 / 5 : ℝ) * c23 +
    (2 / 5 : ℝ) * c24 + (-3 / 5 : ℝ) * c25 + (-3 / 5 : ℝ) * c26 + (3 / 5 : ℝ) * c27 +
    (3 / 5 : ℝ) * c28 + (-2 / 5 : ℝ) * c29 + (2 / 5 : ℝ) * c30 + (-2 / 5 : ℝ) * c31 +
    (-2 / 5 : ℝ) * c32 + (2 / 5 : ℝ) * c33 + (2 / 5 : ℝ) * c34 + (-2 / 5 : ℝ) * c35 +
    (-2 / 5 : ℝ) * c36 + (2 / 5 : ℝ) * c37 + (2 / 5 : ℝ) * c38 + (-3 / 5 : ℝ) * c39 +
    (-3 / 5 : ℝ) * c40 + (3 / 5 : ℝ) * c41 + (3 / 5 : ℝ) * c42 + (-1 : ℝ) * c43 + (-1 : ℝ) * c44 +
    (1 : ℝ) * c45 + (-1 / 5 : ℝ) * c47 + (-1 / 5 : ℝ) * c48 + (1 / 5 : ℝ) * c49 +
    (1 / 5 : ℝ) * c50 + (-1 / 5 : ℝ) * c51 + (1 / 5 : ℝ) * c52 + (-1 / 5 : ℝ) * c53 +
    (1 / 5 : ℝ) * c54 + (-9 : ℝ) * s1 + (4 : ℝ) * s2 + (4 : ℝ) * s3 + (-4 : ℝ) * s4 +
    (4 / 5 : ℝ) * s5 + (4 / 5 : ℝ) * s6 + (-4 / 5 : ℝ) * s7 + (-4 / 5 : ℝ) * s8 + (1 / 5 : ℝ) * s9 +
    (1 / 5 : ℝ) * s10 + (-1 / 5 : ℝ) * s11 + (-1 / 5 : ℝ) * s12 + (3 : ℝ) * s13 + (3 : ℝ) * s14 +
    (-3 : ℝ) * s15 + (-3 : ℝ) * s16 + (1 / 5 : ℝ) * s17 + (1 / 5 : ℝ) * s18 + (-1 / 5 : ℝ) * s19 +
    (-1 / 5 : ℝ) * s20 + (2 / 5 : ℝ) * s21 + (2 / 5 : ℝ) * s22 + (-2 / 5 : ℝ) * s23 +
    (-2 / 5 : ℝ) * s24 + (4 / 5 : ℝ) * s25 + (4 / 5 : ℝ) * s26 + (-4 / 5 : ℝ) * s27 +
    (-4 / 5 : ℝ) * s28 + (4 / 5 : ℝ) * s29 + (4 / 5 : ℝ) * s30 + (-4 / 5 : ℝ) * s31 +
    (-4 / 5 : ℝ) * s32 + (7 / 5 : ℝ) * s33 + (7 / 5 : ℝ) * s34 + (-7 / 5 : ℝ) * s35 +
    (-7 / 5 : ℝ) * s36 + (2 / 5 : ℝ) * s37 + (2 / 5 : ℝ) * s38 + (-2 / 5 : ℝ) * s39 +
    (-2 / 5 : ℝ) * s40 + (12 / 5 : ℝ) * s41 + (12 / 5 : ℝ) * s42 + (-12 / 5 : ℝ) * s43 +
    (-12 / 5 : ℝ) * s44 + (4 / 5 : ℝ) * s45 + (4 / 5 : ℝ) * s46 + (-4 / 5 : ℝ) * s47 +
    (-4 / 5 : ℝ) * s48 + (1 : ℝ) * s49 + (1 : ℝ) * s50 + (-1 : ℝ) * s51 + (-1 : ℝ) * s52 +
    (11 / 5 : ℝ) * s53 + (11 / 5 : ℝ) * s54 + (-11 / 5 : ℝ) * s55 + (-11 / 5 : ℝ) * s56 +
    (1 / 5 : ℝ) * s57 + (1 / 5 : ℝ) * s58 + (-1 / 5 : ℝ) * s59 + (-1 / 5 : ℝ) * s60 +
    (4 / 5 : ℝ) * s61 + (4 / 5 : ℝ) * s62 + (-4 / 5 : ℝ) * s63 + (-4 / 5 : ℝ) * s64 +
    (1 / 5 : ℝ) * s65 + (1 / 5 : ℝ) * s66 + (-1 / 5 : ℝ) * s67 + (-1 / 5 : ℝ) * s68 +
    (1 / 5 : ℝ) * s69 + (1 / 5 : ℝ) * s70 + (-1 / 5 : ℝ) * s71 + (-1 / 5 : ℝ) * s72 +
    (1 / 5 : ℝ) * s73 + (1 / 5 : ℝ) * s74 + (-1 / 5 : ℝ) * s75 + (-1 / 5 : ℝ) * s76 +
    (1 / 5 : ℝ) * s77 + (1 / 5 : ℝ) * s78 + (-1 / 5 : ℝ) * s79 + (-1 / 5 : ℝ) * s80 +
    (1 / 5 : ℝ) * s81 + (1 / 5 : ℝ) * s82 + (-1 / 5 : ℝ) * s83 + (-1 / 5 : ℝ) * s84 +
    (1 / 5 : ℝ) * s85 + (1 / 5 : ℝ) * s86 + (-1 / 5 : ℝ) * s87 + (-1 / 5 : ℝ) * s88 +
    (1 : ℝ) * s89 + (1 : ℝ) * s90 + (-1 : ℝ) * s91 + (-1 : ℝ) * s92 + (2 / 5 : ℝ) * s93 +
    (2 / 5 : ℝ) * s94 + (-2 / 5 : ℝ) * s95 + (-2 / 5 : ℝ) * s96 + (1 / 5 : ℝ) * s97 +
    (1 / 5 : ℝ) * s98 + (-1 / 5 : ℝ) * s99 + (-1 / 5 : ℝ) * s100 + (1 / 5 : ℝ) * s101 +
    (1 / 5 : ℝ) * s102 + (-1 / 5 : ℝ) * s103 + (-1 / 5 : ℝ) * s104 + (1 : ℝ) * s105 +
    (1 : ℝ) * s106 + (-1 : ℝ) * s107 + (-1 : ℝ) * s108 + (1 : ℝ) * s109 + (1 : ℝ) * s110 +
    (-1 : ℝ) * s111 + (-1 : ℝ) * s112 + (1 / 5 : ℝ) * s113 + (1 / 5 : ℝ) * s114 +
    (-1 / 5 : ℝ) * s115 + (-1 / 5 : ℝ) * s116 + (2 / 5 : ℝ) * s117 + (2 / 5 : ℝ) * s118 +
    (-2 / 5 : ℝ) * s119 + (-2 / 5 : ℝ) * s120 + (1 / 5 : ℝ) * s121 + (1 / 5 : ℝ) * s122 +
    (-1 / 5 : ℝ) * s123 + (-1 / 5 : ℝ) * s124 + (3 / 5 : ℝ) * s125 + (3 / 5 : ℝ) * s126 +
    (-3 / 5 : ℝ) * s127 + (-3 / 5 : ℝ) * s128 + (1 / 5 : ℝ) * s129 + (1 / 5 : ℝ) * s130 +
    (-1 / 5 : ℝ) * s131 + (-1 / 5 : ℝ) * s132 + (1 / 5 : ℝ) * s133 + (1 / 5 : ℝ) * s134 +
    (-1 / 5 : ℝ) * s135 + (-1 / 5 : ℝ) * s136 + (2 / 5 : ℝ) * s137 + (2 / 5 : ℝ) * s138 +
    (-2 / 5 : ℝ) * s139 + (-2 / 5 : ℝ) * s140 + (3 / 5 : ℝ) * s141 + (3 / 5 : ℝ) * s142 +
    (-3 / 5 : ℝ) * s143 + (-3 / 5 : ℝ) * s144 + (2 / 5 : ℝ) * s145 + (2 / 5 : ℝ) * s146 +
    (-2 / 5 : ℝ) * s147 + (-2 / 5 : ℝ) * s148 + (3 / 5 : ℝ) * s149 + (3 / 5 : ℝ) * s150 +
    (-3 / 5 : ℝ) * s151 + (-3 / 5 : ℝ) * s152 + (2 / 5 : ℝ) * s153 + (2 / 5 : ℝ) * s154 +
    (-2 / 5 : ℝ) * s155 + (-2 / 5 : ℝ) * s156 + (2 / 5 : ℝ) * s157 + (2 / 5 : ℝ) * s158 +
    (-2 / 5 : ℝ) * s159 + (-2 / 5 : ℝ) * s160 + (2 / 5 : ℝ) * s161 + (2 / 5 : ℝ) * s162 +
    (-2 / 5 : ℝ) * s163 + (-2 / 5 : ℝ) * s164 + (3 / 5 : ℝ) * s165 + (3 / 5 : ℝ) * s166 +
    (-3 / 5 : ℝ) * s167 + (-3 / 5 : ℝ) * s168 + (1 : ℝ) * s169 + (1 : ℝ) * s170 + (-1 : ℝ) * s171 +
    (1 : ℝ) * c46 + (4 : ℝ) * s172 + (4 : ℝ) * s173 + (-4 : ℝ) * s174 + (16 / 5 : ℝ) * s175 +
    (16 / 5 : ℝ) * s176 + (-16 / 5 : ℝ) * s177 + (-16 / 5 : ℝ) * s178 + (1 / 5 : ℝ) * s179 +
    (1 / 5 : ℝ) * s180 + (-1 / 5 : ℝ) * s181 + (-1 / 5 : ℝ) * s182 + (1 / 5 : ℝ) * s183 +
    (1 / 5 : ℝ) * s184 + (-1 / 5 : ℝ) * s185 + (-1 / 5 : ℝ) * s186 + (2 / 5 : ℝ) * s187 +
    (2 / 5 : ℝ) * s188 + (-2 / 5 : ℝ) * s189 + (-2 / 5 : ℝ) * s190 + (1 / 5 : ℝ) * s191 +
    (1 / 5 : ℝ) * s192 + (-1 / 5 : ℝ) * s193 + (-1 / 5 : ℝ) * s194 + (1 / 5 : ℝ) * s195 +
    (1 / 5 : ℝ) * s196 + (-1 / 5 : ℝ) * s197 + (-1 / 5 : ℝ) * s198 + (6 / 5 : ℝ) * s199 +
    (6 / 5 : ℝ) * s200 + (-6 / 5 : ℝ) * s201 + (-6 / 5 : ℝ) * s202 + (1 / 5 : ℝ) * s203 +
    (1 / 5 : ℝ) * s204 + (-1 / 5 : ℝ) * s205 + (-1 / 5 : ℝ) * s206 + (1 / 5 : ℝ) * s207 +
    (1 / 5 : ℝ) * s208 + (-1 / 5 : ℝ) * s209 + (-1 / 5 : ℝ) * s210 + (-5 / 8 : ℝ) * s211 +
    (-37 / 8 : ℝ) * s212 + (-37 / 8 : ℝ) * s213 + (-5 / 8 : ℝ) * s214 + (-5 / 8 : ℝ) * s215 +
    (-5 / 8 : ℝ) * s216 + (-5 / 8 : ℝ) * s217 + (-5 / 8 : ℝ) * s218 + (-5 / 8 : ℝ) * s219 +
    (-5 / 8 : ℝ) * s220 + (-5 / 8 : ℝ) * s221 + (-5 / 8 : ℝ) * s222 + (67 / 8 : ℝ) * s223 +
    (-5 / 8 : ℝ) * s224 + (-5 / 8 : ℝ) * s225 + (-9 : ℝ) * h0

theorem rateBound_clebschGraph : RateBound (nbhd clebschGraph) (5 / 8) := by
  rw [nbhd_clebschGraph]
  exact rateBound_clebsch

/-- Every storage code on the Clebsch graph has at most `|α|^10` codewords. -/
theorem clebsch_card_le {α : Type*} [Fintype α] [Nonempty α] {C : Finset (Fin 16 → α)}
    (hC : IsStorageCode (nbhd clebschGraph) C) : C.card ≤ Fintype.card α ^ 10 := by
  rcases C.eq_empty_or_nonempty with hCe | hne
  · rw [hCe, Finset.card_empty]
    positivity
  · have h1 := log_card_le_of_rateBound (by norm_num) rateBound_clebschGraph hC
    have hc : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
    have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    have h2 : Real.log (C.card : ℝ) ≤ Real.log ((Fintype.card α : ℝ) ^ 10) := by
      rw [Real.log_pow]
      simp only [Fintype.card_fin] at h1
      push_cast at h1 ⊢
      linarith
    have h3 := (Real.log_le_log_iff hc (by positivity)).mp h2
    exact_mod_cast h3

/-- **`gn(Clebsch) = 10`** (answering Cameron–Dang–Riis): no storage code on the
Clebsch graph over an alphabet of size `q` has more than `q^10` codewords, and a
binary code has exactly `2^10`. -/
theorem clebsch_guessingNumber :
    (∀ (α : Type) [Fintype α] [Nonempty α] (C : Finset (Fin 16 → α)),
      IsStorageCode (nbhd clebschGraph) C → C.card ≤ Fintype.card α ^ 10) ∧
    ∃ C : Finset (Fin 16 → ZMod 2), IsStorageCode (nbhd clebschGraph) C ∧
      C.card = Fintype.card (ZMod 2) ^ 10 :=
  ⟨fun _ _ _ _ hC => clebsch_card_le hC,
    ⟨clebschCode, clebschCode_isStorageCode, by rw [clebschCode_card, ZMod.card]⟩⟩

/-- **`λ(Clebsch) = 5/8`**: the rate bound `c` holds for every valid polymatroid
on the Clebsch graph exactly when `c ≥ 5/8`. The binary code shows that no
smaller constant works. -/
theorem clebsch_rateBound_iff (c : ℝ) : RateBound (nbhd clebschGraph) c ↔ 5 / 8 ≤ c := by
  constructor
  · intro hR
    have h := log_card_le_of_rateBound' hR clebschCode_isStorageCode
    rw [clebschCode_card, Fintype.card_fin, ZMod.card, Nat.cast_pow, Real.log_pow] at h
    norm_num at h
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    by_contra hlt
    push Not at hlt
    have hm : max c 0 < 5 / 8 := max_lt hlt (by norm_num)
    nlinarith
  · intro hc
    exact rateBound_clebschGraph.mono hc

/-! ## The binary code is all of `ker (I + A)`, and `I + A` has rank 6 over `GF(2)` -/

/-- The binary code of the Clebsch graph is the whole solution space of `x_v = Σ_{u ~ v} x_u`. -/
theorem clebschCode_eq :
    clebschCode = univ.filter (fun x : Fin 16 → ZMod 2 => ∀ v, x v = ∑ u ∈ clebschNbhd v, x u) := by
  set K := univ.filter (fun x : Fin 16 → ZMod 2 => ∀ v, x v = ∑ u ∈ clebschNbhd v, x u)
  have hsub : clebschCode ⊆ K := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun v => clebschEncode_parity b v
  have hK : IsStorageCode (nbhd clebschGraph) K := by
    rw [nbhd_clebschGraph]
    intro x hx y hy v hxy
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rw [hx v, hy v]
    exact Finset.sum_congr rfl hxy
  have hcard : K.card ≤ clebschCode.card := by
    have := clebsch_card_le hK
    rwa [ZMod.card, ← clebschCode_card] at this
  exact Finset.eq_of_subset_of_card_le hsub hcard

theorem neighborFinset_clebschGraph (v : Fin 16) : clebschGraph.neighborFinset v = clebschNbhd v := by
  rw [← nbhd_clebschGraph]
  ext u
  simp [nbhd, SimpleGraph.mem_neighborFinset]

/-- `x` lies in the kernel of `I + A` over `GF(2)` exactly when `x_v = Σ_{u ~ v} x_u` for all `v`. -/
theorem mem_ker_clebsch_iff (x : Fin 16 → ZMod 2) :
    x ∈ LinearMap.ker (1 + clebschGraph.adjMatrix (ZMod 2)).mulVecLin ↔
      ∀ v, x v = ∑ u ∈ clebschNbhd v, x u := by
  have h2 : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.one_mulVec]
  constructor
  · intro h v
    have hv := congrFun h v
    simp only [Pi.add_apply, SimpleGraph.adjMatrix_mulVec_apply, neighborFinset_clebschGraph,
      Pi.zero_apply] at hv
    exact (h2 _ _).mp hv
  · intro h
    funext v
    simp only [Pi.add_apply, SimpleGraph.adjMatrix_mulVec_apply, neighborFinset_clebschGraph,
      Pi.zero_apply]
    exact (h2 _ _).mpr (h v)

/-- **The kernel of `I + A` over `GF(2)` has dimension 10.** -/
theorem finrank_ker_clebsch :
    Module.finrank (ZMod 2) (LinearMap.ker (1 + clebschGraph.adjMatrix (ZMod 2)).mulVecLin) = 10 := by
  classical
  set Kr := LinearMap.ker (1 + clebschGraph.adjMatrix (ZMod 2)).mulVecLin
  have hset : (Kr : Set (Fin 16 → ZMod 2)) = (clebschCode : Set (Fin 16 → ZMod 2)) := by
    ext x
    rw [SetLike.mem_coe, mem_ker_clebsch_iff, clebschCode_eq]
    simp
  have hcard : Nat.card Kr = 2 ^ 10 := by
    rw [← clebschCode_card, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Set.ext_iff.mp hset x)
  have hpow := Module.card_eq_pow_finrank (K := ZMod 2) (V := Kr)
  rw [← Nat.card_eq_fintype_card, hcard, ZMod.card] at hpow
  exact (Nat.pow_right_injective (le_refl 2) hpow).symm

/-- **`I + A` has rank 6 over `GF(2)`.** -/
theorem rank_clebsch : (1 + clebschGraph.adjMatrix (ZMod 2)).rank = 6 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (1 + clebschGraph.adjMatrix (ZMod 2)).mulVecLin
  rw [finrank_ker_clebsch, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  have h3 : (1 + clebschGraph.adjMatrix (ZMod 2)).rank =
      Module.finrank (ZMod 2) (LinearMap.range (1 + clebschGraph.adjMatrix (ZMod 2)).mulVecLin) := rfl
  omega

end MotionDepthCodes
