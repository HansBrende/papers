import MotionDepthCodes.Symmetry
import SoftRecovery.Decomposition

/-!
# The paid Fano Shannon certificate

Generated from the saved 33-term certificate by tools/fano-shannon/generate_lean.py.
Every finite map below is proved to be an automorphism of the actual residual
Fano helper relation. Every certificate inequality is derived from polymatroid
submodularity, a coordinate purchase, or a paid recovery step; none is supplied
as an unexplained premise. The final integer combination is kernel-checked.

The ground set is the 28 nonincident point-line pairs. Points and line normals
are the nonzero binary triples in lexicographic order, indexed by Fin 7.
The paid theorem needs no exact recovery, singleton caps or symmetry assumption.
The residual exact-recovery bound is its corollary. Companion modules prove
the full 49-cell contraction, Shannon attainment by explicit polymatroids,
and order value 41. The actual triangle-code realization remains written.
-/

namespace LeanBacklog.FanoCertificate

open Finset MotionDepthCodes SoftRecovery
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev Cell := Fin 28

/-- Orthogonality of the nonzero binary triples encoded by p+1 and l+1. -/
def incident (p l : Fin 7) : Prop :=
  (((p.val + 1) % 2) * ((l.val + 1) % 2) +
   (((p.val + 1) / 2) % 2) * (((l.val + 1) / 2) % 2) +
   (((p.val + 1) / 4) % 2) * (((l.val + 1) / 4) % 2)) % 2 = 0

instance (p l : Fin 7) : Decidable (incident p l) := inferInstanceAs
  (Decidable (((p.val + 1) % 2 * ((l.val + 1) % 2) +
    ((p.val + 1) / 2 % 2) * ((l.val + 1) / 2 % 2) +
    ((p.val + 1) / 4 % 2) * ((l.val + 1) / 4 % 2)) % 2 = 0))

def row : Cell → Fin 7 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6]

def column : Cell → Fin 7 := ![0, 2, 4, 6, 1, 2, 5, 6, 0, 1, 4, 5, 3, 4, 5, 6, 0, 2, 3, 5, 1, 2, 3, 4, 0, 1, 3, 6]

/-- The twelve residual helper cells of each target. -/
def nbhd : Cell → Finset Cell := ![
  {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23},
  {8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27},
  {4, 5, 6, 7, 16, 17, 18, 19, 24, 25, 26, 27},
  {8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23},
  {0, 1, 2, 3, 12, 13, 14, 15, 16, 17, 18, 19},
  {8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27},
  {0, 1, 2, 3, 20, 21, 22, 23, 24, 25, 26, 27},
  {8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23},
  {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23},
  {0, 1, 2, 3, 12, 13, 14, 15, 16, 17, 18, 19},
  {4, 5, 6, 7, 16, 17, 18, 19, 24, 25, 26, 27},
  {0, 1, 2, 3, 20, 21, 22, 23, 24, 25, 26, 27},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {4, 5, 6, 7, 16, 17, 18, 19, 24, 25, 26, 27},
  {0, 1, 2, 3, 20, 21, 22, 23, 24, 25, 26, 27},
  {8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23},
  {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23},
  {8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {0, 1, 2, 3, 20, 21, 22, 23, 24, 25, 26, 27},
  {0, 1, 2, 3, 12, 13, 14, 15, 16, 17, 18, 19},
  {8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {4, 5, 6, 7, 16, 17, 18, 19, 24, 25, 26, 27},
  {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23},
  {0, 1, 2, 3, 12, 13, 14, 15, 16, 17, 18, 19},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23}]


theorem cells_nonincident : ∀ v, ¬incident (row v) (column v) := by decide
theorem cells_injective : Function.Injective (fun v : Cell => (row v, column v)) := by decide
theorem cells_complete : ∀ p l, ¬incident p l → ∃ v, row v = p ∧ column v = l := by decide
theorem nbhd_eq_incidence : ∀ v, nbhd v =
    univ.filter (fun w => incident (row w) (column v)) := by decide

private def aut0 : Equiv.Perm Cell where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut0_isAut : IsAut nbhd aut0 := by decide

private def aut1 : Equiv.Perm Cell where
  toFun := ![0, 1, 3, 2, 20, 21, 22, 23, 24, 25, 27, 26, 14, 15, 12, 13, 16, 17, 19, 18, 4, 5, 6, 7, 8, 9, 11, 10]
  invFun := ![0, 1, 3, 2, 20, 21, 22, 23, 24, 25, 27, 26, 14, 15, 12, 13, 16, 17, 19, 18, 4, 5, 6, 7, 8, 9, 11, 10]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut1_isAut : IsAut nbhd aut1 := by decide

private def aut2 : Equiv.Perm Cell where
  toFun := ![0, 2, 1, 3, 12, 13, 14, 15, 16, 18, 17, 19, 4, 5, 6, 7, 8, 10, 9, 11, 22, 23, 20, 21, 24, 26, 25, 27]
  invFun := ![0, 2, 1, 3, 12, 13, 14, 15, 16, 18, 17, 19, 4, 5, 6, 7, 8, 10, 9, 11, 22, 23, 20, 21, 24, 26, 25, 27]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut2_isAut : IsAut nbhd aut2 := by decide

private def aut3 : Equiv.Perm Cell where
  toFun := ![0, 2, 3, 1, 22, 23, 20, 21, 24, 26, 27, 25, 6, 7, 4, 5, 8, 10, 11, 9, 12, 13, 14, 15, 16, 18, 19, 17]
  invFun := ![0, 3, 1, 2, 14, 15, 12, 13, 16, 19, 17, 18, 20, 21, 22, 23, 24, 27, 25, 26, 6, 7, 4, 5, 8, 11, 9, 10]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut3_isAut : IsAut nbhd aut3 := by decide

private def aut4 : Equiv.Perm Cell where
  toFun := ![1, 0, 2, 3, 25, 24, 26, 27, 21, 20, 23, 22, 14, 13, 12, 15, 17, 16, 19, 18, 9, 8, 11, 10, 5, 4, 6, 7]
  invFun := ![1, 0, 2, 3, 25, 24, 26, 27, 21, 20, 23, 22, 14, 13, 12, 15, 17, 16, 19, 18, 9, 8, 11, 10, 5, 4, 6, 7]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut4_isAut : IsAut nbhd aut4 := by decide

private def aut5 : Equiv.Perm Cell where
  toFun := ![1, 0, 3, 2, 9, 8, 11, 10, 5, 4, 7, 6, 12, 15, 14, 13, 17, 16, 18, 19, 25, 24, 26, 27, 21, 20, 22, 23]
  invFun := ![1, 0, 3, 2, 9, 8, 11, 10, 5, 4, 7, 6, 12, 15, 14, 13, 17, 16, 18, 19, 25, 24, 26, 27, 21, 20, 22, 23]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut5_isAut : IsAut nbhd aut5 := by decide

private def aut6 : Equiv.Perm Cell where
  toFun := ![2, 0, 1, 3, 26, 24, 25, 27, 23, 22, 21, 20, 6, 5, 4, 7, 10, 8, 11, 9, 18, 16, 19, 17, 13, 12, 14, 15]
  invFun := ![1, 2, 0, 3, 14, 13, 12, 15, 17, 19, 16, 18, 25, 24, 26, 27, 21, 23, 20, 22, 11, 10, 9, 8, 5, 6, 4, 7]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut6_isAut : IsAut nbhd aut6 := by decide

private def aut7 : Equiv.Perm Cell where
  toFun := ![2, 1, 3, 0, 19, 17, 18, 16, 13, 14, 15, 12, 25, 27, 26, 24, 23, 21, 20, 22, 6, 5, 4, 7, 10, 11, 9, 8]
  invFun := ![3, 1, 0, 2, 22, 21, 20, 23, 27, 26, 24, 25, 11, 8, 9, 10, 7, 5, 6, 4, 18, 17, 19, 16, 15, 12, 14, 13]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut7_isAut : IsAut nbhd aut7 := by decide

private def aut8 : Equiv.Perm Cell where
  toFun := ![3, 0, 1, 2, 11, 8, 9, 10, 7, 6, 5, 4, 22, 21, 20, 23, 27, 24, 26, 25, 19, 16, 18, 17, 15, 14, 12, 13]
  invFun := ![1, 2, 3, 0, 11, 10, 9, 8, 5, 6, 7, 4, 26, 27, 25, 24, 21, 23, 22, 20, 14, 13, 12, 15, 17, 19, 18, 16]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut8_isAut : IsAut nbhd aut8 := by decide

private def aut9 : Equiv.Perm Cell where
  toFun := ![3, 2, 1, 0, 9, 10, 11, 8, 7, 4, 5, 6, 18, 17, 19, 16, 15, 13, 12, 14, 20, 23, 22, 21, 27, 25, 26, 24]
  invFun := ![3, 2, 1, 0, 9, 10, 11, 8, 7, 4, 5, 6, 18, 17, 19, 16, 15, 13, 12, 14, 20, 23, 22, 21, 27, 25, 26, 24]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut9_isAut : IsAut nbhd aut9 := by decide

private def aut10 : Equiv.Perm Cell where
  toFun := ![4, 5, 6, 7, 0, 1, 2, 3, 9, 8, 11, 10, 12, 14, 13, 15, 20, 21, 22, 23, 16, 17, 18, 19, 25, 24, 26, 27]
  invFun := ![4, 5, 6, 7, 0, 1, 2, 3, 9, 8, 11, 10, 12, 14, 13, 15, 20, 21, 22, 23, 16, 17, 18, 19, 25, 24, 26, 27]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut10_isAut : IsAut nbhd aut10 := by decide

private def aut11 : Equiv.Perm Cell where
  toFun := ![4, 6, 5, 7, 12, 14, 13, 15, 20, 22, 21, 23, 0, 1, 2, 3, 9, 11, 8, 10, 18, 19, 16, 17, 25, 26, 24, 27]
  invFun := ![12, 13, 14, 15, 0, 2, 1, 3, 18, 16, 19, 17, 4, 6, 5, 7, 22, 23, 20, 21, 8, 10, 9, 11, 26, 24, 25, 27]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut11_isAut : IsAut nbhd aut11 := by decide

private def aut12 : Equiv.Perm Cell where
  toFun := ![4, 7, 5, 6, 13, 15, 12, 14, 20, 23, 21, 22, 16, 17, 18, 19, 25, 27, 24, 26, 2, 3, 0, 1, 9, 10, 8, 11]
  invFun := ![22, 23, 20, 21, 0, 2, 3, 1, 26, 24, 25, 27, 6, 4, 7, 5, 12, 13, 14, 15, 8, 10, 11, 9, 18, 16, 19, 17]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut12_isAut : IsAut nbhd aut12 := by decide

private def aut13 : Equiv.Perm Cell where
  toFun := ![4, 7, 6, 5, 2, 3, 0, 1, 9, 10, 11, 8, 18, 19, 16, 17, 25, 27, 26, 24, 13, 15, 12, 14, 20, 23, 22, 21]
  invFun := ![6, 7, 4, 5, 0, 3, 2, 1, 11, 8, 9, 10, 22, 20, 23, 21, 14, 15, 12, 13, 24, 27, 26, 25, 19, 16, 18, 17]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut13_isAut : IsAut nbhd aut13 := by decide

private def aut14 : Equiv.Perm Cell where
  toFun := ![5, 4, 6, 7, 24, 25, 26, 27, 17, 16, 19, 18, 13, 14, 12, 15, 21, 20, 23, 22, 8, 9, 10, 11, 1, 0, 2, 3]
  invFun := ![25, 24, 26, 27, 1, 0, 2, 3, 20, 21, 22, 23, 14, 12, 13, 15, 9, 8, 11, 10, 17, 16, 19, 18, 4, 5, 6, 7]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut14_isAut : IsAut nbhd aut14 := by decide

private def aut15 : Equiv.Perm Cell where
  toFun := ![6, 4, 5, 7, 26, 25, 24, 27, 19, 18, 17, 16, 2, 1, 0, 3, 11, 9, 10, 8, 22, 20, 23, 21, 14, 12, 13, 15]
  invFun := ![14, 13, 12, 15, 1, 2, 0, 3, 19, 17, 18, 16, 25, 26, 24, 27, 11, 10, 9, 8, 21, 23, 20, 22, 6, 5, 4, 7]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut15_isAut : IsAut nbhd aut15 := by decide

private def aut16 : Equiv.Perm Cell where
  toFun := ![7, 4, 5, 6, 10, 9, 8, 11, 3, 2, 1, 0, 18, 17, 16, 19, 27, 25, 26, 24, 23, 20, 22, 21, 15, 13, 12, 14]
  invFun := ![11, 10, 9, 8, 1, 2, 3, 0, 6, 5, 4, 7, 26, 25, 27, 24, 14, 13, 12, 15, 21, 23, 22, 20, 19, 17, 18, 16]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut16_isAut : IsAut nbhd aut16 := by decide

private def aut17 : Equiv.Perm Cell where
  toFun := ![8, 9, 10, 11, 5, 4, 7, 6, 0, 1, 2, 3, 12, 13, 15, 14, 24, 25, 26, 27, 21, 20, 22, 23, 16, 17, 18, 19]
  invFun := ![8, 9, 10, 11, 5, 4, 7, 6, 0, 1, 2, 3, 12, 13, 15, 14, 24, 25, 26, 27, 21, 20, 22, 23, 16, 17, 18, 19]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut17_isAut : IsAut nbhd aut17 := by decide

private def aut18 : Equiv.Perm Cell where
  toFun := ![8, 10, 9, 11, 12, 13, 15, 14, 24, 26, 25, 27, 5, 4, 7, 6, 0, 2, 1, 3, 22, 23, 21, 20, 16, 18, 17, 19]
  invFun := ![16, 18, 17, 19, 13, 12, 15, 14, 0, 2, 1, 3, 4, 5, 7, 6, 24, 26, 25, 27, 23, 22, 20, 21, 8, 10, 9, 11]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut18_isAut : IsAut nbhd aut18 := by decide

private def aut19 : Equiv.Perm Cell where
  toFun := ![8, 10, 11, 9, 22, 23, 21, 20, 16, 18, 19, 17, 7, 6, 5, 4, 0, 2, 3, 1, 12, 13, 15, 14, 24, 26, 27, 25]
  invFun := ![16, 19, 17, 18, 15, 14, 13, 12, 0, 3, 1, 2, 20, 21, 23, 22, 8, 11, 9, 10, 7, 6, 4, 5, 24, 27, 25, 26]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut19_isAut : IsAut nbhd aut19 := by decide

private def aut20 : Equiv.Perm Cell where
  toFun := ![8, 11, 10, 9, 7, 6, 5, 4, 0, 3, 2, 1, 22, 23, 21, 20, 16, 19, 18, 17, 15, 14, 12, 13, 24, 27, 26, 25]
  invFun := ![8, 11, 10, 9, 7, 6, 5, 4, 0, 3, 2, 1, 22, 23, 21, 20, 16, 19, 18, 17, 15, 14, 12, 13, 24, 27, 26, 25]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut20_isAut : IsAut nbhd aut20 := by decide

private def aut21 : Equiv.Perm Cell where
  toFun := ![9, 8, 10, 11, 17, 16, 18, 19, 20, 21, 23, 22, 15, 13, 12, 14, 25, 24, 27, 26, 1, 0, 3, 2, 4, 5, 7, 6]
  invFun := ![21, 20, 23, 22, 24, 25, 27, 26, 1, 0, 2, 3, 14, 13, 15, 12, 5, 4, 6, 7, 8, 9, 11, 10, 17, 16, 19, 18]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut21_isAut : IsAut nbhd aut21 := by decide

private def aut22 : Equiv.Perm Cell where
  toFun := ![9, 8, 11, 10, 1, 0, 3, 2, 4, 5, 6, 7, 12, 14, 15, 13, 25, 24, 26, 27, 17, 16, 18, 19, 20, 21, 22, 23]
  invFun := ![5, 4, 7, 6, 8, 9, 10, 11, 1, 0, 3, 2, 12, 15, 13, 14, 21, 20, 22, 23, 24, 25, 26, 27, 17, 16, 18, 19]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut22_isAut : IsAut nbhd aut22 := by decide

private def aut23 : Equiv.Perm Cell where
  toFun := ![9, 10, 8, 11, 15, 13, 12, 14, 25, 27, 24, 26, 17, 16, 18, 19, 20, 23, 21, 22, 3, 2, 1, 0, 4, 7, 5, 6]
  invFun := ![23, 22, 21, 20, 24, 26, 27, 25, 2, 0, 1, 3, 6, 5, 7, 4, 13, 12, 14, 15, 16, 18, 19, 17, 10, 8, 11, 9]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut23_isAut : IsAut nbhd aut23 := by decide

private def aut24 : Equiv.Perm Cell where
  toFun := ![9, 10, 11, 8, 3, 2, 1, 0, 4, 7, 6, 5, 18, 19, 17, 16, 20, 23, 22, 21, 15, 13, 12, 14, 25, 27, 26, 24]
  invFun := ![7, 6, 5, 4, 8, 11, 10, 9, 3, 0, 1, 2, 22, 21, 23, 20, 15, 14, 12, 13, 16, 19, 18, 17, 27, 24, 26, 25]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut24_isAut : IsAut nbhd aut24 := by decide

private def aut25 : Equiv.Perm Cell where
  toFun := ![10, 8, 9, 11, 18, 16, 17, 19, 23, 22, 20, 21, 7, 4, 5, 6, 2, 0, 3, 1, 26, 24, 27, 25, 13, 12, 15, 14]
  invFun := ![17, 19, 16, 18, 13, 14, 15, 12, 1, 2, 0, 3, 25, 24, 27, 26, 5, 6, 4, 7, 10, 11, 9, 8, 21, 23, 20, 22]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut25_isAut : IsAut nbhd aut25 := by decide

private def aut26 : Equiv.Perm Cell where
  toFun := ![11, 8, 9, 10, 3, 0, 1, 2, 6, 7, 4, 5, 22, 20, 21, 23, 19, 16, 18, 17, 27, 24, 26, 25, 14, 15, 12, 13]
  invFun := ![5, 6, 7, 4, 10, 11, 8, 9, 1, 2, 3, 0, 26, 27, 24, 25, 17, 19, 18, 16, 13, 14, 12, 15, 21, 23, 22, 20]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut26_isAut : IsAut nbhd aut26 := by decide

private def aut27 : Equiv.Perm Cell where
  toFun := ![12, 13, 14, 15, 0, 2, 1, 3, 18, 16, 19, 17, 4, 6, 5, 7, 22, 23, 20, 21, 8, 10, 9, 11, 26, 24, 25, 27]
  invFun := ![4, 6, 5, 7, 12, 14, 13, 15, 20, 22, 21, 23, 0, 1, 2, 3, 9, 11, 8, 10, 18, 19, 16, 17, 25, 26, 24, 27]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut27_isAut : IsAut nbhd aut27 := by decide

private def aut28 : Equiv.Perm Cell where
  toFun := ![12, 14, 13, 15, 4, 6, 5, 7, 22, 20, 23, 21, 0, 2, 1, 3, 18, 19, 16, 17, 9, 11, 8, 10, 26, 25, 24, 27]
  invFun := ![12, 14, 13, 15, 4, 6, 5, 7, 22, 20, 23, 21, 0, 2, 1, 3, 18, 19, 16, 17, 9, 11, 8, 10, 26, 25, 24, 27]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut28_isAut : IsAut nbhd aut28 := by decide

private def aut29 : Equiv.Perm Cell where
  toFun := ![12, 14, 15, 13, 9, 11, 8, 10, 26, 25, 27, 24, 1, 3, 0, 2, 18, 19, 17, 16, 4, 6, 5, 7, 22, 20, 21, 23]
  invFun := ![14, 12, 15, 13, 20, 22, 21, 23, 6, 4, 7, 5, 0, 3, 1, 2, 19, 18, 16, 17, 25, 26, 24, 27, 11, 9, 8, 10]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut29_isAut : IsAut nbhd aut29 := by decide

private def aut30 : Equiv.Perm Cell where
  toFun := ![13, 12, 14, 15, 24, 26, 25, 27, 10, 8, 11, 9, 5, 6, 4, 7, 23, 22, 21, 20, 16, 18, 17, 19, 2, 0, 1, 3]
  invFun := ![25, 26, 24, 27, 14, 12, 13, 15, 9, 11, 8, 10, 1, 0, 2, 3, 20, 22, 21, 23, 19, 18, 17, 16, 4, 6, 5, 7]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut30_isAut : IsAut nbhd aut30 := by decide

private def aut31 : Equiv.Perm Cell where
  toFun := ![13, 12, 15, 14, 16, 18, 17, 19, 2, 0, 3, 1, 4, 7, 5, 6, 23, 22, 20, 21, 24, 26, 25, 27, 10, 8, 9, 11]
  invFun := ![9, 11, 8, 10, 12, 14, 15, 13, 25, 26, 24, 27, 1, 0, 3, 2, 4, 6, 5, 7, 18, 19, 17, 16, 20, 22, 21, 23]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut31_isAut : IsAut nbhd aut31 := by decide

private def aut32 : Equiv.Perm Cell where
  toFun := ![13, 15, 12, 14, 4, 7, 5, 6, 23, 20, 22, 21, 16, 18, 17, 19, 2, 3, 0, 1, 25, 27, 24, 26, 10, 9, 8, 11]
  invFun := ![18, 19, 16, 17, 4, 6, 7, 5, 26, 25, 24, 27, 2, 0, 3, 1, 12, 14, 13, 15, 9, 11, 10, 8, 22, 20, 23, 21]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut32_isAut : IsAut nbhd aut32 := by decide

private def aut33 : Equiv.Perm Cell where
  toFun := ![14, 12, 13, 15, 25, 26, 24, 27, 11, 9, 10, 8, 1, 2, 0, 3, 19, 18, 17, 16, 20, 22, 21, 23, 6, 4, 5, 7]
  invFun := ![14, 12, 13, 15, 25, 26, 24, 27, 11, 9, 10, 8, 1, 2, 0, 3, 19, 18, 17, 16, 20, 22, 21, 23, 6, 4, 5, 7]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut33_isAut : IsAut nbhd aut33 := by decide

private def aut34 : Equiv.Perm Cell where
  toFun := ![15, 12, 13, 14, 17, 18, 16, 19, 3, 1, 2, 0, 9, 10, 8, 11, 27, 26, 25, 24, 21, 22, 20, 23, 7, 5, 4, 6]
  invFun := ![11, 9, 10, 8, 26, 25, 27, 24, 14, 12, 13, 15, 1, 2, 3, 0, 6, 4, 5, 7, 22, 20, 21, 23, 19, 18, 17, 16]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut34_isAut : IsAut nbhd aut34 := by decide

private def aut35 : Equiv.Perm Cell where
  toFun := ![16, 17, 18, 19, 4, 5, 7, 6, 24, 25, 26, 27, 13, 12, 15, 14, 0, 1, 2, 3, 20, 21, 23, 22, 8, 9, 10, 11]
  invFun := ![16, 17, 18, 19, 4, 5, 7, 6, 24, 25, 26, 27, 13, 12, 15, 14, 0, 1, 2, 3, 20, 21, 23, 22, 8, 9, 10, 11]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut35_isAut : IsAut nbhd aut35 := by decide

private def aut36 : Equiv.Perm Cell where
  toFun := ![17, 16, 18, 19, 9, 8, 10, 11, 21, 20, 22, 23, 15, 12, 13, 14, 1, 0, 3, 2, 25, 24, 27, 26, 5, 4, 7, 6]
  invFun := ![17, 16, 19, 18, 25, 24, 27, 26, 5, 4, 6, 7, 13, 14, 15, 12, 1, 0, 2, 3, 9, 8, 10, 11, 21, 20, 23, 22]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut36_isAut : IsAut nbhd aut36 := by decide

private def aut37 : Equiv.Perm Cell where
  toFun := ![18, 16, 17, 19, 10, 8, 9, 11, 22, 23, 21, 20, 7, 5, 4, 6, 26, 24, 27, 25, 2, 0, 3, 1, 12, 13, 15, 14]
  invFun := ![21, 23, 20, 22, 14, 13, 15, 12, 5, 6, 4, 7, 24, 25, 27, 26, 1, 2, 0, 3, 11, 10, 8, 9, 17, 19, 16, 18]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut37_isAut : IsAut nbhd aut37 := by decide

private def aut38 : Equiv.Perm Cell where
  toFun := ![19, 16, 17, 18, 27, 24, 25, 26, 6, 7, 5, 4, 23, 21, 20, 22, 11, 8, 10, 9, 3, 0, 2, 1, 14, 15, 13, 12]
  invFun := ![21, 23, 22, 20, 11, 10, 8, 9, 17, 19, 18, 16, 27, 26, 24, 25, 1, 2, 3, 0, 14, 13, 15, 12, 5, 6, 7, 4]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut38_isAut : IsAut nbhd aut38 := by decide

private def aut39 : Equiv.Perm Cell where
  toFun := ![20, 21, 22, 23, 0, 1, 3, 2, 25, 24, 26, 27, 14, 12, 15, 13, 4, 5, 6, 7, 16, 17, 19, 18, 9, 8, 11, 10]
  invFun := ![4, 5, 7, 6, 16, 17, 18, 19, 25, 24, 27, 26, 13, 15, 12, 14, 20, 21, 23, 22, 0, 1, 2, 3, 9, 8, 10, 11]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut39_isAut : IsAut nbhd aut39 := by decide

private def aut40 : Equiv.Perm Cell where
  toFun := ![20, 23, 21, 22, 15, 13, 14, 12, 4, 7, 5, 6, 16, 17, 19, 18, 9, 10, 8, 11, 3, 2, 0, 1, 25, 27, 24, 26]
  invFun := ![22, 23, 21, 20, 8, 10, 11, 9, 18, 16, 17, 19, 7, 5, 6, 4, 12, 13, 15, 14, 0, 2, 3, 1, 26, 24, 27, 25]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut40_isAut : IsAut nbhd aut40 := by decide

private def aut41 : Equiv.Perm Cell where
  toFun := ![21, 20, 22, 23, 8, 9, 11, 10, 17, 16, 18, 19, 15, 12, 14, 13, 5, 4, 7, 6, 24, 25, 27, 26, 1, 0, 3, 2]
  invFun := ![25, 24, 27, 26, 17, 16, 19, 18, 4, 5, 7, 6, 13, 15, 14, 12, 9, 8, 10, 11, 1, 0, 2, 3, 20, 21, 23, 22]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut41_isAut : IsAut nbhd aut41 := by decide

private def aut42 : Equiv.Perm Cell where
  toFun := ![22, 20, 21, 23, 11, 9, 8, 10, 18, 19, 17, 16, 3, 1, 0, 2, 26, 25, 27, 24, 6, 4, 7, 5, 12, 14, 15, 13]
  invFun := ![14, 13, 15, 12, 21, 23, 20, 22, 6, 5, 7, 4, 24, 27, 25, 26, 11, 10, 8, 9, 1, 2, 0, 3, 19, 17, 16, 18]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut42_isAut : IsAut nbhd aut42 := by decide

private def aut43 : Equiv.Perm Cell where
  toFun := ![22, 23, 20, 21, 0, 2, 3, 1, 26, 24, 25, 27, 6, 4, 7, 5, 12, 13, 14, 15, 8, 10, 11, 9, 18, 16, 19, 17]
  invFun := ![4, 7, 5, 6, 13, 15, 12, 14, 20, 23, 21, 22, 16, 17, 18, 19, 25, 27, 24, 26, 2, 3, 0, 1, 9, 10, 8, 11]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut43_isAut : IsAut nbhd aut43 := by decide

private def aut44 : Equiv.Perm Cell where
  toFun := ![23, 20, 21, 22, 27, 25, 24, 26, 2, 3, 1, 0, 19, 17, 16, 18, 10, 9, 11, 8, 7, 4, 6, 5, 13, 15, 14, 12]
  invFun := ![11, 10, 8, 9, 21, 23, 22, 20, 19, 17, 16, 18, 27, 24, 26, 25, 14, 13, 15, 12, 1, 2, 3, 0, 6, 5, 7, 4]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut44_isAut : IsAut nbhd aut44 := by decide

private def aut45 : Equiv.Perm Cell where
  toFun := ![24, 25, 26, 27, 5, 4, 6, 7, 16, 17, 18, 19, 13, 12, 14, 15, 8, 9, 10, 11, 21, 20, 23, 22, 0, 1, 2, 3]
  invFun := ![24, 25, 26, 27, 5, 4, 6, 7, 16, 17, 18, 19, 13, 12, 14, 15, 8, 9, 10, 11, 21, 20, 23, 22, 0, 1, 2, 3]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut45_isAut : IsAut nbhd aut45 := by decide

private def aut46 : Equiv.Perm Cell where
  toFun := ![25, 24, 26, 27, 1, 0, 2, 3, 20, 21, 22, 23, 14, 12, 13, 15, 9, 8, 11, 10, 17, 16, 19, 18, 4, 5, 6, 7]
  invFun := ![5, 4, 6, 7, 24, 25, 26, 27, 17, 16, 19, 18, 13, 14, 12, 15, 21, 20, 23, 22, 8, 9, 10, 11, 1, 0, 2, 3]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut46_isAut : IsAut nbhd aut46 := by decide

private def aut47 : Equiv.Perm Cell where
  toFun := ![26, 24, 25, 27, 2, 0, 1, 3, 22, 23, 20, 21, 6, 4, 5, 7, 18, 16, 19, 17, 10, 8, 11, 9, 12, 13, 14, 15]
  invFun := ![5, 6, 4, 7, 13, 14, 12, 15, 21, 23, 20, 22, 24, 25, 26, 27, 17, 19, 16, 18, 10, 11, 8, 9, 1, 2, 0, 3]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut47_isAut : IsAut nbhd aut47 := by decide

private def aut48 : Equiv.Perm Cell where
  toFun := ![27, 24, 25, 26, 19, 16, 17, 18, 7, 6, 4, 5, 23, 20, 21, 22, 3, 0, 2, 1, 11, 8, 10, 9, 15, 14, 13, 12]
  invFun := ![17, 19, 18, 16, 10, 11, 9, 8, 21, 23, 22, 20, 27, 26, 25, 24, 5, 6, 7, 4, 13, 14, 15, 12, 1, 2, 3, 0]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut48_isAut : IsAut nbhd aut48 := by decide

private def vertexAut : Cell → Equiv.Perm Cell := ![
  aut0, aut4, aut6, aut8, aut10, aut14, aut15, aut16, aut17, aut21, aut25, aut26, aut27, aut30, aut33, aut34, aut35, aut36, aut37, aut38, aut39, aut41, aut42, aut44, aut45, aut46, aut47, aut48]

private theorem vertexAut_isAut (v : Cell) : IsAut nbhd (vertexAut v) := by
  fin_cases v
  · exact aut0_isAut
  · exact aut4_isAut
  · exact aut6_isAut
  · exact aut8_isAut
  · exact aut10_isAut
  · exact aut14_isAut
  · exact aut15_isAut
  · exact aut16_isAut
  · exact aut17_isAut
  · exact aut21_isAut
  · exact aut25_isAut
  · exact aut26_isAut
  · exact aut27_isAut
  · exact aut30_isAut
  · exact aut33_isAut
  · exact aut34_isAut
  · exact aut35_isAut
  · exact aut36_isAut
  · exact aut37_isAut
  · exact aut38_isAut
  · exact aut39_isAut
  · exact aut41_isAut
  · exact aut42_isAut
  · exact aut44_isAut
  · exact aut45_isAut
  · exact aut46_isAut
  · exact aut47_isAut
  · exact aut48_isAut

private theorem vertexAut_zero : ∀ v, vertexAut v 0 = v := by decide


/-- Repeated diminishing returns, with a uniform price for the added cells. -/
private theorem adjoin_uniform {V : Type*} [DecidableEq V]
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (S D : Finset V) (b : ℝ)
    (hb : ∀ v ∈ D, increment h S v ≤ b) :
    h (S ∪ D) ≤ h S + (D.card : ℝ) * b := by
  revert hb
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | @insert v D hv ih =>
    intro hb
    have hi := ih (fun u hu => hb u (mem_insert_of_mem hu))
    have hs := (increment_antitone hh
      (subset_union_left : S ⊆ S ∪ D) v).trans (hb v (mem_insert_self v D))
    simp only [increment] at hs
    rw [union_insert, card_insert_of_notMem hv, Nat.cast_add, Nat.cast_one]
    linarith

/-- Pay for an explicit list of additional coordinates. -/
private theorem purchase {h : Finset Cell → ℝ} (hh : IsPolymatroid h)
    {s : ℝ} (hs : ∀ v, h {v} = s) {A B D : Finset Cell} {n : ℕ}
    (hcover : A ⊆ B ∪ D) (hcard : D.card = n) :
    h A ≤ h B + (n : ℝ) * s := by
  have h1 := adjoin_uniform hh B D s (fun v _ =>
    (increment_le_singleton hh B v).trans (hs v).le)
  rw [hcard] at h1
  exact (hh.mono hcover).trans h1

/-- A recovery step with its actual conditional-rank error retained. -/
private theorem recover_paid {h : Finset Cell → ℝ} (hh : IsPolymatroid h)
    {e : ℝ} (he : ∀ v, increment h (nbhd v) v = e)
    {A B D : Finset Cell} {n : ℕ}
    (hcover : A ⊆ B ∪ D) (hguard : ∀ v ∈ D, nbhd v ⊆ B)
    (hcard : D.card = n) : h A ≤ h B + (n : ℝ) * e := by
  have h1 := adjoin_uniform hh B D e (fun v hv =>
    (increment_antitone hh (hguard v hv) v).trans (he v).le)
  rw [hcard] at h1
  exact (hh.mono hcover).trans h1

private theorem singleton_uniform {h : Finset Cell → ℝ}
    (hi : ∀ σ, IsAut nbhd σ → ∀ S, h (S.map σ.toEmbedding) = h S) (v : Cell) :
    h {v} = h {0} := by
  have h1 := hi (vertexAut v) (vertexAut_isAut v) {0}
  simp only [map_singleton] at h1
  change h {vertexAut v 0} = h {0} at h1
  simpa only [vertexAut_zero] using h1

private theorem error_uniform {h : Finset Cell → ℝ}
    (hi : ∀ σ, IsAut nbhd σ → ∀ S, h (S.map σ.toEmbedding) = h S) (v : Cell) :
    increment h (nbhd v) v = increment h (nbhd 0) 0 := by
  have hn := hi (vertexAut v) (vertexAut_isAut v) (nbhd 0)
  have hi' := hi (vertexAut v) (vertexAut_isAut v) (insert 0 (nbhd 0))
  rw [(vertexAut_isAut v) 0, vertexAut_zero] at hn
  rw [map_insert] at hi'
  change h (insert (vertexAut v 0) ((nbhd 0).map (vertexAut v).toEmbedding)) =
    h (insert 0 (nbhd 0)) at hi'
  rw [(vertexAut_isAut v) 0, vertexAut_zero] at hi'
  simp only [increment]
  rw [hn, hi']


private theorem paid_invariant (h : Finset Cell → ℝ) (hh : IsPolymatroid h)
    (hi : ∀ σ, IsAut nbhd σ → ∀ S, h (S.map σ.toEmbedding) = h S) :
    3 * h univ ≤ 2 * ∑ v, h {v} + ∑ v, increment h (nbhd v) v := by
  let s := h ({0} : Finset Cell)
  let e := increment h (nbhd 0) 0
  have hs : ∀ v, h {v} = s := singleton_uniform hi
  have he : ∀ v, increment h (nbhd v) v = e := error_uniform hi

  have o0 : h {4, 5} = h {0, 1} := by
    have hx := hi aut10 aut10_isAut {4, 5}
    rw [show ({4, 5} : Finset Cell).map aut10.toEmbedding = {0, 1} by decide] at hx
    exact hx.symm

  have o1 : h {0, 1, 2, 3, 8, 9, 10, 11} = h {0, 1, 2, 3, 4, 5, 6, 7} := by
    have hx := hi aut5 aut5_isAut {0, 1, 2, 3, 8, 9, 10, 11}
    rw [show ({0, 1, 2, 3, 8, 9, 10, 11} : Finset Cell).map aut5.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7} by decide] at hx
    exact hx.symm

  have o2 : h {5, 7, 8, 9, 10, 11} = h {0, 1, 2, 3, 4, 6} := by
    have hx := hi aut17 aut17_isAut {5, 7, 8, 9, 10, 11}
    rw [show ({5, 7, 8, 9, 10, 11} : Finset Cell).map aut17.toEmbedding = {0, 1, 2, 3, 4, 6} by decide] at hx
    exact hx.symm

  have o3 : h {4, 5, 6, 7, 8, 9, 10, 11} = h {0, 1, 2, 3, 4, 5, 6, 7} := by
    have hx := hi aut17 aut17_isAut {4, 5, 6, 7, 8, 9, 10, 11}
    rw [show ({4, 5, 6, 7, 8, 9, 10, 11} : Finset Cell).map aut17.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7} by decide] at hx
    exact hx.symm

  have o4 : h {0, 1, 2, 3, 9, 12} = h {0, 1, 2, 3, 4, 12} := by
    have hx := hi aut5 aut5_isAut {0, 1, 2, 3, 9, 12}
    rw [show ({0, 1, 2, 3, 9, 12} : Finset Cell).map aut5.toEmbedding = {0, 1, 2, 3, 4, 12} by decide] at hx
    exact hx.symm

  have o5 : h {4, 5, 6, 7, 8, 9, 10, 11, 12} = h {0, 1, 2, 3, 4, 5, 6, 7, 12} := by
    have hx := hi aut17 aut17_isAut {4, 5, 6, 7, 8, 9, 10, 11, 12}
    rw [show ({4, 5, 6, 7, 8, 9, 10, 11, 12} : Finset Cell).map aut17.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 12} by decide] at hx
    exact hx.symm

  have o6 : h {4, 5, 6, 7, 13} = h {0, 1, 2, 3, 4} := by
    have hx := hi aut43 aut43_isAut {4, 5, 6, 7, 13}
    rw [show ({4, 5, 6, 7, 13} : Finset Cell).map aut43.toEmbedding = {0, 1, 2, 3, 4} by decide] at hx
    exact hx.symm

  have o7 : h {4, 5, 6, 7, 8, 9, 10, 11, 13} = h {0, 1, 2, 3, 4, 5, 6, 7, 13} := by
    have hx := hi aut17 aut17_isAut {4, 5, 6, 7, 8, 9, 10, 11, 13}
    rw [show ({4, 5, 6, 7, 8, 9, 10, 11, 13} : Finset Cell).map aut17.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 13} by decide] at hx
    exact hx.symm

  have o8 : h {12, 13, 14, 15} = h {0, 1, 2, 3} := by
    have hx := hi aut11 aut11_isAut {12, 13, 14, 15}
    rw [show ({12, 13, 14, 15} : Finset Cell).map aut11.toEmbedding = {0, 1, 2, 3} by decide] at hx
    exact hx.symm

  have o9 : h {0, 1, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 6} := by
    have hx := hi aut11 aut11_isAut {0, 1, 12, 13, 14, 15}
    rw [show ({0, 1, 12, 13, 14, 15} : Finset Cell).map aut11.toEmbedding = {0, 1, 2, 3, 4, 6} by decide] at hx
    exact hx.symm

  have o10 : h {0, 3, 4, 5, 6, 7, 12, 13, 14, 15} = h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13} := by
    have hx := hi aut29 aut29_isAut {0, 3, 4, 5, 6, 7, 12, 13, 14, 15}
    rw [show ({0, 3, 4, 5, 6, 7, 12, 13, 14, 15} : Finset Cell).map aut29.toEmbedding = {0, 1, 2, 3, 8, 9, 10, 11, 12, 13} by decide] at hx
    exact hx.symm

  have o11 : h {1, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 12} := by
    have hx := hi aut31 aut31_isAut {1, 8, 9, 10, 11, 12, 13, 14, 15}
    rw [show ({1, 8, 9, 10, 11, 12, 13, 14, 15} : Finset Cell).map aut31.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 12} by decide] at hx
    exact hx.symm

  have o12 : h {0, 1, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13} := by
    have hx := hi aut31 aut31_isAut {0, 1, 8, 9, 10, 11, 12, 13, 14, 15}
    rw [show ({0, 1, 8, 9, 10, 11, 12, 13, 14, 15} : Finset Cell).map aut31.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 12, 13} by decide] at hx
    exact hx.symm

  have o13 : h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15} = h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15} := by
    have hx := hi aut5 aut5_isAut {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15}
    rw [show ({0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15} : Finset Cell).map aut5.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15} by decide] at hx
    exact hx.symm

  have o14 : h {4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19} = h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} := by
    have hx := hi aut41 aut41_isAut {4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19}
    rw [show ({4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19} : Finset Cell).map aut41.toEmbedding = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} by decide] at hx
    exact hx.symm

  have o15 : h {0, 4, 5, 6, 7, 12, 13, 14, 15, 16, 20} = h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} := by
    have hx := hi aut28 aut28_isAut {0, 4, 5, 6, 7, 12, 13, 14, 15, 16, 20}
    rw [show ({0, 4, 5, 6, 7, 12, 13, 14, 15, 16, 20} : Finset Cell).map aut28.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} by decide] at hx
    exact hx.symm

  have o16 : h {0, 1, 2, 3, 4, 9, 12, 15, 16, 17, 18, 19, 20} = h {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20} := by
    have hx := hi aut9 aut9_isAut {0, 1, 2, 3, 4, 9, 12, 15, 16, 17, 18, 19, 20}
    rw [show ({0, 1, 2, 3, 4, 9, 12, 15, 16, 17, 18, 19, 20} : Finset Cell).map aut9.toEmbedding = {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20} by decide] at hx
    exact hx.symm

  have o17 : h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} = h {0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20} := by
    have hx := hi aut9 aut9_isAut {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} : Finset Cell).map aut9.toEmbedding = {0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20} by decide] at hx
    exact hx.symm

  have o18 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 22} = h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} := by
    have hx := hi aut10 aut10_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 22}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 22} : Finset Cell).map aut10.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} by decide] at hx
    exact hx.symm

  have o19 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 18, 22} = h {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20} := by
    have hx := hi aut2 aut2_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 18, 22}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 18, 22} : Finset Cell).map aut2.toEmbedding = {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20} by decide] at hx
    exact hx.symm

  have o20 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 22} = h {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20} := by
    have hx := hi aut10 aut10_isAut {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 22}
    rw [show ({0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 22} : Finset Cell).map aut10.toEmbedding = {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20} by decide] at hx
    exact hx.symm

  have o21 : h {0, 1, 2, 3, 8, 9, 10, 11, 14, 15, 20, 21, 22, 23} = h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} := by
    have hx := hi aut13 aut13_isAut {0, 1, 2, 3, 8, 9, 10, 11, 14, 15, 20, 21, 22, 23}
    rw [show ({0, 1, 2, 3, 8, 9, 10, 11, 14, 15, 20, 21, 22, 23} : Finset Cell).map aut13.toEmbedding = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} by decide] at hx
    exact hx.symm

  have o22 : h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 22, 23} = h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} := by
    have hx := hi aut10 aut10_isAut {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 22, 23}
    rw [show ({0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 22, 23} : Finset Cell).map aut10.toEmbedding = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} by decide] at hx
    exact hx.symm

  have o23 : h {7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} = h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} := by
    have hx := hi aut40 aut40_isAut {7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23}
    rw [show ({7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} : Finset Cell).map aut40.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} by decide] at hx
    exact hx.symm

  have o24 : h {0, 7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} = h {0, 1, 2, 3, 4, 8, 12, 13, 14, 15, 16, 20} := by
    have hx := hi aut20 aut20_isAut {0, 7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23}
    rw [show ({0, 7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} : Finset Cell).map aut20.toEmbedding = {0, 1, 2, 3, 4, 8, 12, 13, 14, 15, 16, 20} by decide] at hx
    exact hx.symm

  have o25 : h {0, 1, 4, 5, 6, 7, 8, 12, 15, 16, 20, 21, 22, 23} = h {0, 1, 2, 3, 4, 9, 10, 12, 13, 14, 15, 16, 18, 20} := by
    have hx := hi aut24 aut24_isAut {0, 1, 4, 5, 6, 7, 8, 12, 15, 16, 20, 21, 22, 23}
    rw [show ({0, 1, 4, 5, 6, 7, 8, 12, 15, 16, 20, 21, 22, 23} : Finset Cell).map aut24.toEmbedding = {0, 1, 2, 3, 4, 9, 10, 12, 13, 14, 15, 16, 18, 20} by decide] at hx
    exact hx.symm

  have o26 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23} = h {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22} := by
    have hx := hi aut11 aut11_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23} : Finset Cell).map aut11.toEmbedding = {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22} by decide] at hx
    exact hx.symm

  have o27 : h {0, 1, 2, 3, 4, 12, 13, 14, 15, 16, 20, 24} = h {0, 1, 2, 3, 4, 8, 12, 13, 14, 15, 16, 20} := by
    have hx := hi aut1 aut1_isAut {0, 1, 2, 3, 4, 12, 13, 14, 15, 16, 20, 24}
    rw [show ({0, 1, 2, 3, 4, 12, 13, 14, 15, 16, 20, 24} : Finset Cell).map aut1.toEmbedding = {0, 1, 2, 3, 4, 8, 12, 13, 14, 15, 16, 20} by decide] at hx
    exact hx.symm

  have o28 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 21, 22, 24} = h {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20} := by
    have hx := hi aut22 aut22_isAut {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 21, 22, 24}
    rw [show ({0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 21, 22, 24} : Finset Cell).map aut22.toEmbedding = {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20} by decide] at hx
    exact hx.symm

  have o29 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 17, 21, 22, 24} = h {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20, 24} := by
    have hx := hi aut22 aut22_isAut {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 17, 21, 22, 24}
    rw [show ({0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 17, 21, 22, 24} : Finset Cell).map aut22.toEmbedding = {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20, 24} by decide] at hx
    exact hx.symm

  have o30 : h {0, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} = h {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} := by
    have hx := hi aut3 aut3_isAut {0, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24}
    rw [show ({0, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} : Finset Cell).map aut3.toEmbedding = {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o31 : h {0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} := by
    have hx := hi aut17 aut17_isAut {0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24}
    rw [show ({0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} : Finset Cell).map aut17.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o32 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24} = h {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} := by
    have hx := hi aut19 aut19_isAut {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24}
    rw [show ({0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24} : Finset Cell).map aut19.toEmbedding = {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o33 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} := by
    have hx := hi aut18 aut18_isAut {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}
    rw [show ({0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} : Finset Cell).map aut18.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o34 : h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 25} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} := by
    have hx := hi aut10 aut10_isAut {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 25}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 25} : Finset Cell).map aut10.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o35 : h {1, 2, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 21, 23, 24, 25} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25} := by
    have hx := hi aut35 aut35_isAut {1, 2, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 21, 23, 24, 25}
    rw [show ({1, 2, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 21, 23, 24, 25} : Finset Cell).map aut35.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25} by decide] at hx
    exact hx.symm

  have o36 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26} = h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} := by
    have hx := hi aut11 aut11_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26} : Finset Cell).map aut11.toEmbedding = {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o37 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26} = h {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} := by
    have hx := hi aut11 aut11_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26} : Finset Cell).map aut11.toEmbedding = {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o38 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 22, 26} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} := by
    have hx := hi aut11 aut11_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 22, 26}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 22, 26} : Finset Cell).map aut11.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o39 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 22, 26} = h {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} := by
    have hx := hi aut32 aut32_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 22, 26}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 22, 26} : Finset Cell).map aut32.toEmbedding = {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o40 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 18, 20, 21, 22, 23, 26} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24} := by
    have hx := hi aut40 aut40_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 18, 20, 21, 22, 23, 26}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 18, 20, 21, 22, 23, 26} : Finset Cell).map aut40.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24} by decide] at hx
    exact hx.symm

  have o41 : h {0, 1, 2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15, 21, 24, 26} = h {0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20} := by
    have hx := hi aut17 aut17_isAut {0, 1, 2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15, 21, 24, 26}
    rw [show ({0, 1, 2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15, 21, 24, 26} : Finset Cell).map aut17.toEmbedding = {0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20} by decide] at hx
    exact hx.symm

  have o42 : h {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 24, 26} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25} := by
    have hx := hi aut5 aut5_isAut {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 24, 26}
    rw [show ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 24, 26} : Finset Cell).map aut5.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25} by decide] at hx
    exact hx.symm

  have o43 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 26} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} := by
    have hx := hi aut2 aut2_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 26}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 26} : Finset Cell).map aut2.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} by decide] at hx
    exact hx.symm

  have o44 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 26} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} := by
    have hx := hi aut27 aut27_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 26}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 26} : Finset Cell).map aut27.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} by decide] at hx
    exact hx.symm

  have o45 : h {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} := by
    have hx := hi aut19 aut19_isAut {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27}
    rw [show ({0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27} : Finset Cell).map aut19.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} by decide] at hx
    exact hx.symm

  have o46 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} := by
    have hx := hi aut7 aut7_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27} : Finset Cell).map aut7.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} by decide] at hx
    exact hx.symm

  have o47 : h {0, 1, 2, 3, 4, 5, 6, 7, 13, 24, 25, 26, 27} = h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} := by
    have hx := hi aut23 aut23_isAut {0, 1, 2, 3, 4, 5, 6, 7, 13, 24, 25, 26, 27}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 13, 24, 25, 26, 27} : Finset Cell).map aut23.toEmbedding = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} by decide] at hx
    exact hx.symm

  have o48 : h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 24, 25, 26, 27} = h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} := by
    have hx := hi aut12 aut12_isAut {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 24, 25, 26, 27}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 24, 25, 26, 27} : Finset Cell).map aut12.toEmbedding = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} by decide] at hx
    exact hx.symm

  have e0 : -h ∅ ≤ 0 := by
    have hn := hh.nonneg ∅
    linarith

  have cl1 : h {0, 1, 12, 13, 14, 15} ≤ h {0, 1, 12, 13, 14, 15} + 0 * e := by
    simp

  have raw1 : h {0, 1, 12, 13, 14, 15} + h ∅ ≤ h {0, 1} + h {12, 13, 14, 15} :=
    hh.elemental (by decide) (by decide)
  have e1 : h {0, 1, 12, 13, 14, 15} + h ∅ ≤ h {0, 1} + h {12, 13, 14, 15} + 0 * e := by
    linarith only [raw1, cl1]

  have cl2_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} + 4 * e := by
    exact recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}) (D := {12, 18, 22, 26}) (n := 4) (by decide) (by decide) (by decide)

  have cl2 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} + 4 * e := by
    linarith only [cl2_0]

  have raw2 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} + h ∅ ≤ h {0, 1, 2, 3, 4, 6} + h {5, 7, 8, 9, 10, 11} :=
    hh.elemental (by decide) (by decide)
  have e2 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26} + h ∅ ≤ h {0, 1, 2, 3, 4, 6} + h {5, 7, 8, 9, 10, 11} + 4 * e := by
    linarith only [raw2, cl2]

  have cl3_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} + 4 * e := by
    exact recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}) (D := {12, 18, 22, 26}) (n := 4) (by decide) (by decide) (by decide)

  have cl3 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} + 4 * e := by
    linarith only [cl3_0]

  have raw3 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} + h {4, 5} ≤ h {0, 1, 2, 3, 4, 5} + h {4, 5, 6, 7, 8, 9, 10, 11} :=
    hh.elemental (by decide) (by decide)
  have e3 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 22, 26} + h {4, 5} ≤ h {0, 1, 2, 3, 4, 5} + h {4, 5, 6, 7, 8, 9, 10, 11} + 4 * e := by
    linarith only [raw3, cl3]

  have cl4_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13} + 4 * e := by
    exact recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13}) (D := {12, 18, 22, 26}) (n := 4) (by decide) (by decide) (by decide)

  have cl4 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13} + 4 * e := by
    linarith only [cl4_0]

  have raw4 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13} + h {4, 5} ≤ h {0, 1, 2, 3, 4, 5} + h {4, 5, 6, 7, 8, 9, 10, 11, 13} :=
    hh.elemental (by decide) (by decide)
  have e4 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26} + h {4, 5} ≤ h {0, 1, 2, 3, 4, 5} + h {4, 5, 6, 7, 8, 9, 10, 11, 13} + 4 * e := by
    linarith only [raw4, cl4]

  have cl5 : h {0, 1, 2, 3, 4, 5} ≤ h {0, 1, 2, 3, 4, 5} + 0 * e := by
    simp

  have raw5 : h {0, 1, 2, 3, 4, 5} + h {0, 1, 2, 3} ≤ h {0, 1, 2, 3, 4} + h {0, 1, 2, 3, 5} :=
    hh.elemental (by decide) (by decide)
  have e5 : h {0, 1, 2, 3, 4, 5} + h {0, 1, 2, 3} ≤ h {0, 1, 2, 3, 4} + h {0, 1, 2, 3, 5} + 0 * e := by
    linarith only [raw5, cl5]

  have cl6 : h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} + 0 * e := by
    simp

  have raw6 : h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} + h {0, 1, 2, 3, 4} ≤ h {0, 1, 2, 3, 4, 5, 6, 7} + h {0, 1, 2, 3, 4, 9, 12, 15, 16, 17, 18, 19, 20} :=
    hh.elemental (by decide) (by decide)
  have e6 : h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} + h {0, 1, 2, 3, 4} ≤ h {0, 1, 2, 3, 4, 5, 6, 7} + h {0, 1, 2, 3, 4, 9, 12, 15, 16, 17, 18, 19, 20} + 0 * e := by
    linarith only [raw6, cl6]

  have cl7_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13} + 4 * e := by
    exact recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13}) (D := {12, 18, 22, 26}) (n := 4) (by decide) (by decide) (by decide)

  have cl7 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13} + 4 * e := by
    linarith only [cl7_0]

  have raw7 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13} + h {4, 5, 6, 7, 13} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 13} + h {4, 5, 6, 7, 8, 9, 10, 11, 13} :=
    hh.elemental (by decide) (by decide)
  have e7 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18, 22, 26} + h {4, 5, 6, 7, 13} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 13} + h {4, 5, 6, 7, 8, 9, 10, 11, 13} + 4 * e := by
    linarith only [raw7, cl7]

  have buy8 : h ∅ ≤ h ∅ + 0 * s := by
    simpa only [Nat.cast_zero] using (purchase hh hs (A := ∅) (B := ∅) (D := ∅) (n := 0) (by decide) (by decide))

  have cl8 : h ∅ ≤ h ∅ + 0 * e := by
    simp

  have extra8 : h {0, 1, 2, 3, 5} ≤ h ∅ + 5 * s := by
    exact purchase hh hs (A := {0, 1, 2, 3, 5}) (B := ∅) (D := {0, 1, 2, 3, 5}) (n := 5) (by decide) (by decide)

  have e8 : h {0, 1, 2, 3, 5} ≤ 5 * s + 0 * e := by
    linarith only [buy8, cl8, extra8, hh.empty]

  have e9 : h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13} ≤ h {0, 1, 2, 3, 9, 12} + 4 * s := by
    exact purchase hh hs (A := {0, 1, 2, 3, 8, 9, 10, 11, 12, 13}) (B := {0, 1, 2, 3, 9, 12}) (D := {8, 10, 11, 13}) (n := 4) (by decide) (by decide)

  have cl10 : h {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20, 24} ≤ h {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20, 24} + 0 * e := by
    simp

  have raw10 : h {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20, 24} + h {0, 1, 2, 3, 4, 12} ≤ h {0, 1, 2, 3, 4, 9, 12, 18} + h {0, 1, 2, 3, 4, 12, 13, 14, 15, 16, 20, 24} :=
    hh.elemental (by decide) (by decide)
  have e10 : h {0, 1, 2, 3, 4, 9, 12, 13, 14, 15, 16, 18, 20, 24} + h {0, 1, 2, 3, 4, 12} ≤ h {0, 1, 2, 3, 4, 9, 12, 18} + h {0, 1, 2, 3, 4, 12, 13, 14, 15, 16, 20, 24} + 0 * e := by
    linarith only [raw10, cl10]

  have cl11 : h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 22, 23} ≤ h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 22, 23} + 0 * e := by
    simp

  have raw11 : h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 22, 23} + h {0, 1, 2, 3, 8, 9, 10, 11} ≤ h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13} + h {0, 1, 2, 3, 8, 9, 10, 11, 14, 15, 20, 21, 22, 23} :=
    hh.elemental (by decide) (by decide)
  have e11 : h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 22, 23} + h {0, 1, 2, 3, 8, 9, 10, 11} ≤ h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13} + h {0, 1, 2, 3, 8, 9, 10, 11, 14, 15, 20, 21, 22, 23} + 0 * e := by
    linarith only [raw11, cl11]

  have buy12 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15} ≤ h {0, 1, 2, 3, 10, 11, 13, 14} + 7 * s := by
    exact purchase hh hs (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15}) (B := {0, 1, 2, 3, 10, 11, 13, 14}) (D := {4, 5, 6, 7, 8, 9, 15}) (n := 7) (by decide) (by decide)

  have cl12_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15} + 4 * e := by
    exact recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 22, 26}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15}) (D := {12, 18, 22, 26}) (n := 4) (by decide) (by decide) (by decide)

  have cl12 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 22, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15} + 4 * e := by
    linarith only [cl12_0]

  have e12 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 22, 26} ≤ h {0, 1, 2, 3, 10, 11, 13, 14} + 7 * s + 4 * e := by
    linarith only [buy12, cl12]

  have buy13 : h ∅ ≤ h ∅ + 0 * s := by
    simpa only [Nat.cast_zero] using (purchase hh hs (A := ∅) (B := ∅) (D := ∅) (n := 0) (by decide) (by decide))

  have cl13 : h ∅ ≤ h ∅ + 0 * e := by
    simp

  have extra13 : h {0, 1, 2, 3, 10, 11, 13, 14} ≤ h ∅ + 8 * s := by
    exact purchase hh hs (A := {0, 1, 2, 3, 10, 11, 13, 14}) (B := ∅) (D := {0, 1, 2, 3, 10, 11, 13, 14}) (n := 8) (by decide) (by decide)

  have e13 : h {0, 1, 2, 3, 10, 11, 13, 14} ≤ 8 * s + 0 * e := by
    linarith only [buy13, cl13, extra13, hh.empty]

  have cl14 : h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} + 0 * e := by
    simp

  have raw14 : h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} + h {0, 1, 2, 3, 4, 9, 12, 18} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} + h {0, 1, 2, 3, 4, 9, 12, 15, 16, 17, 18, 19, 20} :=
    hh.elemental (by decide) (by decide)
  have e14 : h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 15, 16, 17, 18, 19, 20} + h {0, 1, 2, 3, 4, 9, 12, 18} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} + h {0, 1, 2, 3, 4, 9, 12, 15, 16, 17, 18, 19, 20} + 0 * e := by
    linarith only [raw14, cl14]

  have buy15 : h {0, 1, 8, 9, 10, 11, 12, 13, 14, 15} ≤ h {1, 8, 9, 10, 11, 12, 13, 14, 15} + 1 * s := by
    simpa only [Nat.cast_one] using (purchase hh hs (A := {0, 1, 8, 9, 10, 11, 12, 13, 14, 15}) (B := {1, 8, 9, 10, 11, 12, 13, 14, 15}) (D := {0}) (n := 1) (by decide) (by decide))

  have cl15 : h {0, 1, 8, 9, 10, 11, 12, 13, 14, 15} ≤ h {0, 1, 8, 9, 10, 11, 12, 13, 14, 15} + 0 * e := by
    simp

  have e15 : h {0, 1, 8, 9, 10, 11, 12, 13, 14, 15} ≤ h {1, 8, 9, 10, 11, 12, 13, 14, 15} + 1 * s + 0 * e := by
    linarith only [buy15, cl15]

  have cl16 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 18, 22} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 18, 22} + 0 * e := by
    simp

  have raw16 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 18, 22} + h {0, 1, 2, 3, 4, 5, 6, 7, 12} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 22} :=
    hh.elemental (by decide) (by decide)
  have e16 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 18, 22} + h {0, 1, 2, 3, 4, 5, 6, 7, 12} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 18} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 22} + 0 * e := by
    linarith only [raw16, cl16]

  have cl17_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 26} + 2 * e := by
    exact recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 26}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 26}) (D := {20, 25}) (n := 2) (by decide) (by decide) (by decide)

  have cl17 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 26} + 2 * e := by
    linarith only [cl17_0]

  have raw17 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 26} + h {4, 5, 6, 7, 8, 9, 10, 11, 12} ≤ h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 22, 26} :=
    hh.elemental (by decide) (by decide)
  have e17 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 26} + h {4, 5, 6, 7, 8, 9, 10, 11, 12} ≤ h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 22, 26} + 2 * e := by
    linarith only [raw17, cl17]

  have cl18 : h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 24, 25, 26, 27} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 24, 25, 26, 27} + 0 * e := by
    simp

  have raw18 : h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 24, 25, 26, 27} + h {0, 1, 2, 3, 4, 5, 6, 7, 13} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13} + h {0, 1, 2, 3, 4, 5, 6, 7, 13, 24, 25, 26, 27} :=
    hh.elemental (by decide) (by decide)
  have e18 : h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 24, 25, 26, 27} + h {0, 1, 2, 3, 4, 5, 6, 7, 13} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13} + h {0, 1, 2, 3, 4, 5, 6, 7, 13, 24, 25, 26, 27} + 0 * e := by
    linarith only [raw18, cl18]

  have cl19 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + 0 * e := by
    simp

  have raw19 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + h {0, 3, 4, 5, 6, 7, 12, 13, 14, 15} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15} + h {0, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} :=
    hh.elemental (by decide) (by decide)
  have e19 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + h {0, 3, 4, 5, 6, 7, 12, 13, 14, 15} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15} + h {0, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + 0 * e := by
    linarith only [raw19, cl19]

  have buy20 : h {0, 7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} ≤ h {7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} + 1 * s := by
    simpa only [Nat.cast_one] using (purchase hh hs (A := {0, 7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23}) (B := {7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23}) (D := {0}) (n := 1) (by decide) (by decide))

  have cl20 : h {0, 7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} ≤ h {0, 7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} + 0 * e := by
    simp

  have e20 : h {0, 7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} ≤ h {7, 8, 9, 10, 11, 15, 16, 20, 21, 22, 23} + 1 * s + 0 * e := by
    linarith only [buy20, cl20]

  have cl21 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + 0 * e := by
    simp

  have raw21 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + h {0, 4, 5, 6, 7, 12, 13, 14, 15, 16, 20} ≤ h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 25} :=
    hh.elemental (by decide) (by decide)
  have e21 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + h {0, 4, 5, 6, 7, 12, 13, 14, 15, 16, 20} ≤ h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + h {0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 25} + 0 * e := by
    linarith only [raw21, cl21]

  have cl22 : h {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 24, 26} ≤ h {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 24, 26} + 0 * e := by
    simp

  have raw22 : h {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 24, 26} + h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15} ≤ h {0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20} + h {0, 1, 2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15, 21, 24, 26} :=
    hh.elemental (by decide) (by decide)
  have e22 : h {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 24, 26} + h {0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15} ≤ h {0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20} + h {0, 1, 2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15, 21, 24, 26} + 0 * e := by
    linarith only [raw22, cl22]

  have cl23_0 : h {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27} ≤ h {0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} + 2 * e := by
    exact recover_paid hh he (A := {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27}) (B := {0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}) (D := {3, 27}) (n := 2) (by decide) (by decide) (by decide)

  have cl23 : h {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27} ≤ h {0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} + 2 * e := by
    linarith only [cl23_0]

  have raw23 : h {0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} + h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} ≤ h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} + h {0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} :=
    hh.elemental (by decide) (by decide)
  have e23 : h {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27} + h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} ≤ h {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} + h {0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + 2 * e := by
    linarith only [raw23, cl23]

  have cl24 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} ≤ h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} + 0 * e := by
    simp

  have raw24 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} + h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 21, 22, 24} ≤ h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 17, 18, 21, 22, 24} + h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24} :=
    hh.elemental (by decide) (by decide)
  have e24 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} + h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 21, 22, 24} ≤ h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 17, 18, 21, 22, 24} + h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24} + 0 * e := by
    linarith only [raw24, cl24]

  have cl25_0 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26} + 1 * e := by
    simpa only [Nat.cast_one] using (recover_paid hh he (A := univ) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26}) (D := {27}) (n := 1) (by decide) (by decide) (by decide))

  have cl25 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26} + 1 * e := by
    linarith only [cl25_0]

  have raw25 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26} + h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 22} ≤ h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 26} :=
    hh.elemental (by decide) (by decide)
  have e25 : h univ + h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 22} ≤ h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 26} + 1 * e := by
    linarith only [raw25, cl25]

  have cl26_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + 1 * e := by
    simpa only [Nat.cast_one] using (recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25}) (D := {26}) (n := 1) (by decide) (by decide) (by decide))

  have cl26_1 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26} + 1 * e := by
    simpa only [Nat.cast_one] using (recover_paid hh he (A := univ) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26}) (D := {27}) (n := 1) (by decide) (by decide) (by decide))

  have cl26 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + 2 * e := by
    linarith only [cl26_0, cl26_1]

  have raw26 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + h {4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19} ≤ h {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22} + h {1, 2, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 21, 23, 24, 25} :=
    hh.elemental (by decide) (by decide)
  have e26 : h univ + h {4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19} ≤ h {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22} + h {1, 2, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 21, 23, 24, 25} + 2 * e := by
    linarith only [raw26, cl26]

  have e27 : h {0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20} ≤ h {0, 1, 2, 3, 4, 9, 10, 12, 13, 14, 15, 16, 18, 20} + 2 * s := by
    exact purchase hh hs (A := {0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20}) (B := {0, 1, 2, 3, 4, 9, 10, 12, 13, 14, 15, 16, 18, 20}) (D := {8, 11}) (n := 2) (by decide) (by decide)

  have cl28 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 26} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 26} + 0 * e := by
    simp

  have raw28 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 26} + h {0, 1, 4, 5, 6, 7, 8, 12, 15, 16, 20, 21, 22, 23} ≤ h {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 18, 20, 21, 22, 23, 26} :=
    hh.elemental (by decide) (by decide)
  have e28 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 26} + h {0, 1, 4, 5, 6, 7, 8, 12, 15, 16, 20, 21, 22, 23} ≤ h {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 18, 20, 21, 22, 23, 26} + 0 * e := by
    linarith only [raw28, cl28]

  have e29 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 17, 18, 21, 22, 24} ≤ h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 17, 21, 22, 24} + 1 * s := by
    simpa only [Nat.cast_one] using (purchase hh hs (A := {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 17, 18, 21, 22, 24}) (B := {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 17, 21, 22, 24}) (D := {18}) (n := 1) (by decide) (by decide))

  have buy30 : h {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23} ≤ h ∅ + 12 * s := by
    exact purchase hh hs (A := {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23}) (B := ∅) (D := {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23}) (n := 12) (by decide) (by decide)

  have cl30_0 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} ≤ h {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23} + 4 * e := by
    exact recover_paid hh he (A := {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24}) (B := {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23}) (D := {0, 8, 16, 24}) (n := 4) (by decide) (by decide) (by decide)

  have cl30 : h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} ≤ h {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23} + 4 * e := by
    linarith only [cl30_0]

  have extra30 : h {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} ≤ h {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} + 1 * s := by
    simpa only [Nat.cast_one] using (purchase hh hs (A := {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24}) (B := {0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24}) (D := {1}) (n := 1) (by decide) (by decide))

  have e30 : h {0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24} ≤ 13 * s + 4 * e := by
    linarith only [buy30, cl30, extra30, hh.empty]

  have cl31 : h univ ≤ h univ + 0 * e := by
    simp

  have raw31 : h univ + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27} :=
    hh.elemental (by decide) (by decide)
  have e31 : h univ + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27} + 0 * e := by
    linarith only [raw31, cl31]

  have cl32_0 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26} + 1 * e := by
    simpa only [Nat.cast_one] using (recover_paid hh he (A := univ) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26}) (D := {27}) (n := 1) (by decide) (by decide) (by decide))

  have cl32 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26} + 1 * e := by
    linarith only [cl32_0]

  have raw32 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 26} :=
    hh.elemental (by decide) (by decide)
  have e32 : h univ + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 26} + 1 * e := by
    linarith only [raw32, cl32]

  simp only [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25, o26, o27, o28, o29, o30, o31, o32, o33, o34, o35, o36, o37, o38, o39, o40, o41, o42, o43, o44, o45, o46, o47, o48] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 e32

  have certificate : 264 * h univ ≤ 4928 * s + 2464 * e := by
    linear_combination 117 * e0 +
      78 * e1 +
      39 * e2 +
      63 * e3 +
      15 * e4 +
      78 * e5 +
      36 * e6 +
      42 * e7 +
      78 * e8 +
      22 * e9 +
      22 * e10 +
      99 * e11 +
      88 * e12 +
      88 * e13 +
      22 * e14 +
      99 * e15 +
      22 * e16 +
      77 * e17 +
      99 * e18 +
      77 * e19 +
      22 * e20 +
      88 * e21 +
      77 * e22 +
      99 * e23 +
      22 * e24 +
      14 * e25 +
      77 * e26 +
      96 * e27 +
      96 * e28 +
      22 * e29 +
      215 * e30 +
      77 * e31 +
      96 * e32


  have hs_sum : (∑ v, h {v}) = 28 * s := by simp_rw [hs]; simp
  have he_sum : (∑ v, increment h (nbhd v) v) = 28 * e := by simp_rw [he]; simp
  rw [hs_sum, he_sum]
  linarith only [certificate]


/-- Averaging preserves the sum of the actual per-coordinate recovery errors. -/
private theorem sum_symmetrize_error (h : Finset Cell → ℝ) :
    ∑ v, increment (symmetrize nbhd h) (nbhd v) v =
      ∑ v, increment h (nbhd v) v := by
  have e : ∀ σ ∈ autSet nbhd,
      (∑ v, (relabel σ h (insert v (nbhd v)) - relabel σ h (nbhd v))) =
        ∑ v, increment h (nbhd v) v := by
    intro σ hσ
    have ha : ∀ v, (nbhd v).map σ.toEmbedding = nbhd (σ v) := mem_autSet.mp hσ
    simp only [relabel, map_insert, ha]
    change (∑ v, increment h (nbhd (σ v)) (σ v)) = _
    exact Equiv.sum_comp σ (fun v => increment h (nbhd v) v)
  simp only [increment, symmetrize, ← mul_sub, ← Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have he :
      (∑ σ ∈ autSet nbhd,
        ∑ v, (relabel σ h (insert v (nbhd v)) - relabel σ h (nbhd v))) =
      ∑ σ ∈ autSet nbhd, ∑ v, increment h (nbhd v) v := by
    apply Finset.sum_congr rfl
    intro σ hσ
    exact e σ hσ
  rw [he]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [(autSet_card_pos nbhd).ne']
  rfl

/-- The paid Fano inequality on the actual 28-coordinate residual helper graph. -/
theorem paid_fano (h : Finset Cell → ℝ) (hh : IsPolymatroid h) :
    3 * h univ ≤ 2 * ∑ v, h {v} + ∑ v, increment h (nbhd v) v := by
  have hp := paid_invariant (symmetrize nbhd h) (hh.symmetrize nbhd)
    (fun σ hσ S => symmetrize_invariant nbhd h hσ S)
  rwa [symmetrize_univ, sum_symmetrize_singleton, sum_symmetrize_error] at hp

/-- Exact recovery gives the weighted two-thirds rate bound, without caps. -/
theorem rateBound_fano : RateBound nbhd (2 / 3) := by
  intro h hh hv
  have hp := paid_fano h hh
  have he : (∑ v, increment h (nbhd v) v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp only [increment, hv v, sub_self]
  rw [he] at hp
  linarith

/-- Unit scalar capacities give the residual bound 56/3. -/
theorem residual_le (h : Finset Cell → ℝ) (hh : IsPolymatroid h)
    (hv : IsValid h nbhd) (hc : ∀ v, h {v} ≤ 1) : h univ ≤ 56 / 3 := by
  have hp := rateBound_fano h hh hv
  have hs : (∑ v, h {v}) ≤ 28 := by
    calc
      _ ≤ ∑ _ : Cell, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hc v)
      _ = 28 := by norm_num
  linarith

end LeanBacklog.FanoCertificate

#print axioms LeanBacklog.FanoCertificate.paid_fano
#print axioms LeanBacklog.FanoCertificate.rateBound_fano
#print axioms LeanBacklog.FanoCertificate.residual_le
