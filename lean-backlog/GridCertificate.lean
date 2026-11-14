import ShannonCertificate

/-!
# The paid grid Shannon certificate

Generated from the saved 18-term certificate by tools/grid-shannon/generate_lean.py.
Every finite map is checked against the actual residual grid helper relation.
Each certificate inequality follows from polymatroid submodularity, an explicit
coordinate purchase, or a paid recovery step. The final integer combination is
kernel-checked. No exact-recovery, capacity, or symmetry premise is imposed on
the paid theorem. In particular the upper bound is not asserted to be sharp.

The 36 coordinates are the nonincident pairs of nine point rows and six line
columns. A point p has grid coordinates (p / 3, p % 3); lines 0,1,2 fix the first
coordinate and lines 3,4,5 fix the second. The cell indexing is lexicographic.
-/

namespace LeanBacklog.GridCertificate

open Finset MotionDepthCodes SoftRecovery ShannonCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev Cell := Fin 36

/-- Actual point-line incidence in the three-by-three grid. -/
def incident (p : Fin 9) (l : Fin 6) : Prop :=
  if l.val < 3 then p.val / 3 = l.val else p.val % 3 = l.val - 3

instance (p : Fin 9) (l : Fin 6) : Decidable (incident p l) := by
  unfold incident
  infer_instance

def row : Cell → Fin 9 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8]

def column : Cell → Fin 6 := ![1, 2, 4, 5, 1, 2, 3, 5, 1, 2, 3, 4, 0, 2, 4, 5, 0, 2, 3, 5, 0, 2, 3, 4, 0, 1, 4, 5, 0, 1, 3, 5, 0, 1, 3, 4]

/-- The twelve actual residual helper cells of each target. -/
def nbhd : Cell → Finset Cell := ![
  {12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23},
  {24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35},
  {4, 5, 6, 7, 16, 17, 18, 19, 28, 29, 30, 31},
  {8, 9, 10, 11, 20, 21, 22, 23, 32, 33, 34, 35},
  {12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23},
  {24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35},
  {0, 1, 2, 3, 12, 13, 14, 15, 24, 25, 26, 27},
  {8, 9, 10, 11, 20, 21, 22, 23, 32, 33, 34, 35},
  {12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23},
  {24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35},
  {0, 1, 2, 3, 12, 13, 14, 15, 24, 25, 26, 27},
  {4, 5, 6, 7, 16, 17, 18, 19, 28, 29, 30, 31},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35},
  {4, 5, 6, 7, 16, 17, 18, 19, 28, 29, 30, 31},
  {8, 9, 10, 11, 20, 21, 22, 23, 32, 33, 34, 35},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35},
  {0, 1, 2, 3, 12, 13, 14, 15, 24, 25, 26, 27},
  {8, 9, 10, 11, 20, 21, 22, 23, 32, 33, 34, 35},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35},
  {0, 1, 2, 3, 12, 13, 14, 15, 24, 25, 26, 27},
  {4, 5, 6, 7, 16, 17, 18, 19, 28, 29, 30, 31},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23},
  {4, 5, 6, 7, 16, 17, 18, 19, 28, 29, 30, 31},
  {8, 9, 10, 11, 20, 21, 22, 23, 32, 33, 34, 35},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23},
  {0, 1, 2, 3, 12, 13, 14, 15, 24, 25, 26, 27},
  {8, 9, 10, 11, 20, 21, 22, 23, 32, 33, 34, 35},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
  {12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23},
  {0, 1, 2, 3, 12, 13, 14, 15, 24, 25, 26, 27},
  {4, 5, 6, 7, 16, 17, 18, 19, 28, 29, 30, 31}]


theorem cells_nonincident : ∀ v, ¬incident (row v) (column v) := by decide
theorem cells_injective : Function.Injective (fun v : Cell => (row v, column v)) := by decide
theorem cells_complete : ∀ p l, ¬incident p l → ∃ v, row v = p ∧ column v = l := by decide
theorem nbhd_eq_incidence : ∀ v, nbhd v =
    univ.filter (fun w => incident (row w) (column v)) := by decide
theorem nbhd_iff (u v : Cell) : u ∈ nbhd v ↔ incident (row u) (column v) := by
  rw [nbhd_eq_incidence]
  simp
theorem nbhd_card : ∀ v, (nbhd v).card = 12 := by decide
theorem loopless : ∀ v, v ∉ nbhd v := by
  intro v
  rw [nbhd_iff]
  exact cells_nonincident v

/-- No three cells are pairwise mutual helpers; distinctness need not be assumed. -/
theorem mutual_triangle_free : ∀ u v : Cell, v ∈ nbhd u → u ∈ nbhd v →
    ∀ w : Cell, w ∈ nbhd u → u ∈ nbhd w → w ∈ nbhd v → v ∈ nbhd w → False := by
  decide

private def aut0 : Equiv.Perm Cell where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut0_isAut : IsAut nbhd aut0 := by decide

private def aut1 : Equiv.Perm Cell where
  toFun := ![1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut1_isAut : IsAut nbhd aut1 := by decide

private def aut2 : Equiv.Perm Cell where
  toFun := ![2, 3, 0, 1, 14, 15, 12, 13, 26, 27, 24, 25, 6, 7, 4, 5, 18, 19, 16, 17, 30, 31, 28, 29, 10, 11, 8, 9, 22, 23, 20, 21, 34, 35, 32, 33]
  invFun := ![2, 3, 0, 1, 14, 15, 12, 13, 26, 27, 24, 25, 6, 7, 4, 5, 18, 19, 16, 17, 30, 31, 28, 29, 10, 11, 8, 9, 22, 23, 20, 21, 34, 35, 32, 33]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut2_isAut : IsAut nbhd aut2 := by decide

private def aut3 : Equiv.Perm Cell where
  toFun := ![3, 2, 0, 1, 15, 14, 12, 13, 27, 26, 24, 25, 10, 11, 8, 9, 22, 23, 20, 21, 34, 35, 32, 33, 6, 7, 4, 5, 18, 19, 16, 17, 30, 31, 28, 29]
  invFun := ![2, 3, 1, 0, 26, 27, 24, 25, 14, 15, 12, 13, 6, 7, 5, 4, 30, 31, 28, 29, 18, 19, 16, 17, 10, 11, 9, 8, 34, 35, 32, 33, 22, 23, 20, 21]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut3_isAut : IsAut nbhd aut3 := by decide

private def aut4 : Equiv.Perm Cell where
  toFun := ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 11, 10, 16, 17, 18, 19, 12, 13, 14, 15, 20, 21, 23, 22, 28, 29, 30, 31, 24, 25, 26, 27, 32, 33, 35, 34]
  invFun := ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 11, 10, 16, 17, 18, 19, 12, 13, 14, 15, 20, 21, 23, 22, 28, 29, 30, 31, 24, 25, 26, 27, 32, 33, 35, 34]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut4_isAut : IsAut nbhd aut4 := by decide

private def aut5 : Equiv.Perm Cell where
  toFun := ![4, 5, 7, 6, 8, 9, 11, 10, 0, 1, 2, 3, 16, 17, 19, 18, 20, 21, 23, 22, 12, 13, 14, 15, 28, 29, 31, 30, 32, 33, 35, 34, 24, 25, 26, 27]
  invFun := ![8, 9, 10, 11, 0, 1, 3, 2, 4, 5, 7, 6, 20, 21, 22, 23, 12, 13, 15, 14, 16, 17, 19, 18, 32, 33, 34, 35, 24, 25, 27, 26, 28, 29, 31, 30]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut5_isAut : IsAut nbhd aut5 := by decide

private def aut6 : Equiv.Perm Cell where
  toFun := ![5, 4, 6, 7, 1, 0, 2, 3, 9, 8, 11, 10, 28, 29, 30, 31, 24, 25, 26, 27, 32, 33, 35, 34, 16, 17, 18, 19, 12, 13, 14, 15, 20, 21, 23, 22]
  invFun := ![5, 4, 6, 7, 1, 0, 2, 3, 9, 8, 11, 10, 28, 29, 30, 31, 24, 25, 26, 27, 32, 33, 35, 34, 16, 17, 18, 19, 12, 13, 14, 15, 20, 21, 23, 22]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut6_isAut : IsAut nbhd aut6 := by decide

private def aut7 : Equiv.Perm Cell where
  toFun := ![6, 7, 4, 5, 18, 19, 16, 17, 30, 31, 28, 29, 2, 3, 0, 1, 14, 15, 12, 13, 26, 27, 24, 25, 11, 10, 8, 9, 23, 22, 20, 21, 35, 34, 32, 33]
  invFun := ![14, 15, 12, 13, 2, 3, 0, 1, 26, 27, 25, 24, 18, 19, 16, 17, 6, 7, 4, 5, 30, 31, 29, 28, 22, 23, 20, 21, 10, 11, 8, 9, 34, 35, 33, 32]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut7_isAut : IsAut nbhd aut7 := by decide

private def aut8 : Equiv.Perm Cell where
  toFun := ![7, 6, 4, 5, 19, 18, 16, 17, 31, 30, 28, 29, 11, 10, 8, 9, 23, 22, 20, 21, 35, 34, 32, 33, 2, 3, 0, 1, 14, 15, 12, 13, 26, 27, 24, 25]
  invFun := ![26, 27, 24, 25, 2, 3, 1, 0, 14, 15, 13, 12, 30, 31, 28, 29, 6, 7, 5, 4, 18, 19, 17, 16, 34, 35, 32, 33, 10, 11, 9, 8, 22, 23, 21, 20]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut8_isAut : IsAut nbhd aut8 := by decide

private def aut9 : Equiv.Perm Cell where
  toFun := ![8, 9, 10, 11, 0, 1, 3, 2, 4, 5, 7, 6, 20, 21, 22, 23, 12, 13, 15, 14, 16, 17, 19, 18, 32, 33, 34, 35, 24, 25, 27, 26, 28, 29, 31, 30]
  invFun := ![4, 5, 7, 6, 8, 9, 11, 10, 0, 1, 2, 3, 16, 17, 19, 18, 20, 21, 23, 22, 12, 13, 14, 15, 28, 29, 31, 30, 32, 33, 35, 34, 24, 25, 26, 27]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut9_isAut : IsAut nbhd aut9 := by decide

private def aut10 : Equiv.Perm Cell where
  toFun := ![9, 8, 10, 11, 1, 0, 3, 2, 5, 4, 7, 6, 32, 33, 34, 35, 24, 25, 27, 26, 28, 29, 31, 30, 20, 21, 22, 23, 12, 13, 15, 14, 16, 17, 19, 18]
  invFun := ![5, 4, 7, 6, 9, 8, 11, 10, 1, 0, 2, 3, 28, 29, 31, 30, 32, 33, 35, 34, 24, 25, 26, 27, 16, 17, 19, 18, 20, 21, 23, 22, 12, 13, 14, 15]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut10_isAut : IsAut nbhd aut10 := by decide

private def aut11 : Equiv.Perm Cell where
  toFun := ![10, 11, 8, 9, 22, 23, 20, 21, 34, 35, 32, 33, 3, 2, 0, 1, 15, 14, 12, 13, 27, 26, 24, 25, 7, 6, 4, 5, 19, 18, 16, 17, 31, 30, 28, 29]
  invFun := ![14, 15, 13, 12, 26, 27, 25, 24, 2, 3, 0, 1, 18, 19, 17, 16, 30, 31, 29, 28, 6, 7, 4, 5, 22, 23, 21, 20, 34, 35, 33, 32, 10, 11, 8, 9]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut11_isAut : IsAut nbhd aut11 := by decide

private def aut12 : Equiv.Perm Cell where
  toFun := ![11, 10, 8, 9, 23, 22, 20, 21, 35, 34, 32, 33, 7, 6, 4, 5, 19, 18, 16, 17, 31, 30, 28, 29, 3, 2, 0, 1, 15, 14, 12, 13, 27, 26, 24, 25]
  invFun := ![26, 27, 25, 24, 14, 15, 13, 12, 2, 3, 1, 0, 30, 31, 29, 28, 18, 19, 17, 16, 6, 7, 5, 4, 34, 35, 33, 32, 22, 23, 21, 20, 10, 11, 9, 8]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut12_isAut : IsAut nbhd aut12 := by decide

private def aut13 : Equiv.Perm Cell where
  toFun := ![12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 25, 24, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35]
  invFun := ![12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 25, 24, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut13_isAut : IsAut nbhd aut13 := by decide

private def aut14 : Equiv.Perm Cell where
  toFun := ![13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23, 25, 24, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  invFun := ![24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11, 13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut14_isAut : IsAut nbhd aut14 := by decide

private def aut15 : Equiv.Perm Cell where
  toFun := ![14, 15, 12, 13, 2, 3, 0, 1, 26, 27, 25, 24, 18, 19, 16, 17, 6, 7, 4, 5, 30, 31, 29, 28, 22, 23, 20, 21, 10, 11, 8, 9, 34, 35, 33, 32]
  invFun := ![6, 7, 4, 5, 18, 19, 16, 17, 30, 31, 28, 29, 2, 3, 0, 1, 14, 15, 12, 13, 26, 27, 24, 25, 11, 10, 8, 9, 23, 22, 20, 21, 35, 34, 32, 33]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut15_isAut : IsAut nbhd aut15 := by decide

private def aut16 : Equiv.Perm Cell where
  toFun := ![14, 15, 13, 12, 26, 27, 25, 24, 2, 3, 0, 1, 18, 19, 17, 16, 30, 31, 29, 28, 6, 7, 4, 5, 22, 23, 21, 20, 34, 35, 33, 32, 10, 11, 8, 9]
  invFun := ![10, 11, 8, 9, 22, 23, 20, 21, 34, 35, 32, 33, 3, 2, 0, 1, 15, 14, 12, 13, 27, 26, 24, 25, 7, 6, 4, 5, 19, 18, 16, 17, 31, 30, 28, 29]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut16_isAut : IsAut nbhd aut16 := by decide

private def aut17 : Equiv.Perm Cell where
  toFun := ![15, 14, 12, 13, 3, 2, 0, 1, 27, 26, 25, 24, 22, 23, 20, 21, 10, 11, 8, 9, 34, 35, 33, 32, 18, 19, 16, 17, 6, 7, 4, 5, 30, 31, 29, 28]
  invFun := ![6, 7, 5, 4, 30, 31, 28, 29, 18, 19, 16, 17, 2, 3, 1, 0, 26, 27, 24, 25, 14, 15, 12, 13, 11, 10, 9, 8, 35, 34, 32, 33, 23, 22, 20, 21]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut17_isAut : IsAut nbhd aut17 := by decide

private def aut18 : Equiv.Perm Cell where
  toFun := ![16, 17, 18, 19, 12, 13, 14, 15, 20, 21, 23, 22, 4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 11, 10, 29, 28, 30, 31, 25, 24, 26, 27, 33, 32, 35, 34]
  invFun := ![16, 17, 18, 19, 12, 13, 14, 15, 20, 21, 23, 22, 4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 11, 10, 29, 28, 30, 31, 25, 24, 26, 27, 33, 32, 35, 34]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut18_isAut : IsAut nbhd aut18 := by decide

private def aut19 : Equiv.Perm Cell where
  toFun := ![17, 16, 18, 19, 13, 12, 14, 15, 21, 20, 23, 22, 29, 28, 30, 31, 25, 24, 26, 27, 33, 32, 35, 34, 4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 11, 10]
  invFun := ![28, 29, 30, 31, 24, 25, 26, 27, 32, 33, 35, 34, 5, 4, 6, 7, 1, 0, 2, 3, 9, 8, 11, 10, 17, 16, 18, 19, 13, 12, 14, 15, 21, 20, 23, 22]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut19_isAut : IsAut nbhd aut19 := by decide

private def aut20 : Equiv.Perm Cell where
  toFun := ![18, 19, 16, 17, 6, 7, 4, 5, 30, 31, 29, 28, 14, 15, 12, 13, 2, 3, 0, 1, 26, 27, 25, 24, 23, 22, 20, 21, 11, 10, 8, 9, 35, 34, 33, 32]
  invFun := ![18, 19, 16, 17, 6, 7, 4, 5, 30, 31, 29, 28, 14, 15, 12, 13, 2, 3, 0, 1, 26, 27, 25, 24, 23, 22, 20, 21, 11, 10, 8, 9, 35, 34, 33, 32]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut20_isAut : IsAut nbhd aut20 := by decide

private def aut21 : Equiv.Perm Cell where
  toFun := ![19, 18, 16, 17, 7, 6, 4, 5, 31, 30, 29, 28, 23, 22, 20, 21, 11, 10, 8, 9, 35, 34, 33, 32, 14, 15, 12, 13, 2, 3, 0, 1, 26, 27, 25, 24]
  invFun := ![30, 31, 28, 29, 6, 7, 5, 4, 18, 19, 17, 16, 26, 27, 24, 25, 2, 3, 1, 0, 14, 15, 13, 12, 35, 34, 32, 33, 11, 10, 9, 8, 23, 22, 21, 20]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut21_isAut : IsAut nbhd aut21 := by decide

private def aut22 : Equiv.Perm Cell where
  toFun := ![20, 21, 22, 23, 12, 13, 15, 14, 16, 17, 19, 18, 8, 9, 10, 11, 0, 1, 3, 2, 4, 5, 7, 6, 33, 32, 34, 35, 25, 24, 27, 26, 29, 28, 31, 30]
  invFun := ![16, 17, 19, 18, 20, 21, 23, 22, 12, 13, 14, 15, 4, 5, 7, 6, 8, 9, 11, 10, 0, 1, 2, 3, 29, 28, 31, 30, 33, 32, 35, 34, 25, 24, 26, 27]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut22_isAut : IsAut nbhd aut22 := by decide

private def aut23 : Equiv.Perm Cell where
  toFun := ![21, 20, 22, 23, 13, 12, 15, 14, 17, 16, 19, 18, 33, 32, 34, 35, 25, 24, 27, 26, 29, 28, 31, 30, 8, 9, 10, 11, 0, 1, 3, 2, 4, 5, 7, 6]
  invFun := ![28, 29, 31, 30, 32, 33, 35, 34, 24, 25, 26, 27, 5, 4, 7, 6, 9, 8, 11, 10, 1, 0, 2, 3, 17, 16, 19, 18, 21, 20, 23, 22, 13, 12, 14, 15]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut23_isAut : IsAut nbhd aut23 := by decide

private def aut24 : Equiv.Perm Cell where
  toFun := ![22, 23, 20, 21, 10, 11, 8, 9, 34, 35, 33, 32, 15, 14, 12, 13, 3, 2, 0, 1, 27, 26, 25, 24, 19, 18, 16, 17, 7, 6, 4, 5, 31, 30, 29, 28]
  invFun := ![18, 19, 17, 16, 30, 31, 29, 28, 6, 7, 4, 5, 14, 15, 13, 12, 26, 27, 25, 24, 2, 3, 0, 1, 23, 22, 21, 20, 35, 34, 33, 32, 11, 10, 8, 9]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut24_isAut : IsAut nbhd aut24 := by decide

private def aut25 : Equiv.Perm Cell where
  toFun := ![23, 22, 20, 21, 11, 10, 8, 9, 35, 34, 33, 32, 19, 18, 16, 17, 7, 6, 4, 5, 31, 30, 29, 28, 15, 14, 12, 13, 3, 2, 0, 1, 27, 26, 25, 24]
  invFun := ![30, 31, 29, 28, 18, 19, 17, 16, 6, 7, 5, 4, 26, 27, 25, 24, 14, 15, 13, 12, 2, 3, 1, 0, 35, 34, 33, 32, 23, 22, 21, 20, 11, 10, 9, 8]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut25_isAut : IsAut nbhd aut25 := by decide

private def aut26 : Equiv.Perm Cell where
  toFun := ![24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11, 13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23]
  invFun := ![13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23, 25, 24, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut26_isAut : IsAut nbhd aut26 := by decide

private def aut27 : Equiv.Perm Cell where
  toFun := ![25, 24, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35, 13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23, 1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11]
  invFun := ![25, 24, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35, 13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23, 1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut27_isAut : IsAut nbhd aut27 := by decide

private def aut28 : Equiv.Perm Cell where
  toFun := ![26, 27, 24, 25, 2, 3, 1, 0, 14, 15, 13, 12, 30, 31, 28, 29, 6, 7, 5, 4, 18, 19, 17, 16, 34, 35, 32, 33, 10, 11, 9, 8, 22, 23, 21, 20]
  invFun := ![7, 6, 4, 5, 19, 18, 16, 17, 31, 30, 28, 29, 11, 10, 8, 9, 23, 22, 20, 21, 35, 34, 32, 33, 2, 3, 0, 1, 14, 15, 12, 13, 26, 27, 24, 25]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut28_isAut : IsAut nbhd aut28 := by decide

private def aut29 : Equiv.Perm Cell where
  toFun := ![27, 26, 24, 25, 3, 2, 1, 0, 15, 14, 13, 12, 34, 35, 32, 33, 10, 11, 9, 8, 22, 23, 21, 20, 30, 31, 28, 29, 6, 7, 5, 4, 18, 19, 17, 16]
  invFun := ![7, 6, 5, 4, 31, 30, 28, 29, 19, 18, 16, 17, 11, 10, 9, 8, 35, 34, 32, 33, 23, 22, 20, 21, 2, 3, 1, 0, 26, 27, 24, 25, 14, 15, 12, 13]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut29_isAut : IsAut nbhd aut29 := by decide

private def aut30 : Equiv.Perm Cell where
  toFun := ![28, 29, 30, 31, 24, 25, 26, 27, 32, 33, 35, 34, 5, 4, 6, 7, 1, 0, 2, 3, 9, 8, 11, 10, 17, 16, 18, 19, 13, 12, 14, 15, 21, 20, 23, 22]
  invFun := ![17, 16, 18, 19, 13, 12, 14, 15, 21, 20, 23, 22, 29, 28, 30, 31, 25, 24, 26, 27, 33, 32, 35, 34, 4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 11, 10]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut30_isAut : IsAut nbhd aut30 := by decide

private def aut31 : Equiv.Perm Cell where
  toFun := ![29, 28, 30, 31, 25, 24, 26, 27, 33, 32, 35, 34, 17, 16, 18, 19, 13, 12, 14, 15, 21, 20, 23, 22, 5, 4, 6, 7, 1, 0, 2, 3, 9, 8, 11, 10]
  invFun := ![29, 28, 30, 31, 25, 24, 26, 27, 33, 32, 35, 34, 17, 16, 18, 19, 13, 12, 14, 15, 21, 20, 23, 22, 5, 4, 6, 7, 1, 0, 2, 3, 9, 8, 11, 10]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut31_isAut : IsAut nbhd aut31 := by decide

private def aut32 : Equiv.Perm Cell where
  toFun := ![30, 31, 28, 29, 6, 7, 5, 4, 18, 19, 17, 16, 26, 27, 24, 25, 2, 3, 1, 0, 14, 15, 13, 12, 35, 34, 32, 33, 11, 10, 9, 8, 23, 22, 21, 20]
  invFun := ![19, 18, 16, 17, 7, 6, 4, 5, 31, 30, 29, 28, 23, 22, 20, 21, 11, 10, 8, 9, 35, 34, 33, 32, 14, 15, 12, 13, 2, 3, 0, 1, 26, 27, 25, 24]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut32_isAut : IsAut nbhd aut32 := by decide

private def aut33 : Equiv.Perm Cell where
  toFun := ![31, 30, 28, 29, 7, 6, 5, 4, 19, 18, 17, 16, 35, 34, 32, 33, 11, 10, 9, 8, 23, 22, 21, 20, 26, 27, 24, 25, 2, 3, 1, 0, 14, 15, 13, 12]
  invFun := ![31, 30, 28, 29, 7, 6, 5, 4, 19, 18, 17, 16, 35, 34, 32, 33, 11, 10, 9, 8, 23, 22, 21, 20, 26, 27, 24, 25, 2, 3, 1, 0, 14, 15, 13, 12]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut33_isAut : IsAut nbhd aut33 := by decide

private def aut34 : Equiv.Perm Cell where
  toFun := ![32, 33, 34, 35, 24, 25, 27, 26, 28, 29, 31, 30, 9, 8, 10, 11, 1, 0, 3, 2, 5, 4, 7, 6, 21, 20, 22, 23, 13, 12, 15, 14, 17, 16, 19, 18]
  invFun := ![17, 16, 19, 18, 21, 20, 23, 22, 13, 12, 14, 15, 29, 28, 31, 30, 33, 32, 35, 34, 25, 24, 26, 27, 4, 5, 7, 6, 8, 9, 11, 10, 0, 1, 2, 3]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut34_isAut : IsAut nbhd aut34 := by decide

private def aut35 : Equiv.Perm Cell where
  toFun := ![33, 32, 34, 35, 25, 24, 27, 26, 29, 28, 31, 30, 21, 20, 22, 23, 13, 12, 15, 14, 17, 16, 19, 18, 9, 8, 10, 11, 1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![29, 28, 31, 30, 33, 32, 35, 34, 25, 24, 26, 27, 17, 16, 19, 18, 21, 20, 23, 22, 13, 12, 14, 15, 5, 4, 7, 6, 9, 8, 11, 10, 1, 0, 2, 3]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut35_isAut : IsAut nbhd aut35 := by decide

private def aut36 : Equiv.Perm Cell where
  toFun := ![34, 35, 32, 33, 10, 11, 9, 8, 22, 23, 21, 20, 27, 26, 24, 25, 3, 2, 1, 0, 15, 14, 13, 12, 31, 30, 28, 29, 7, 6, 5, 4, 19, 18, 17, 16]
  invFun := ![19, 18, 17, 16, 31, 30, 29, 28, 7, 6, 4, 5, 23, 22, 21, 20, 35, 34, 33, 32, 11, 10, 8, 9, 14, 15, 13, 12, 26, 27, 25, 24, 2, 3, 0, 1]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut36_isAut : IsAut nbhd aut36 := by decide

private def aut37 : Equiv.Perm Cell where
  toFun := ![35, 34, 32, 33, 11, 10, 9, 8, 23, 22, 21, 20, 31, 30, 28, 29, 7, 6, 5, 4, 19, 18, 17, 16, 27, 26, 24, 25, 3, 2, 1, 0, 15, 14, 13, 12]
  invFun := ![31, 30, 29, 28, 19, 18, 17, 16, 7, 6, 5, 4, 35, 34, 33, 32, 23, 22, 21, 20, 11, 10, 9, 8, 26, 27, 25, 24, 14, 15, 13, 12, 2, 3, 1, 0]
  left_inv := by intro v; revert v; decide
  right_inv := by intro v; revert v; decide
private theorem aut37_isAut : IsAut nbhd aut37 := by decide

private def vertexAut : Cell → Equiv.Perm Cell := ![
  aut0, aut1, aut2, aut3, aut4, aut6, aut7, aut8, aut9, aut10, aut11, aut12, aut13, aut14, aut15, aut17, aut18, aut19, aut20, aut21, aut22, aut23, aut24, aut25, aut26, aut27, aut28, aut29, aut30, aut31, aut32, aut33, aut34, aut35, aut36, aut37]

private theorem vertexAut_isAut (v : Cell) : IsAut nbhd (vertexAut v) := by
  fin_cases v
  · exact aut0_isAut
  · exact aut1_isAut
  · exact aut2_isAut
  · exact aut3_isAut
  · exact aut4_isAut
  · exact aut6_isAut
  · exact aut7_isAut
  · exact aut8_isAut
  · exact aut9_isAut
  · exact aut10_isAut
  · exact aut11_isAut
  · exact aut12_isAut
  · exact aut13_isAut
  · exact aut14_isAut
  · exact aut15_isAut
  · exact aut17_isAut
  · exact aut18_isAut
  · exact aut19_isAut
  · exact aut20_isAut
  · exact aut21_isAut
  · exact aut22_isAut
  · exact aut23_isAut
  · exact aut24_isAut
  · exact aut25_isAut
  · exact aut26_isAut
  · exact aut27_isAut
  · exact aut28_isAut
  · exact aut29_isAut
  · exact aut30_isAut
  · exact aut31_isAut
  · exact aut32_isAut
  · exact aut33_isAut
  · exact aut34_isAut
  · exact aut35_isAut
  · exact aut36_isAut
  · exact aut37_isAut

private theorem vertexAut_zero : ∀ v, vertexAut v 0 = v := by decide


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
    30 * h univ ≤ 19 * ∑ v, h {v} + 11 * ∑ v, increment h (nbhd v) v := by
  let s := h ({0} : Finset Cell)
  let e := increment h (nbhd 0) 0
  have hs : ∀ v, h {v} = s := singleton_uniform hi
  have he : ∀ v, increment h (nbhd v) v = e := error_uniform hi

  have o0 : h {2} = h {0} := by
    have hx := hi aut2 aut2_isAut {2}
    rw [show ({2} : Finset Cell).map aut2.toEmbedding = {0} by decide] at hx
    exact hx.symm

  have o1 : h {0, 2, 3} = h {0, 1, 2} := by
    have hx := hi aut2 aut2_isAut {0, 2, 3}
    rw [show ({0, 2, 3} : Finset Cell).map aut2.toEmbedding = {0, 1, 2} by decide] at hx
    exact hx.symm

  have o2 : h {1, 2, 3} = h {0, 1, 2} := by
    have hx := hi aut3 aut3_isAut {1, 2, 3}
    rw [show ({1, 2, 3} : Finset Cell).map aut3.toEmbedding = {0, 1, 2} by decide] at hx
    exact hx.symm

  have o3 : h {0, 4, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 29, 33} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 20, 24, 28, 32} := by
    have hx := hi aut13 aut13_isAut {0, 4, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 29, 33}
    rw [show ({0, 4, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 29, 33} : Finset Cell).map aut13.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 20, 24, 28, 32} by decide] at hx
    exact hx.symm

  have o4 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29, 32, 33} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 28, 29, 32, 33} := by
    have hx := hi aut13 aut13_isAut {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29, 32, 33}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29, 32, 33} : Finset Cell).map aut13.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 28, 29, 32, 33} by decide] at hx
    exact hx.symm

  have o5 : h {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 20, 22, 26, 27, 28, 30, 32, 34} = h {0, 1, 2, 3, 5, 6, 9, 10, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 28, 29, 32, 33} := by
    have hx := hi aut28 aut28_isAut {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 20, 22, 26, 27, 28, 30, 32, 34}
    rw [show ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 20, 22, 26, 27, 28, 30, 32, 34} : Finset Cell).map aut28.toEmbedding = {0, 1, 2, 3, 5, 6, 9, 10, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 28, 29, 32, 33} by decide] at hx
    exact hx.symm

  have o6 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34} := by
    have hx := hi aut2 aut2_isAut {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} : Finset Cell).map aut2.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34} by decide] at hx
    exact hx.symm

  have o7 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} := by
    have hx := hi aut13 aut13_isAut {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} : Finset Cell).map aut13.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} by decide] at hx
    exact hx.symm

  have o8 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 23, 24, 26, 28, 29, 30, 31, 32, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} := by
    have hx := hi aut4 aut4_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 23, 24, 26, 28, 29, 30, 31, 32, 35}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 23, 24, 26, 28, 29, 30, 31, 32, 35} : Finset Cell).map aut4.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} by decide] at hx
    exact hx.symm

  have o9 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 34} := by
    have hx := hi aut4 aut4_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 35}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 35} : Finset Cell).map aut4.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 34} by decide] at hx
    exact hx.symm

  have o10 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} := by
    have hx := hi aut4 aut4_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} : Finset Cell).map aut4.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} by decide] at hx
    exact hx.symm

  have o11 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} := by
    have hx := hi aut4 aut4_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} : Finset Cell).map aut4.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} by decide] at hx
    exact hx.symm

  have o12 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 19, 20, 21, 22, 23, 24, 27, 28, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} := by
    have hx := hi aut5 aut5_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 19, 20, 21, 22, 23, 24, 27, 28, 31, 32, 33, 34, 35}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 19, 20, 21, 22, 23, 24, 27, 28, 31, 32, 33, 34, 35} : Finset Cell).map aut5.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} by decide] at hx
    exact hx.symm

  have o13 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} := by
    have hx := hi aut16 aut16_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35} : Finset Cell).map aut16.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} by decide] at hx
    exact hx.symm

  have o14 : h {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 32, 33} := by
    have hx := hi aut36 aut36_isAut {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}
    rw [show ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} : Finset Cell).map aut36.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 32, 33} by decide] at hx
    exact hx.symm

  have o15 : h {0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} := by
    have hx := hi aut32 aut32_isAut {0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}
    rw [show ({0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} : Finset Cell).map aut32.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} by decide] at hx
    exact hx.symm

  have o16 : h {1, 2, 3, 5, 6, 9, 10, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34} := by
    have hx := hi aut14 aut14_isAut {1, 2, 3, 5, 6, 9, 10, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}
    rw [show ({1, 2, 3, 5, 6, 9, 10, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} : Finset Cell).map aut14.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34} by decide] at hx
    exact hx.symm

  have o17 : h {0, 1, 2, 3, 5, 6, 9, 10, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} := by
    have hx := hi aut8 aut8_isAut {0, 1, 2, 3, 5, 6, 9, 10, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}
    rw [show ({0, 1, 2, 3, 5, 6, 9, 10, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} : Finset Cell).map aut8.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} by decide] at hx
    exact hx.symm

  have o18 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} := by
    have hx := hi aut14 aut14_isAut {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} : Finset Cell).map aut14.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} by decide] at hx
    exact hx.symm

  have o19 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} := by
    have hx := hi aut1 aut1_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} : Finset Cell).map aut1.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} by decide] at hx
    exact hx.symm

  have o20 : h {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 34} := by
    have hx := hi aut23 aut23_isAut {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}
    rw [show ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} : Finset Cell).map aut23.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 34} by decide] at hx
    exact hx.symm

  have o21 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} = h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} := by
    have hx := hi aut6 aut6_isAut {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}
    rw [show ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} : Finset Cell).map aut6.toEmbedding = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} by decide] at hx
    exact hx.symm

  have e0 : -h ∅ ≤ 0 := by rw [hh.empty]; norm_num

  have cl1 : h {0, 1, 2, 3} ≤ h {0, 1, 2, 3} + 0 * e := by
    simp

  have raw1 : h {0, 1, 2, 3} + h ∅ ≤ h {0} + h {1, 2, 3} :=
    hh.elemental (by decide) (by decide)
  have e1 : h {0, 1, 2, 3} + h ∅ ≤ h {0} + h {1, 2, 3} + 0 * e := by
    linarith only [raw1, cl1]

  have cl2_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 1 * e := by
    simpa only [Nat.cast_one] using (recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}) (D := {12}) (n := 1) (by decide) (by decide) (by decide))

  have cl2 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 1 * e := by
    linarith only [cl2_0]

  have raw2 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + h ∅ ≤ h {0} + h {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} :=
    hh.elemental (by decide) (by decide)
  have e2 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + h ∅ ≤ h {0} + h {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 1 * e := by
    linarith only [raw2, cl2]

  have cl3 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} ≤ h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 0 * e := by
    simp

  have raw3 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + h ∅ ≤ h {0, 4, 8, 12, 16, 20} + h {1, 2, 3, 5, 6, 9, 10, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} :=
    hh.elemental (by decide) (by decide)
  have e3 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + h ∅ ≤ h {0, 4, 8, 12, 16, 20} + h {1, 2, 3, 5, 6, 9, 10, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 0 * e := by
    linarith only [raw3, cl3]

  have cl4_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 20, 22, 26, 27, 28, 30, 32, 34} + 2 * e := by
    exact recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 20, 22, 26, 27, 28, 30, 32, 34}) (D := {12, 24}) (n := 2) (by decide) (by decide) (by decide)

  have cl4 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 20, 22, 26, 27, 28, 30, 32, 34} + 2 * e := by
    linarith only [cl4_0]

  have raw4 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 20, 22, 26, 27, 28, 30, 32, 34} + h {2} ≤ h {0, 1, 2} + h {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 20, 22, 26, 27, 28, 30, 32, 34} :=
    hh.elemental (by decide) (by decide)
  have e4 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34} + h {2} ≤ h {0, 1, 2} + h {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 20, 22, 26, 27, 28, 30, 32, 34} + 2 * e := by
    linarith only [raw4, cl4]

  have cl5_0 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 2 * e := by
    exact recover_paid hh he (A := univ) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}) (D := {12, 24}) (n := 2) (by decide) (by decide) (by decide)

  have cl5 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 2 * e := by
    linarith only [cl5_0]

  have raw5 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + h {2} ≤ h {0, 1, 2} + h {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} :=
    hh.elemental (by decide) (by decide)
  have e5 : h univ + h {2} ≤ h {0, 1, 2} + h {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 2 * e := by
    linarith only [raw5, cl5]

  have buy6 : h {0, 1, 2} ≤ h ∅ + 3 * s := by
    exact purchase hh hs (A := {0, 1, 2}) (B := ∅) (D := {0, 1, 2}) (n := 3) (by decide) (by decide)

  have cl6 : h {0, 1, 2} ≤ h {0, 1, 2} + 0 * e := by
    simp

  have e6 : h {0, 1, 2} ≤ 3 * s + 0 * e := by
    linarith only [buy6, cl6, hh.empty]

  have cl7_0 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 1 * e := by
    simpa only [Nat.cast_one] using (recover_paid hh he (A := univ) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35}) (D := {24}) (n := 1) (by decide) (by decide) (by decide))

  have cl7 : h univ ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 1 * e := by
    linarith only [cl7_0]

  have raw7 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + h {0, 2, 3} ≤ h {0, 1, 2, 3} + h {0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} :=
    hh.elemental (by decide) (by decide)
  have e7 : h univ + h {0, 2, 3} ≤ h {0, 1, 2, 3} + h {0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 1 * e := by
    linarith only [raw7, cl7]

  have cl8 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29, 32, 33} ≤ h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29, 32, 33} + 0 * e := by
    simp

  have raw8 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29, 32, 33} + h {0, 4, 8, 12, 16, 20} ≤ h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 20, 24, 28, 32} + h {0, 4, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 29, 33} :=
    hh.elemental (by decide) (by decide)
  have e8 : h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29, 32, 33} + h {0, 4, 8, 12, 16, 20} ≤ h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 20, 24, 28, 32} + h {0, 4, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 29, 33} + 0 * e := by
    linarith only [raw8, cl8]

  have cl9 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + 0 * e := by
    simp

  have raw9 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 20, 24, 28, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 20, 24, 28, 32} + h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} :=
    hh.elemental (by decide) (by decide)
  have e9 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 20, 24, 28, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 20, 24, 28, 32} + h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + 0 * e := by
    linarith only [raw9, cl9]

  have cl10 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35} + 0 * e := by
    simp

  have raw10 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 20, 24, 28, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 26, 28, 30, 32} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 19, 20, 21, 22, 23, 24, 27, 28, 31, 32, 33, 34, 35} :=
    hh.elemental (by decide) (by decide)
  have e10 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 20, 24, 28, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 26, 28, 30, 32} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 19, 20, 21, 22, 23, 24, 27, 28, 31, 32, 33, 34, 35} + 0 * e := by
    linarith only [raw10, cl10]

  have cl11 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 35} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 35} + 0 * e := by
    simp

  have raw11 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 35} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 26, 28, 30, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 28, 30, 32} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 23, 24, 26, 28, 29, 30, 31, 32, 35} :=
    hh.elemental (by decide) (by decide)
  have e11 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 35} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 26, 28, 30, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 28, 30, 32} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 23, 24, 26, 28, 29, 30, 31, 32, 35} + 0 * e := by
    linarith only [raw11, cl11]

  have cl12 : h univ ≤ h univ + 0 * e := by
    simp

  have raw12 : h univ + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 26, 28, 30, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} :=
    hh.elemental (by decide) (by decide)
  have e12 : h univ + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 26, 28, 30, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 27, 28, 30, 32, 34} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} + 0 * e := by
    linarith only [raw12, cl12]

  have cl13 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 0 * e := by
    simp

  have raw13 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + h {0, 1, 2, 3, 5, 6, 9, 10, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 28, 29, 32, 33} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 28, 29, 32, 33} + h {0, 1, 2, 3, 5, 6, 9, 10, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} :=
    hh.elemental (by decide) (by decide)
  have e13 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + h {0, 1, 2, 3, 5, 6, 9, 10, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 28, 29, 32, 33} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 28, 29, 32, 33} + h {0, 1, 2, 3, 5, 6, 9, 10, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35} + 0 * e := by
    linarith only [raw13, cl13]

  have cl14 : h univ ≤ h univ + 0 * e := by
    simp

  have raw14 : h univ + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 28, 30, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} :=
    hh.elemental (by decide) (by decide)
  have e14 : h univ + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 28, 30, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} + 0 * e := by
    linarith only [raw14, cl14]

  have cl15 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + 0 * e := by
    simp

  have raw15 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} + h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} :=
    hh.elemental (by decide) (by decide)
  have e15 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} + h {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + 0 * e := by
    linarith only [raw15, cl15]

  have buy16 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 25, 26, 27} ≤ h ∅ + 18 * s := by
    exact purchase hh hs (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 25, 26, 27}) (B := ∅) (D := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 25, 26, 27}) (n := 18) (by decide) (by decide)

  have cl16_0 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 24, 25, 26, 27, 28, 32} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 25, 26, 27} + 6 * e := by
    exact recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 24, 25, 26, 27, 28, 32}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 25, 26, 27}) (D := {12, 16, 20, 24, 28, 32}) (n := 6) (by decide) (by decide) (by decide)

  have cl16_1 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 24, 25, 26, 27, 28, 32} + 4 * e := by
    exact recover_paid hh he (A := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34}) (B := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 24, 25, 26, 27, 28, 32}) (D := {18, 22, 30, 34}) (n := 4) (by decide) (by decide) (by decide)

  have cl16 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 25, 26, 27} + 10 * e := by
    linarith only [cl16_0, cl16_1]

  have e16 : h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34} ≤ 18 * s + 10 * e := by
    linarith only [buy16, cl16, hh.empty]

  have cl17 : h univ ≤ h univ + 0 * e := by
    simp

  have raw17 : h univ + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 32, 33} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} :=
    hh.elemental (by decide) (by decide)
  have e17 : h univ + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 32, 33} ≤ h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34} + h {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 35} + 0 * e := by
    linarith only [raw17, cl17]

  simp only [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17

  have certificate : 5 * h univ ≤ 114 * s + 66 * e := by
    linear_combination 3 * e0 +
      1 * e1 +
      1 * e2 +
      1 * e3 +
      1 * e4 +
      1 * e5 +
      2 * e6 +
      1 * e7 +
      1 * e8 +
      1 * e9 +
      2 * e10 +
      1 * e11 +
      1 * e12 +
      1 * e13 +
      1 * e14 +
      1 * e15 +
      6 * e16 +
      1 * e17


  have hs_sum : (∑ v, h {v}) = 36 * s := by simp_rw [hs]; simp
  have he_sum : (∑ v, increment h (nbhd v) v) = 36 * e := by simp_rw [he]; simp
  rw [hs_sum, he_sum]
  linarith only [certificate]


/-- The paid inequality for the actual 36-coordinate residual helper graph. -/
theorem paid_grid (h : Finset Cell → ℝ) (hh : IsPolymatroid h) :
    30 * h univ ≤ 19 * ∑ v, h {v} + 11 * ∑ v, increment h (nbhd v) v := by
  have hp := paid_invariant (symmetrize nbhd h) (hh.symmetrize nbhd)
    (fun σ hσ S => symmetrize_invariant nbhd h hσ S)
  rwa [symmetrize_univ, sum_symmetrize_singleton, sum_symmetrize_error] at hp

/-- Exact recovery gives the weighted 19/30 bound without singleton caps. -/
theorem rateBound_grid : RateBound nbhd (19 / 30) := by
  intro h hh hv
  have hp := paid_grid h hh
  have he : (∑ v, increment h (nbhd v) v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp only [increment, hv v, sub_self]
  rw [he] at hp
  linarith

/-- Unit scalar capacities give the residual upper bound 114/5. -/
theorem residual_le (h : Finset Cell → ℝ) (hh : IsPolymatroid h)
    (hv : IsValid h nbhd) (hc : ∀ v, h {v} ≤ 1) : h univ ≤ 114 / 5 := by
  have hp := rateBound_grid h hh hv
  have hs : (∑ v, h {v}) ≤ 36 := by
    calc
      _ ≤ ∑ _ : Cell, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hc v)
      _ = 36 := by norm_num
  linarith

end LeanBacklog.GridCertificate

#print axioms LeanBacklog.GridCertificate.paid_grid
#print axioms LeanBacklog.GridCertificate.rateBound_grid
#print axioms LeanBacklog.GridCertificate.residual_le
#print axioms LeanBacklog.GridCertificate.loopless
#print axioms LeanBacklog.GridCertificate.mutual_triangle_free
