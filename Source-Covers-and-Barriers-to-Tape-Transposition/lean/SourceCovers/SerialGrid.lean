import SourceCovers.SerialParameters
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Rev

set_option autoImplicit false

/-! The older continuation grid and its sparse excursion. Sorting is used
only to prescribe a fixed geometry, with no algorithmic cost claim. -/

namespace SourceCovers.SerialGeometry.Parameters

open Finset BoundedNesting LeanMachine.ScheduledExcursion
noncomputable section

variable (P : Parameters)

abbrev GridIndex := Fin (P.m - 1) × Fin (P.m - 1)

def olderOffset (i : P.GridIndex) : ℕ :=
  if (i.2.val + 1) % 2 = 0 then P.m - 1 - i.1.val
  else P.width - (P.m - 1 - i.1.val)

def olderWindow (i : P.GridIndex) : ℕ := P.bankCount - (i.2.val + 1)

def olderTime (i : P.GridIndex) : ℕ :=
  4 * P.length + P.olderWindow i * P.width + P.olderOffset i

theorem olderOffset_bounds (i : P.GridIndex) :
    0 < P.olderOffset i ∧ P.olderOffset i < P.width := by
  have hi := i.1.isLt
  have hw := P.m_lt_width
  dsimp [olderOffset]
  split <;> omega

theorem olderWindow_add (i : P.GridIndex) :
    P.olderWindow i + (i.2.val + 1) = P.bankCount := by
  have hi := i.2.isLt
  have hm := P.hm
  dsimp [olderWindow, bankCount]
  omega

theorem olderTime_window (i : P.GridIndex) :
    4 * P.length + P.olderWindow i * P.width < P.olderTime i ∧
      P.olderTime i < 4 * P.length + (P.olderWindow i + 1) * P.width := by
  have h := P.olderOffset_bounds i
  dsimp only [olderTime]
  constructor <;> nlinarith

theorem olderTime_bounds (i : P.GridIndex) :
    4 * P.length < P.olderTime i ∧ P.olderTime i < 5 * P.length := by
  have h := P.olderTime_window i
  have hw := P.olderWindow_add i
  have hm := Nat.mul_le_mul_right P.width
    (show P.olderWindow i + 1 ≤ P.bankCount by omega)
  change (P.olderWindow i + 1) * P.width ≤ P.length at hm
  constructor <;> nlinarith

theorem olderTime_injective : Function.Injective P.olderTime := by
  intro i j he
  have hi := P.olderTime_window i
  have hj := P.olderTime_window j
  have hwin : P.olderWindow i = P.olderWindow j := by
    apply Nat.le_antisymm
    · by_contra! hh
      have hmul := Nat.mul_le_mul_right P.width (Nat.succ_le_of_lt hh)
      nlinarith
    · by_contra! hh
      have hmul := Nat.mul_le_mul_right P.width (Nat.succ_le_of_lt hh)
      nlinarith
  have hia := P.olderWindow_add i
  have hja := P.olderWindow_add j
  have hsecond : i.2 = j.2 := Fin.ext (by omega)
  have hoff : P.olderOffset i = P.olderOffset j := by
    dsimp only [olderTime] at he
    rw [hwin] at he
    omega
  have hfirst : i.1 = j.1 := by
    apply Fin.ext
    have hi' := i.1.isLt
    have hj' := j.1.isLt
    have hw := P.m_lt_width
    simp only [olderOffset, hsecond] at hoff
    split at hoff <;> omega
  exact Prod.ext hfirst hsecond

def olderGrid : Finset ℕ := univ.image P.olderTime

theorem olderGrid_card : P.olderGrid.card = P.targets := by
  rw [olderGrid, card_image_of_injective _ P.olderTime_injective]
  simp [targets, pow_two]

theorem olderGrid_bounds {t : ℕ} (ht : t ∈ P.olderGrid) :
    4 * P.length < t ∧ t < 5 * P.length := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp ht
  exact P.olderTime_bounds i

/-- Last outward visits spaced by the floor grid. -/
def sparseDeparture (i : Fin P.targets) : ℕ := 2 * P.length + i.val * P.length / P.targets

theorem sparseDeparture_strictMono : StrictMono P.sparseDeparture := by
  intro i j hij
  have hi := Nat.div_mul_le_self (i.val * P.length) P.targets
  have hmul := Nat.mul_le_mul_right P.length (show i.val + 1 ≤ j.val from hij)
  have hL := P.targets_lt_length
  have hdiv : i.val * P.length / P.targets + 1 ≤ j.val * P.length / P.targets :=
    (Nat.le_div_iff_mul_le P.targets_pos).mpr (by nlinarith)
  dsimp only [sparseDeparture]
  omega

theorem sparseDeparture_bounds (i : Fin P.targets) :
    2 * P.length ≤ P.sparseDeparture i ∧ P.sparseDeparture i + 1 < 3 * P.length := by
  have hi := Nat.div_mul_le_self (i.val * P.length) P.targets
  have hmul := Nat.mul_le_mul_right P.length (show i.val + 1 ≤ P.targets from i.isLt)
  have hL := P.targets_lt_length
  have hQ := P.targets_pos
  have hdiv : i.val * P.length / P.targets + 1 < P.length := by nlinarith
  dsimp only [sparseDeparture]
  refine ⟨Nat.le_add_right _ _, ?_⟩
  calc
    2 * P.length + i.val * P.length / P.targets + 1 =
        2 * P.length + (i.val * P.length / P.targets + 1) := Nat.add_assoc _ _ _
    _ < 2 * P.length + P.length := Nat.add_lt_add_left hdiv _
    _ = 3 * P.length := by omega

@[simp] theorem sparseDeparture_zero : P.sparseDeparture 0 = 2 * P.length := by
  simp [sparseDeparture]

/-- Descending enumeration of all older continuation times. -/
def sparseArrival (i : Fin P.targets) : ℕ :=
  P.olderGrid.orderEmbOfFin P.olderGrid_card i.rev

theorem sparseArrival_mem (i : Fin P.targets) : P.sparseArrival i ∈ P.olderGrid :=
  orderEmbOfFin_mem _ _ _

theorem sparseArrival_strictAnti : StrictAnti P.sparseArrival := by
  intro i j hij
  exact (P.olderGrid.orderEmbOfFin P.olderGrid_card).strictMono (Fin.rev_lt_rev.mpr hij)

theorem sparseArrival_bounds (i : Fin P.targets) :
    4 * P.length < P.sparseArrival i ∧ P.sparseArrival i < 5 * P.length :=
  P.olderGrid_bounds (P.sparseArrival_mem i)

theorem sparseArrival_image : univ.image P.sparseArrival = P.olderGrid := by
  unfold sparseArrival
  calc
    _ = (univ.image Fin.rev).image (P.olderGrid.orderEmbOfFin P.olderGrid_card) :=
      (image_image ..).symm
    _ = univ.image (P.olderGrid.orderEmbOfFin P.olderGrid_card) := by
      rw [Finset.image_univ_of_surjective Fin.rev_surjective]
    _ = P.olderGrid := image_orderEmbOfFin_univ _ _

def older : Schedule P.targets where
  depart := P.sparseDeparture
  arrive := P.sparseArrival
  depart_strictMono := P.sparseDeparture_strictMono
  arrive_strictAnti := P.sparseArrival_strictAnti
  separated := by
    intro i j
    have := (P.sparseDeparture_bounds i).2
    have := (P.sparseArrival_bounds j).1
    omega

theorem older_before_horizon (i : Fin P.targets) : P.older.arrive i < P.horizon := by
  have := (P.sparseArrival_bounds i).2
  change P.sparseArrival i < P.horizon
  dsimp only [horizon]
  omega

theorem older_hops (p u : ℕ) :
    IsHop (NativeExcursion.walk P.older) P.horizon p u ↔
      ∃ i : Fin P.targets, p = P.sparseDeparture i ∧ u = P.sparseArrival i := by
  rw [NativeExcursion.hop_iff]
  constructor
  · exact fun h => h.2
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨P.older_before_horizon i, i, rfl, rfl⟩

theorem older_legal :
    IsWalk (NativeExcursion.walk P.older) ∧ NativeExcursion.walk P.older 0 = 0 ∧
      ∀ c T, (entries (NativeExcursion.walk P.older) c T).card ≤ 2 :=
  ⟨NativeExcursion.isWalk _, NativeExcursion.walk_zero _,
    fun c T => NativeExcursion.entries_card_le_two _ c T⟩

end
end SourceCovers.SerialGeometry.Parameters
