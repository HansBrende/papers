import SourceCovers.NativeExcursion

set_option autoImplicit false

/-! Parameters, input/output chronology and the two plateau heads in the
serial-exception construction. This is infrastructure for Proposition 6.1;
it does not yet assert the eight-head construction or its cover bound. -/

namespace SourceCovers.SerialGeometry

open BoundedNesting LeanMachine.ScheduledExcursion

structure Parameters where
  m : ℕ
  b : ℕ
  hm : 4 ≤ m
  hb : 1 ≤ b

namespace Parameters

variable (P : Parameters)

def bankCount : ℕ := 8 * P.m
def width : ℕ := 4 * P.bankCount * P.b
def length : ℕ := P.bankCount * P.width
def dimension : ℕ := 2 * P.bankCount
def horizon : ℕ := 12 * P.length + P.width + 1
def targets : ℕ := (P.m - 1) ^ 2

theorem bankCount_ge : 32 ≤ P.bankCount := by have := P.hm; dsimp [bankCount]; omega
theorem bankCount_pos : 0 < P.bankCount := lt_of_lt_of_le (by norm_num) P.bankCount_ge
theorem width_pos : 0 < P.width :=
  Nat.mul_pos (Nat.mul_pos (by norm_num) P.bankCount_pos) P.hb
theorem length_pos : 0 < P.length := Nat.mul_pos P.bankCount_pos P.width_pos

theorem width_eq : P.width = 32 * P.m * P.b := by unfold width bankCount; ring

theorem width_ge : 32 * P.m ≤ P.width := by
  rw [P.width_eq]
  exact Nat.le_mul_of_pos_right _ P.hb

theorem m_lt_width : P.m < P.width := by
  have := P.width_ge
  have := P.hm
  omega

theorem m_lt_length : P.m < P.length := by
  have := P.bankCount_ge
  have := P.m_lt_width
  dsimp only [length]
  nlinarith

instance width_neZero : NeZero P.width := ⟨P.width_pos.ne'⟩

instance length_neZero : NeZero P.length := ⟨P.length_pos.ne'⟩

theorem length_eq_dimension_sq : P.length = P.dimension ^ 2 * P.b := by
  unfold length dimension width
  ring

theorem dimension_eq : P.dimension = 16 * P.m := by unfold dimension bankCount; ring

theorem horizon_lt : P.horizon < 13 * P.length := by
  have hn := P.bankCount_ge
  have hw := P.width_pos
  dsimp only [horizon, length]
  nlinarith

theorem targets_pos : 0 < P.targets := by
  have hm : 0 < P.m - 1 := by have := P.hm; omega
  exact pow_pos hm _

instance targets_neZero : NeZero P.targets := ⟨P.targets_pos.ne'⟩

/-- The grid spacing is much larger than one; this also separates the
held-owner raw value from the nonzero cover targets. -/
theorem targets_spacing : 256 * P.targets < P.length := by
  have hm : 0 < P.m - 1 := by have := P.hm; omega
  have hm' : P.m - 1 + 1 = P.m := by omega
  have hw := P.width_ge
  dsimp only [targets, length, bankCount]
  nlinarith

theorem targets_lt_length : P.targets < P.length :=
  (Nat.le_mul_of_pos_left _ (by norm_num)).trans_lt P.targets_spacing

/-- The input makes one full outward sweep and returns to zero. -/
def raw (t : ℕ) : ℕ := min t (2 * (P.length - 1) - t)

@[simp] theorem raw_zero : P.raw 0 = 0 := by simp [raw]

theorem raw_range (t : ℕ) : P.raw t < P.length := by
  have hL := P.length_pos
  dsimp [raw]
  omega

theorem raw_step (t : ℕ) : |(P.raw (t + 1) : ℤ) - P.raw t| ≤ 1 := by
  simp only [raw, abs_le]
  omega

theorem raw_initial {t : ℕ} (ht : t < P.length) : P.raw t = t := by
  dsimp [raw]
  omega

theorem raw_after {t : ℕ} (ht : 2 * P.length - 2 ≤ t) : P.raw t = 0 := by
  dsimp [raw]
  omega

/-- Increasing output times, prescribed without any claim about output values. -/
def output (i : ℕ) : ℕ := 11 * P.length + i

theorem output_strictMono : StrictMono P.output := fun _ _ hij => Nat.add_lt_add_left hij _

theorem output_lt {i : ℕ} (hi : i < P.length) : P.output i < P.horizon := by
  dsimp [output, horizon]
  omega

theorem reads_before_output {i : ℕ} (hi : i < P.length) :
    P.raw i = i ∧ i < P.output 0 := by
  exact ⟨P.raw_initial hi, by dsimp [output]; omega⟩

/-- The early core excursion H: rise by L, hold through 2L, descend by 3L. -/
def early : Schedule P.length := Schedule.plateau 0 P.length P.length

/-- The newer exception F: rise from 7L to 8L, hold through 11L, return by 12L. -/
def newer : Schedule P.length := Schedule.plateau (7 * P.length) P.length (3 * P.length)

@[simp] theorem early_depart (i : Fin P.length) : P.early.depart i = i := by simp [early, Schedule.plateau]

@[simp] theorem early_arrive (i : Fin P.length) : P.early.arrive i = 3 * P.length - i := by
  dsimp [early, Schedule.plateau]
  congr 1
  omega

@[simp] theorem early_peak : P.early.peak = P.length := by
  simpa [early] using Schedule.plateau_peak 0 P.length P.length P.length_pos

@[simp] theorem newer_depart (i : Fin P.length) : P.newer.depart i = 7 * P.length + i := rfl

@[simp] theorem newer_arrive (i : Fin P.length) : P.newer.arrive i = 12 * P.length - i := by
  dsimp [newer, Schedule.plateau]
  congr 1
  omega

@[simp] theorem newer_peak : P.newer.peak = 8 * P.length := by
  rw [newer, Schedule.plateau_peak _ _ _ P.length_pos]
  omega

theorem plateau_heads_legal :
    IsWalk (NativeExcursion.walk P.early) ∧ IsWalk (NativeExcursion.walk P.newer) ∧
      NativeExcursion.walk P.early 0 = 0 ∧ NativeExcursion.walk P.newer 0 = 0 ∧
      (∀ c, (entries (NativeExcursion.walk P.early) c (P.horizon - 1)).card ≤ 2) ∧
      (∀ c, (entries (NativeExcursion.walk P.newer) c (P.horizon - 1)).card ≤ 2) :=
  ⟨NativeExcursion.isWalk _, NativeExcursion.isWalk _, NativeExcursion.walk_zero _,
    NativeExcursion.walk_zero _, fun c => NativeExcursion.entries_card_le_two _ c _,
    fun c => NativeExcursion.entries_card_le_two _ c _⟩

end Parameters
end SourceCovers.SerialGeometry
