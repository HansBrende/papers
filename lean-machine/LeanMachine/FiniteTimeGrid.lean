import Mathlib

/-! # Fixed finite intervals preceding a witness time

The grid is constructed from the witness by integer division. In particular,
its whole interval precedes the witness, including a halting witness.
-/

namespace LeanMachine.FiniteTimeGrid

open Finset

def previousIndex (ell t : ℕ) : ℕ := t / ell - 1

def interval (ell j : ℕ) : Finset ℕ := Ico (j * ell) ((j + 1) * ell)

theorem card_interval (ell j : ℕ) : (interval ell j).card = ell := by
  simp [interval, Nat.add_mul]

theorem previous_interval {ell R t : ℕ} (hell : 0 < ell)
    (hR : 2 * ell ≤ R) (ht : ell ≤ t) :
    ∀ u ∈ interval ell (previousIndex ell t), t - R ≤ u ∧ u < t := by
  have hq : 1 ≤ t / ell := (Nat.le_div_iff_mul_le hell).mpr (by simpa using ht)
  have hrem := Nat.mod_lt t hell
  have heq := Nat.mod_add_div t ell
  rw [Nat.mul_comm ell] at heq
  have hpred : (t / ell - 1) * ell + ell = t / ell * ell := by
    calc
      _ = (t / ell - 1 + 1) * ell := by ring
      _ = _ := by rw [Nat.sub_add_cancel hq]
  intro u hu
  have hu' := mem_Ico.mp hu
  dsimp [previousIndex] at hu'
  have he : (t / ell - 1 + 1) * ell = t / ell * ell := by
    rw [Nat.sub_add_cancel hq]
  rw [he] at hu'
  constructor <;> omega

theorem half_radius_interval {R t : ℕ} (hR : 2 ≤ R) (ht : R < t) :
    (interval (R / 2) (previousIndex (R / 2) t)).card = R / 2 ∧
      ∀ u ∈ interval (R / 2) (previousIndex (R / 2) t), t - R ≤ u ∧ u < t := by
  refine ⟨card_interval _ _, previous_interval (by omega) ?_ (by omega)⟩
  omega

theorem previousIndex_mem {ell t T : ℕ} (ht : t ≤ T) :
    previousIndex ell t ∈ range (T / ell + 1) := by
  have h : t / ell ≤ T / ell := Nat.div_le_div_right ht
  exact mem_range.mpr ((Nat.sub_le _ _).trans_lt (h.trans_lt (Nat.lt_succ_self _)))

/-- The interval has a quarter-radius lower bound at every radius at least
two; the slightly weaker real bound is convenient for uniform asymptotics. -/
theorem half_radius_length {R : ℕ} (hR : 2 ≤ R) :
    (R : ℝ) / 4 ≤ (R / 2 : ℕ) := by
  have hdiv : R ≤ 2 * (R / 2) + 1 := by omega
  have hpos : 1 ≤ R / 2 := by omega
  have hr : (R : ℝ) ≤ 2 * (R / 2 : ℕ) + 1 := by exact_mod_cast hdiv
  have hp : (1 : ℝ) ≤ (R / 2 : ℕ) := by exact_mod_cast hpos
  linarith

theorem floor_half_length {x : ℝ} (hx : 4 ≤ x) :
    x / 4 ≤ (⌊x⌋₊ / 2 : ℕ) := by
  have hf : 4 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hdiv : ⌊x⌋₊ ≤ 2 * (⌊x⌋₊ / 2) + 1 := by omega
  have hpos : 2 ≤ ⌊x⌋₊ / 2 := by omega
  have hr : (⌊x⌋₊ : ℝ) ≤ 2 * (⌊x⌋₊ / 2 : ℕ) + 1 := by exact_mod_cast hdiv
  have hp : (2 : ℝ) ≤ (⌊x⌋₊ / 2 : ℕ) := by exact_mod_cast hpos
  have hh := Nat.lt_floor_add_one x
  linarith

theorem grid_count_le {T ell : ℕ} {C beta P : ℝ}
    (hell : 0 < ell) (hbeta : 0 < beta) (hP : 0 < P)
    (hlen : beta * P / 4 ≤ ell) (hT : (T : ℝ) ≤ 2 * C * P) :
    T / ell + 1 ≤ ⌈8 * C / beta⌉₊ + 1 := by
  have hC : 0 ≤ C := by nlinarith [Nat.cast_nonneg (α := ℝ) T]
  have hceil : 8 * C / beta ≤ (⌈8 * C / beta⌉₊ : ℝ) := Nat.le_ceil _
  have hb : 8 * C ≤ (⌈8 * C / beta⌉₊ : ℝ) * beta :=
    (div_le_iff₀ hbeta).mp hceil
  have hbound : (T : ℝ) ≤ (⌈8 * C / beta⌉₊ : ℝ) * ell := by
    have hh := mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg ⌈8 * C / beta⌉₊)
    have hP' := mul_le_mul_of_nonneg_right hb hP.le
    nlinarith
  have hn : T ≤ ⌈8 * C / beta⌉₊ * ell := by exact_mod_cast hbound
  have hdiv := Nat.div_le_div_right (c := ell) hn
  rw [Nat.mul_div_cancel _ hell] at hdiv
  omega

end LeanMachine.FiniteTimeGrid
