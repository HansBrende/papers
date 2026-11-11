import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-! # Strict integer cores with closed error fringes

The boundaries are assigned to the fringe. All sets are finite and specified
by integer floor/ceiling endpoints; no real chart description is encoded.
-/

namespace LeanMachine.ProtectedIntervals

noncomputable def closed (a b : ℝ) : Finset ℤ := Finset.Icc ⌈a⌉ ⌊b⌋
noncomputable def core (a b : ℝ) (j : ℕ) : Finset ℤ := Finset.Ioo ⌊a + j⌋ ⌈b - j⌉
noncomputable def fringe (a b : ℝ) (j : ℕ) : Finset ℤ :=
  closed (a - j) (a + j) ∪ closed (b - j) (b + j)

@[simp] theorem mem_closed (a b : ℝ) (z : ℤ) :
    z ∈ closed a b ↔ a ≤ z ∧ (z : ℝ) ≤ b := by
  simp [closed, Int.ceil_le, Int.le_floor]

@[simp] theorem mem_core (a b : ℝ) (j : ℕ) (z : ℤ) :
    z ∈ core a b j ↔ a + j < z ∧ (z : ℝ) < b - j := by
  simp only [core, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]

@[simp] theorem mem_fringe (a b : ℝ) (j : ℕ) (z : ℤ) :
    z ∈ fringe a b j ↔ (a - j ≤ z ∧ (z : ℝ) ≤ a + j) ∨
      (b - j ≤ z ∧ (z : ℝ) ≤ b + j) := by
  simp [fringe]

theorem covered {a b : ℝ} {j : ℕ} {z : ℤ}
    (hz : a - j ≤ z ∧ (z : ℝ) ≤ b + j) : z ∈ core a b j ∪ fringe a b j := by
  rw [Finset.mem_union, mem_core, mem_fringe]
  by_cases ha : (z : ℝ) ≤ a + j
  · exact Or.inr (Or.inl ⟨hz.1, ha⟩)
  · by_cases hb : b - j ≤ (z : ℝ)
    · exact Or.inr (Or.inr ⟨hb, hz.2⟩)
    · exact Or.inl ⟨lt_of_not_ge ha, lt_of_not_ge hb⟩

theorem outside_core {a b : ℝ} {j : ℕ} {z : ℤ}
    (hz : (z : ℝ) ≤ a + j ∨ b - j ≤ z) : z ∉ core a b j := by
  rw [mem_core]
  rcases hz with hz | hz <;> intro hc <;> linarith [hc.1, hc.2]

theorem core_disjoint_fringe (a b : ℝ) (j : ℕ) :
    Disjoint (core a b j) (fringe a b j) := by
  rw [Finset.disjoint_left]
  intro z hc hf
  apply outside_core (z := z) _ hc
  rcases (mem_fringe a b j z).mp hf with hf | hf
  · exact Or.inl hf.2
  · exact Or.inr hf.1

theorem card_closed_le {a b : ℝ} (hab : a ≤ b) :
    ((closed a b).card : ℝ) ≤ b - a + 1 := by
  by_cases h : ⌈a⌉ ≤ ⌊b⌋ + 1
  · have hc := Int.card_Icc_of_le ⌈a⌉ ⌊b⌋ h
    have hc' : ((closed a b).card : ℝ) = (⌊b⌋ : ℝ) + 1 - (⌈a⌉ : ℝ) := by
      exact_mod_cast hc
    linarith [Int.floor_le b, Int.le_ceil a]
  · have he : closed a b = ∅ := by
      apply Finset.Icc_eq_empty_of_lt
      omega
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith

theorem card_core_le {a b : ℝ} (hab : a ≤ b) (j : ℕ) :
    ((core a b j).card : ℝ) ≤ b - a + 1 := by
  have hsub : core a b j ⊆ closed a b := by
    intro z hz
    rw [mem_core] at hz
    rw [mem_closed]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    constructor <;> linarith [hz.1, hz.2]
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (card_closed_le hab)

theorem card_fringe_le (a b : ℝ) (j : ℕ) : (fringe a b j).card ≤ 4 * j + 2 := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have ha := card_closed_le (a := a - j) (b := a + j) (by linarith)
  have hb := card_closed_le (a := b - j) (b := b + j) (by linarith)
  have hu : ((fringe a b j).card : ℝ) ≤
      (closed (a - j) (a + j)).card + (closed (b - j) (b + j)).card := by
    exact_mod_cast Finset.card_union_le (closed (a - j) (a + j)) (closed (b - j) (b + j))
  have hh : ((fringe a b j).card : ℝ) ≤ 4 * j + 2 := by linarith
  exact_mod_cast hh

end LeanMachine.ProtectedIntervals
