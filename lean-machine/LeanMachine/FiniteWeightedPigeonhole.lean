import LeanMachine.ContextPruning
import Mathlib

/-! # A heavy attained cell of a finite weighted partition -/

namespace LeanMachine.FiniteWeightedPigeonhole

open Finset
open scoped BigOperators

theorem exists_heavy_cell {Ω Y : Type*} [Fintype Ω] [DecidableEq Y]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (B : Finset Ω) (f : Ω → Y)
    {M : ℝ} (hp : 0 < ContextPruning.mass w B) (hM : 0 < M)
    (hcount : ((B.image f).card : ℝ) ≤ M) :
    ∃ y ∈ B.image f,
      ContextPruning.mass w B / M ≤ ContextPruning.mass w (B.filter fun x => f x = y) := by
  classical
  have hB : B.Nonempty := by
    by_contra hn
    have he : B = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp [he, ContextPruning.mass] at hp
  let cell (y : Y) := ContextPruning.mass w (B.filter fun x => f x = y)
  obtain ⟨y, hy, hmax⟩ := (B.image f).exists_max_image cell (hB.image f)
  have hsum : ∑ z ∈ B.image f, cell z = ContextPruning.mass w B := by
    exact sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem f hx) w
  have hnonneg : 0 ≤ cell y := ContextPruning.mass_nonneg hw _
  refine ⟨y, hy, (div_le_iff₀ hM).mpr ?_⟩
  calc
    _ = ∑ z ∈ B.image f, cell z := hsum.symm
    _ ≤ ∑ _z ∈ B.image f, cell y := sum_le_sum fun z hz => hmax z hz
    _ = ((B.image f).card : ℝ) * cell y := by simp
    _ ≤ M * cell y := mul_le_mul_of_nonneg_right hcount hnonneg
    _ = _ := mul_comm _ _

end LeanMachine.FiniteWeightedPigeonhole
