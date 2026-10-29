import LeanMachine.PeriodicStripe

/-! # Reindexing sums by the actual transpose source stripes -/

namespace LeanMachine.PeriodicStripe

open Finset

/-- Reindex a column-dependent sum through the unique transpose column of each
raw coordinate. Degenerate dimensions and entry widths give empty sums. -/
theorem sum_stripe_eq_sum_coordinates {M : Type*} [AddCommMonoid M]
    (d b : ℕ) (f : ℕ → ℕ → M) :
    (∑ j ∈ range d, ∑ z ∈ stripe d b j, f j z) =
      ∑ z ∈ range (d * (d * b)), f (z / b % d) z := by
  by_cases hd : d = 0
  · simp [hd]
  by_cases hb : b = 0
  · simp [hb, stripe]
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have hb' : 0 < b := Nat.pos_of_ne_zero hb
  calc
    _ = ∑ j ∈ range d, ∑ z ∈ stripe d b j, f (z / b % d) z := by
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro z hz
      have hcol := (occupied_iff_column hb' d j z).mp (mem_filter.mp hz).2
      rw [hcol]
    _ = ∑ z ∈ (range d).biUnion (stripe d b), f (z / b % d) z :=
      (sum_biUnion (pairwiseDisjoint_stripe hb' d)).symm
    _ = _ := by rw [biUnion_stripe hd' hb']

theorem sum_fin_stripe_eq_sum_coordinates {M : Type*} [AddCommMonoid M]
    (d b : ℕ) (f : ℕ → ℕ → M) :
    (∑ j : Fin d, ∑ z ∈ stripe d b j, f j z) =
      ∑ z ∈ range (d * (d * b)), f (z / b % d) z := by
  rw [Fin.sum_univ_eq_sum_range (fun j => ∑ z ∈ stripe d b j, f j z) d]
  exact sum_stripe_eq_sum_coordinates d b f

/-- Dependent column-index form. Only the positivity needed to construct a
`Fin d` index remains; entry width may be zero. -/
theorem sum_fin_stripe_eq_sum_coordinates_of_pos {M : Type*} [AddCommMonoid M]
    {d : ℕ} (hd : 0 < d) (b : ℕ) (f : Fin d → ℕ → M) :
    (∑ j : Fin d, ∑ z ∈ stripe d b j, f j z) =
      ∑ z ∈ range (d * (d * b)), f ⟨z / b % d, Nat.mod_lt _ hd⟩ z := by
  let f' : ℕ → ℕ → M := fun j z => if hj : j < d then f ⟨j, hj⟩ z else 0
  calc
    _ = ∑ j : Fin d, ∑ z ∈ stripe d b j, f' j z := by
      apply sum_congr rfl
      intro j hj
      simp only [f', dite_eq_left j.isLt]
    _ = ∑ z ∈ range (d * (d * b)), f' (z / b % d) z :=
      sum_fin_stripe_eq_sum_coordinates d b f'
    _ = _ := by
      apply sum_congr rfl
      intro z hz
      simp only [f', dite_eq_left (Nat.mod_lt _ hd)]

end LeanMachine.PeriodicStripe
