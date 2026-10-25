import SubcubicMemo.Schedules
import SubcubicMemo.BlockRecovery
import LeanMachine.FiniteProjection

/-! Paid singular-block recovery: nullities are charged in the directions actually used. -/

namespace SubcubicMemo

open Finset Module MotionDepthCodes LeanMachine.FiniteProjection
open scoped BigOperators

variable {V F K A : Type*} [Fintype V] [DecidableEq V] [Field F] [DecidableEq F]
  [Field K] [AddCommGroup A] [Module K A] [FiniteDimensional K A]

omit [FiniteDimensional K A] in
theorem row_kernel_of_ready {M : Matrix V V F} {T : V → V → A →ₗ[K] A}
    {C : Submodule K (V → A)} {W B : Finset V} {v x : V}
    (hrow : ∀ f ∈ C, ∀ v, ∑ y, T v y (f y) = 0)
    (hsupp : ∀ v y, y ∉ insert v (recSet M v) → T v y = 0)
    (houtside : ∀ f ∈ C, ∀ y ∉ W, f y = 0)
    (hready : (insert v (recSet M v) ∩ W).erase x ⊆ B)
    (f : C) (hf : f ∈ vanishing C B) : T v x ((f : V → A) x) = 0 := by
  have hz : ∀ y ∈ univ, y ≠ x → T v y ((f : V → A) y) = 0 := by
    intro y _ hyx
    by_cases hyW : y ∈ W
    · by_cases hyr : y ∈ insert v (recSet M v)
      · rw [hf y (hready (mem_erase.mpr ⟨hyx, mem_inter.mpr ⟨hyr, hyW⟩⟩)), map_zero]
      · rw [hsupp v y hyr, LinearMap.zero_apply]
    · rw [houtside f f.property y hyW, map_zero]
  simpa only [sum_eq_single x hz (fun hn => False.elim (hn (mem_univ _)))]
    using hrow f f.property v

/-- Exact list of nullity costs, before replacing directions by row maxima. -/
theorem Schedule.nullity_directions {M : Matrix V V F} {W B : Finset V}
    {l : List (V × V)} (hl : Schedule M W B l)
    (C : Submodule K (V → A)) (T : V → V → A →ₗ[K] A)
    (hrow : ∀ f ∈ C, ∀ v, ∑ y, T v y (f y) = 0)
    (hsupp : ∀ v y, y ∉ insert v (recSet M v) → T v y = 0)
    (houtside : ∀ f ∈ C, ∀ y ∉ W, f y = 0) :
    finrank K (vanishing C B) ≤ finrank K (vanishing C W) +
      (l.map (fun e => finrank K (LinearMap.ker (T e.1 e.2)))).sum := by
  induction hl with
  | nil hWB => simpa using Submodule.finrank_mono (vanishing_antitone C hWB)
  | @cons B v x l _ _ _ hready _ ih =>
    have hstep := step_bound C B x (T v x)
      (row_kernel_of_ready hrow hsupp houtside hready)
    simp only [List.map_cons, List.sum_cons]
    omega

theorem Schedule.nullity_rows {M : Matrix V V F} {W B : Finset V}
    {l : List (V × V)} (hl : Schedule M W B l)
    (C : Submodule K (V → A)) (T : V → V → A →ₗ[K] A)
    (hrow : ∀ f ∈ C, ∀ v, ∑ y, T v y (f y) = 0)
    (hsupp : ∀ v y, y ∉ insert v (recSet M v) → T v y = 0)
    (houtside : ∀ f ∈ C, ∀ y ∉ W, f y = 0) (κ : V → ℕ)
    (hκ : ∀ v ∈ W, ∀ x ∈ insert v (recSet M v) ∩ W,
      finrank K (LinearMap.ker (T v x)) ≤ κ v) :
    finrank K (vanishing C B) ≤ finrank K (vanishing C W) +
      ∑ v ∈ (l.map Prod.fst).toFinset, κ v := by
  induction hl with
  | nil hWB => simpa using Submodule.finrank_mono (vanishing_antitone C hWB)
  | @cons B v x l hv hx _ hready htail ih =>
    have hstep := step_bound C B x (T v x)
      (row_kernel_of_ready hrow hsupp houtside hready)
    have hcost := hκ v hv x hx
    have hnot : v ∉ (l.map Prod.fst).toFinset := by
      simpa using htail.center_not_used (by
        intro y hy
        by_cases hyx : y = x
        · simp [hyx]
        · exact mem_insert_of_mem (hready (mem_erase.mpr ⟨hyx, hy⟩)))
    simp only [List.map_cons, List.toFinset_cons, sum_insert hnot]
    omega

/-- A singular participating block is paid by its nullity. Each center is
charged at most once, so row maxima suffice. -/
theorem paid_block_matching {M : Matrix V V F} {G : SimpleGraph V}
    (htri : RecTriangleFree M) (hstar : ∀ v, Star M v)
    (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u)
    (C : Submodule K (V → A)) (T : V → V → A →ₗ[K] A)
    (hrow : ∀ f ∈ C, ∀ v, ∑ y, T v y (f y) = 0)
    (hsupp : ∀ v y, y ∉ insert v (recSet M v) → T v y = 0)
    (κ : V → ℕ) (hκ : ∀ v x, x ∈ insert v (recSet M v) →
      finrank K (LinearMap.ker (T v x)) ≤ κ v) :
    finrank K C ≤ G.matchingNumber * finrank K A + ∑ v, κ v := by
  obtain ⟨B, l, hB, hl, _⟩ := exists_matching_schedule htri hstar hpat
  have hz := hl.nullity_rows C T hrow hsupp (by simp) κ (by
    simpa only [inter_univ, mem_univ, true_implies] using hκ)
  rw [LeanMachine.FiniteProjection.vanishing_univ C] at hz
  simp only [finrank_bot, zero_add] at hz
  have hsum : ∑ v ∈ (l.map Prod.fst).toFinset, κ v ≤ ∑ v, κ v :=
    sum_le_sum_of_subset (subset_univ _)
  have hc := dimension_le C B
  have hb := Nat.mul_le_mul_right (finrank K A) hB
  omega

end SubcubicMemo
