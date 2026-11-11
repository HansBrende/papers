import SharedDecoders.CapacityRunsComponents
import SharedDecoders.CapacityIteration

/-! The actual translate sets for steps `s, 3s, 9s` cover radii `1, 4, 13`. -/

namespace SharedDecoders

open CapacityRuns Finset

variable {d : ℕ} [NeZero d]

private def coeff₁ : Finset ℕ := {0, 1}
private def coeff₂ : Finset ℕ := {0, 1, 3, 4}
private def coeff₃ : Finset ℕ := {0, 1, 3, 4, 9, 10, 12, 13}

private theorem coeff₁_cover : ∀ j ≤ 1, ∃ u ∈ coeff₁, ∃ v ∈ coeff₁, u = j + v := by
  intro j hj
  interval_cases j <;> decide

private theorem coeff₂_cover : ∀ j ≤ 4, ∃ u ∈ coeff₂, ∃ v ∈ coeff₂, u = j + v := by
  intro j hj
  interval_cases j <;> decide

private theorem coeff₃_cover : ∀ j ≤ 13, ∃ u ∈ coeff₃, ∃ v ∈ coeff₃, u = j + v := by
  intro j hj
  interval_cases j <;> decide

omit [NeZero d] in
private theorem image_covers (S : Finset ℕ) (s : ZMod d) (r : ℕ)
    (h : ∀ j ≤ r, ∃ u ∈ S, ∃ v ∈ S, u = j + v) :
    CoversRadius (S.image (fun j => j • s)) s r := by
  intro j hj
  obtain ⟨u, hu, v, hv, he⟩ := h j hj
  exact ⟨u • s, mem_image_of_mem _ hu, v • s, mem_image_of_mem _ hv,
    by rw [he, add_nsmul]⟩

omit [NeZero d] in
theorem first_shift_set (s : ZMod d) :
    extendShifts {0} s = coeff₁.image (fun j => j • s) := by
  ext x
  simp [extendShifts, coeff₁, eq_comm, or_comm]

omit [NeZero d] in
theorem second_shift_set (s : ZMod d) :
    extendShifts (extendShifts {0} s) (3 • s) = coeff₂.image (fun j => j • s) := by
  have h4 : s + 3 * s = 4 * s := by ring
  ext x
  simp [extendShifts, coeff₂, h4, eq_comm, or_left_comm]

omit [NeZero d] in
theorem third_shift_set (s : ZMod d) :
    extendShifts (extendShifts (extendShifts {0} s) (3 • s)) (9 • s) =
      coeff₃.image (fun j => j • s) := by
  have h4 : s + 3 * s = 4 * s := by ring
  have h10 : s + 9 * s = 10 * s := by ring
  have h12 : 3 * s + 9 * s = 12 * s := by ring
  have h13 : 4 * s + 9 * s = 13 * s := by ring
  ext x
  simp [extendShifts, coeff₃, h4, h10, h12, h13, eq_comm, or_left_comm]

omit [NeZero d] in
theorem first_shift_covers (s : ZMod d) : CoversRadius (extendShifts {0} s) s 1 := by
  rw [first_shift_set]
  exact image_covers coeff₁ s 1 coeff₁_cover

omit [NeZero d] in
theorem second_shift_covers (s : ZMod d) :
    CoversRadius (extendShifts (extendShifts {0} s) (3 • s)) s 4 := by
  rw [second_shift_set]
  exact image_covers coeff₂ s 4 coeff₂_cover

omit [NeZero d] in
theorem third_shift_covers (s : ZMod d) :
    CoversRadius (extendShifts (extendShifts (extendShifts {0} s) (3 • s)) (9 • s)) s 13 := by
  rw [third_shift_set]
  exact image_covers coeff₃ s 13 coeff₃_cover

/-- The sharp one-step run estimate, valid also for constant and one-point orbits. -/
theorem componentCount_first_shift (p : ZMod d → Bool) (s : ZMod d) :
    componentCount p (extendShifts {0} s) ≤ changeCount p s + Nat.gcd d s.val :=
  componentCount_le_changes_add_gcd p _ s (first_shift_covers s)

/-- The second actual translate graph contains every same-colour jump to radius four. -/
theorem componentCount_second_shift (p : ZMod d → Bool) (s : ZMod d) :
    componentCount p (extendShifts (extendShifts {0} s) (3 • s)) ≤
      runCount p s 4 + 2 * Nat.gcd d s.val :=
  componentCount_le_runs_add_two_gcd p _ s 4 (by omega) (second_shift_covers s)

/-- The third actual translate graph contains every same-colour jump to radius thirteen. -/
theorem componentCount_third_shift (p : ZMod d → Bool) (s : ZMod d) :
    componentCount p (extendShifts (extendShifts (extendShifts {0} s) (3 • s)) (9 • s)) ≤
      runCount p s 13 + 2 * Nat.gcd d s.val :=
  componentCount_le_runs_add_two_gcd p _ s 13 (by omega) (third_shift_covers s)

end SharedDecoders
