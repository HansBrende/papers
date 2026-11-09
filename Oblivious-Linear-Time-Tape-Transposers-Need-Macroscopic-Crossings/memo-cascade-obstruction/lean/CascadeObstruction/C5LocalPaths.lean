import CascadeObstruction.C5Trace

/-! Extract a charged stage's exact frozen displacement from a complete run.
The surrounding stages may have arbitrary displacement. -/

namespace CascadeObstruction.C5

set_option autoImplicit false

theorem position_min_length (xs : List Tick) (h : Fin 3) (t : ℕ) :
    position xs h (min t xs.length) = position xs h t := by
  by_cases ht : t ≤ xs.length
  · rw [Nat.min_eq_left ht]
  · rw [Nat.min_eq_right (by omega)]
    exact (position_frozen xs h (t := t) (by omega)).symm

theorem position_segment (pre mid post : List Tick) (h : Fin 3) (t : ℕ) :
    position (pre ++ mid ++ post) h (pre.length + min t mid.length) -
      position (pre ++ mid ++ post) h pre.length = position mid h t := by
  have hpre : pre.length ≤ pre.length + min t mid.length := by omega
  have hpost : pre.length + min t mid.length - (pre ++ mid).length = 0 := by
    rw [List.length_append]
    have := Nat.min_le_right t mid.length
    omega
  rw [position_append, position_append, position_append, position_append]
  rw [position_frozen pre h hpre]
  simp only [List.length_append] at hpost ⊢
  rw [hpost]
  simp only [position_zero, add_zero, Nat.add_sub_cancel_left, Nat.sub_self]
  have hz : pre.length - (pre.length + mid.length) = 0 := by omega
  rw [hz]
  simp only [position_zero, add_zero, add_sub_cancel_left, position_min_length]

end CascadeObstruction.C5
