import SourceCovers.NativeBank

set_option autoImplicit false

/-! Radius coordinates for the complete return relation of fresh banks.
Both turns share one interface, including their actual first-maximum owners. -/

namespace SourceCovers.NativeBank

open Finset BoundedNesting

/-- Turn zero is the upper turn and turn one the lower turn. -/
def turnOwner (h D r : ℕ) (q : Fin 2) : ℕ := start h D r + (q.val + 1) * h

theorem turnOwner_bounds (h D r : ℕ) (q : Fin 2) :
    start h D r + h ≤ turnOwner h D r q ∧
      turnOwner h D r q ≤ start h D r + 2 * h := by
  fin_cases q <;> simp [turnOwner] <;> omega

theorem turn_sweep_hop {h D r T a : ℕ} (q : Fin 2)
    (ha : 0 < a) (hah : a ≤ h) (hT : turnOwner h D r q + a < T) :
    IsHop (NativeSweep.walk h (start h D r)) T
      (turnOwner h D r q - a) (turnOwner h D r q + a) := by
  fin_cases q
  · simp only [turnOwner, zero_add, one_mul] at hT ⊢
    have he₁ : start h D r + h - a = start h D r + (h - a) := by omega
    have he₂ : start h D r + h + a = start h D r + 2 * h - (h - a) := by omega
    rw [he₁, he₂]
    exact NativeSweep.upper_hop (by omega) (he₂ ▸ hT)
  · change IsHop (NativeSweep.walk h (start h D r)) T
      (start h D r + 2 * h - a) (start h D r + 2 * h + a)
    exact NativeSweep.lower_hop ha hah hT

theorem turn_hop {h D n r T a : ℕ} (hr : r < n) (q : Fin 2)
    (ha : 0 < a) (hah : a ≤ h) (hT : turnOwner h D r q + a < T) :
    IsHop (walk h D n) T (turnOwner h D r q - a) (turnOwner h D r q + a) :=
  (hop_iff h D n T _ _).mpr ⟨r, hr, turn_sweep_hop q ha hah hT⟩

/-- Uniform finite indexing of every actual return, with no horizon
assumption on a whole bank or on the later banks. -/
theorem hop_iff_radius (h D n T p u : ℕ) : IsHop (walk h D n) T p u ↔
    u < T ∧ ∃ r : Fin n, ∃ q : Fin 2, ∃ a : Fin h,
      p = turnOwner h D r q - (a.val + 1) ∧
      u = turnOwner h D r q + (a.val + 1) := by
  constructor
  · intro hh
    obtain ⟨r, hr, hs⟩ := (hop_iff h D n T p u).mp hh
    obtain ⟨hT, ⟨a, ha, rfl, rfl⟩ | ⟨a, ha, hah, rfl, rfl⟩⟩ :=
      (NativeSweep.hop_iff h (start h D r) T p u).mp hs
    · refine ⟨hT, ⟨r, hr⟩, 0, ⟨h - a - 1, by omega⟩, ?_, ?_⟩
      all_goals simp only [turnOwner, Fin.val_zero, zero_add, one_mul]; omega
    · refine ⟨hT, ⟨r, hr⟩, 1, ⟨a - 1, by omega⟩, ?_, ?_⟩
      all_goals dsimp only [turnOwner]; omega
  · rintro ⟨hT, r, q, a, rfl, rfl⟩
    exact turn_hop r.isLt q (by omega) (by have := a.isLt; omega) hT

theorem turn_owner {h D n r T a : ℕ} (hr : r < n) (q : Fin 2)
    (ha : 0 < a) (hah : a ≤ h) (hT : turnOwner h D r q + a < T) :
    hopOwner (walk h D n) (turnOwner h D r q - a) (turnOwner h D r q + a) =
      turnOwner h D r q := by
  rw [owner_on_bank hr (turn_sweep_hop q ha hah hT)]
  fin_cases q
  · simp only [turnOwner, zero_add, one_mul]
    have he₁ : start h D r + h - a = start h D r + (h - a) := by omega
    have he₂ : start h D r + h + a = start h D r + 2 * h - (h - a) := by omega
    rw [he₁, he₂]
    exact NativeSweep.upper_owner (by omega)
  · exact NativeSweep.lower_owner ha hah

/-- The first step fixes the original upper/lower key; it is not an
extra label assigned to the prescribed family table. -/
theorem turn_rises_iff {h D n r a : ℕ} (hr : r < n) (q : Fin 2)
    (ha : 0 < a) (hah : a ≤ h) :
    walk h D n (turnOwner h D r q - a) <
      walk h D n (turnOwner h D r q - a + 1) ↔ q.val = 0 := by
  have hb := turnOwner_bounds h D r q
  rw [on_bank hr (by omega) (by omega), on_bank hr (by omega) (by omega),
    add_lt_add_iff_left]
  fin_cases q
  · simp only [turnOwner, zero_add, one_mul]
    rw [NativeSweep.rise h (start h D r) (t := start h D r + h - a) (by omega) (by omega),
      NativeSweep.rise h (start h D r) (t := start h D r + h - a + 1) (by omega) (by omega)]
    simp [Nat.add_sub_assoc hah, Nat.add_assoc]
  · change NativeSweep.walk h (start h D r) (start h D r + 2 * h - a) <
      NativeSweep.walk h (start h D r) (start h D r + 2 * h - a + 1) ↔ (1 : ℕ) = 0
    rw [NativeSweep.fall h (start h D r) (t := start h D r + 2 * h - a) (by omega) (by omega),
      NativeSweep.fall h (start h D r) (t := start h D r + 2 * h - a + 1) (by omega) (by omega)]
    simp only [Nat.cast_lt]
    omega

theorem turn_key {h D n r T a k : ℕ} {xs : Fin k → ℕ → ℤ} {head : Fin k}
    (hx : xs head = walk h D n) (hr : r < n) (q : Fin 2)
    (ha : 0 < a) (hah : a ≤ h) (hT : turnOwner h D r q + a < T) :
    key xs (actualOwner xs) (head, turnOwner h D r q - a, turnOwner h D r q + a) =
      (head, decide (q.val = 0), turnOwner h D r q) := by
  simp only [key, side, actualOwner, hx, turn_rises_iff hr q ha hah,
    turn_owner hr q ha hah hT]

/-- Distinct banks and turns have distinct owners on the same head. -/
theorem turnOwner_injective {h D : ℕ} (hh : 0 < h) :
    Function.Injective (fun rq : ℕ × Fin 2 => turnOwner h D rq.1 rq.2) := by
  rintro ⟨r, q⟩ ⟨r', q'⟩ he
  have hq := q.isLt
  have hq' := q'.isLt
  have hn : (4 * r + q.val + 1) * h = (4 * r' + q'.val + 1) * h := by
    dsimp only [turnOwner, start] at he
    nlinarith [he]
  have hc := Nat.eq_of_mul_eq_mul_right hh hn
  have hr : r = r' := by omega
  have heq : q = q' := Fin.ext (by omega)
  exact Prod.ext hr heq

end SourceCovers.NativeBank
