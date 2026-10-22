import TransposeFollowup.NestedExcursion
import Transpose.Tape.Corollaries

/-! Exact multiplicity and full-slot containment of the nested-excursion
chords. This handles arbitrary offsets from the global time-zero grid.
-/

namespace TransposeFollowup.NestedExcursion

open Transpose.Tape Transpose.Tape.Impl
open Classical
set_option autoImplicit false

variable {r K a c : ℕ} {z : ℤ} {h : ℕ → ℤ} (E : NestedExcursion r K a c z h)
include E

theorem source_slot_contained {j : ℕ} (hj : j + 2 ≤ 4 * K) :
    a ≤ ((a + (j + 2) * r - 1) / r) * r ∧
    ((a + (j + 2) * r - 1) / r + 1) * r ≤ a + 6 * K * r := by
  have hr := E.r_pos
  have hK := E.K_pos
  have hkr : r ≤ K * r := by nlinarith
  have hjr := Nat.mul_le_mul_right r hj
  have hu : a + (j + 2) * r - 1 + 1 = a + (j + 2) * r :=
    Nat.sub_add_cancel (by nlinarith)
  have hd := Nat.div_mul_le_self (a + (j + 2) * r - 1) r
  have hd' : a + (j + 2) * r - 1 < (a + (j + 2) * r - 1) / r * r + r :=
    Nat.lt_div_mul_add hr
  constructor <;> nlinarith

theorem target_slot_contained {j : ℕ} (hj : j + 2 ≤ 4 * K) :
    c ≤ ((c + (4 * K - j - 1) * r + 1) / r) * r ∧
    ((c + (4 * K - j - 1) * r + 1) / r + 1) * r ≤ c + 6 * K * r := by
  have hr := E.r_pos
  have hK := E.K_pos
  have hkr : r ≤ K * r := by nlinarith
  have hd := Nat.div_mul_le_self (c + (4 * K - j - 1) * r + 1) r
  have hd' : c + (4 * K - j - 1) * r + 1 <
      (c + (4 * K - j - 1) * r + 1) / r * r + r := Nat.lt_div_mul_add hr
  have htail := Nat.mul_le_mul_right r (show 1 ≤ 4 * K - j - 1 by omega)
  have hw := E.return_time_le hj
  constructor <;> nlinarith

/-- Distinct spatial blocks give distinct counted (target-slot,block) pairs.
The bound uses the exact imported `crossChords` definition. -/
theorem crossing_chord_count {T : ℕ} (hT : c + 4 * K * r < T) (lab : ℕ → ℕ)
    (hl : ∀ j : Fin (4 * K - 1),
      lab ((a + (j.val + 2) * r - 1) / r) ≠
        lab ((c + (4 * K - j.val - 1) * r + 1) / r)) :
    4 * K - 1 ≤ (crossChords (pairRes r h T) lab (numSlots r T)).card := by
  let code : Fin (4 * K - 1) → crossChords (pairRes r h T) lab (numSlots r T) :=
    fun j => ⟨(((c + (4 * K - j.val - 1) * r + 1) / r), z + j.val), by
      have hj : j.val + 2 ≤ 4 * K := by have := j.isLt; omega
      have hc := E.isChord hj hT
      apply mem_crossChords.mpr
      refine ⟨div_lt_numSlots E.r_pos (by have := E.return_time_le hj; omega), hc.2.2.1, ?_⟩
      exact ⟨_, hl j, hc⟩⟩
  have hinj : Function.Injective code := by
    intro i j he
    have hb := congrArg (fun q : crossChords (pairRes r h T) lab (numSlots r T) => q.val.2) he
    change z + (i.val : ℤ) = z + (j.val : ℤ) at hb
    apply Fin.ext
    omega
  have hc := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_fin, Fintype.card_coe] using hc

end TransposeFollowup.NestedExcursion
