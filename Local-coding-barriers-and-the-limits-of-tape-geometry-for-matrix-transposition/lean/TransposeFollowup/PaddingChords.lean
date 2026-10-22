import Transpose.Tape.Blocks
import Mathlib.Tactic

/-! Converting an actual gap in pair residency to the original paper's exact
slot-chord predicate. The time grid has no assumed alignment with a gadget.
These are supporting lemmas for the paid-padding family, not an expander
construction or a paid-machine theorem.
-/

namespace TransposeFollowup

open Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false

theorem residentPair_at_change {r τ : ℕ} {h : ℕ → ℤ} (hτ : 0 < τ)
    (hc : curBlock r h τ ≠ curBlock r h (τ - 1)) :
    residentPair r h τ = {curBlock r h τ, curBlock r h (τ - 1)} := by
  have he := residentPair_succ (r := r) (h := h) (τ - 1)
  rw [Nat.sub_add_cancel hτ, ite_eq_left hc] at he
  exact he

theorem residentPair_constant {r a : ℕ} {h : ℕ → ℤ} (j : ℕ)
    (hc : ∀ t, a ≤ t → t ≤ a + j → curBlock r h t = curBlock r h a) :
    residentPair r h (a + j) = residentPair r h a := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs : curBlock r h (a + j + 1) = curBlock r h (a + j) := by
      exact (hc _ (by omega) (by omega)).trans (hc _ (by omega) (by omega)).symm
    rw [show a + (j + 1) = a + j + 1 by omega, residentPair_succ, ite_eq_right (not_not.mpr hs)]
    exact ih (fun t ha ht => hc t ha (by omega))

/-- A block cannot re-enter the pair without being visited by the current
head. This includes retention of the previous distinct block exactly. -/
theorem residentPair_stays_absent {r a : ℕ} {h : ℕ → ℤ} {β : ℤ}
    (ha : β ∉ residentPair r h a) (j : ℕ)
    (hc : ∀ t, a ≤ t → t ≤ a + j → curBlock r h t ≠ β) :
    β ∉ residentPair r h (a + j) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    have ha0 := hc (a + j) (by omega) (by omega)
    have ha1 := hc (a + j + 1) (by omega) (by omega)
    rw [show a + (j + 1) = a + j + 1 by omega, residentPair_succ]
    split_ifs
    · simp [Ne.symm ha0, Ne.symm ha1]
    · exact ih (fun t ht ht' => hc t ht (by omega))

/-- Last resident step u-1, first returning step w. The endpoint slots are
floor((u-1)/r), floor(w/r), with arbitrary global grid offset. -/
theorem chord_of_residency_gap {r T u w : ℕ} {h : ℕ → ℤ} {β : ℤ}
    (hr : 0 < r) (hu : 0 < u) (huw : u ≤ w) (hwT : w < T)
    (huRes : β ∈ residentPair r h (u - 1)) (hwRes : β ∈ residentPair r h w)
    (hgap : ∀ t, u ≤ t → t < w → β ∉ residentPair r h t)
    (hsep : (u - 1) / r + 1 < w / r) :
    IsChord (pairRes r h T) β ((u - 1) / r) (w / r) := by
  refine ⟨hsep, ?_, ?_, ?_⟩
  · rw [mem_pairRes]
    exact ⟨u - 1, Nat.div_mul_le_self _ _, Nat.lt_div_mul_add hr,
      by omega, huRes⟩
  · rw [mem_pairRes]
    exact ⟨w, Nat.div_mul_le_self _ _, Nat.lt_div_mul_add hr, hwT, hwRes⟩
  · intro y hxy hyw hmem
    obtain ⟨t, hyt, hty, _, hres⟩ := mem_pairRes.mp hmem
    have hut : u ≤ t := by
      have hd := Nat.lt_mul_of_div_lt hxy
      omega
    have htw : t < w := by
      have hy : y + 1 ≤ w / r := by omega
      have hm := Nat.mul_le_mul_right r hy
      rw [Nat.add_mul, one_mul] at hm
      have hw := Nat.div_mul_le_self w r
      omega
    exact hgap t hut htw hres

end TransposeFollowup
