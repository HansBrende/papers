import GapAreaMemo.Staircase

set_option autoImplicit false

/-!
# The two zigzag shapes of the banks

A *late* zigzag rises and descends at unit speed from time `σ` and then rises
again with each level held `f` steps, so that its second rise spans the first
rise of a zigzag `f` times larger that starts at its trough. An *early*
zigzag rises with each level held `f` steps, during the second rise of a
zigzag `f` times larger that ends at time `u`, and then descends and rises at
unit speed.
-/

namespace SourceCovers.Zigzag

open Finset LeanMachine.ScheduledExcursion

theorem peak_eq {h : ℕ} (hh : 0 < h) (D : Schedule h) :
    D.peak = D.depart ⟨h - 1, by omega⟩ + 1 := by
  unfold Schedule.peak
  congr 1
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    exact D.depart_strictMono.monotone (Fin.le_iff_val_le_val.mpr (by have := i.isLt; simp; omega))
  · exact Finset.le_sup (f := D.depart) (mem_univ _)

/-- The late zigzag of height `a` from time `σ`, second rise slowed by `f`. -/
def late (σ a f : ℕ) (ha : 0 < a) (hf : 0 < f) : Shape a where
  P := { depart := fun c => σ + c
         arrive := fun c => σ + 2 * a - c
         depart_strictMono := fun i j hij => by exact Nat.add_lt_add_left hij σ
         arrive_strictAnti := fun i j hij => by
           (try simp only); have := j.isLt; have : i.val < j.val := hij; omega
         separated := fun i j => by have := i.isLt; have := j.isLt; omega }
  Q := { depart := fun i => σ + a + i
         arrive := fun i => σ + 2 * a + f * (a - i)
         depart_strictMono := fun i j hij => by exact Nat.add_lt_add_left hij _
         arrive_strictAnti := fun i j hij => by
           try simp only
           have := j.isLt
           have hij' : i.val < j.val := hij
           have : a - j.val < a - i.val := by omega
           have := Nat.mul_lt_mul_of_pos_left this hf
           omega
         separated := fun i j => by
           try simp only
           have := i.isLt; have := j.isLt
           have : 1 ≤ f * (a - j.val) := Nat.one_le_iff_ne_zero.mpr (by
             apply Nat.mul_ne_zero (by omega) (by omega))
           omega }
  p_arrive := fun c => by
    rw [peak_eq ha]
    try simp only
    have := c.isLt
    omega
  q_depart := fun i => by
    rw [peak_eq ha]
    try simp only
    omega

/-- The early zigzag of height `cc`, first rise slowed by `f`, after time `u`. -/
def early (u cc f : ℕ) (hc : 0 < cc) (hf : 0 < f) : Shape cc where
  P := { depart := fun c => u + f * (c + 1) - 1
         arrive := fun c => u + f * cc + cc - c
         depart_strictMono := fun i j hij => by
           try simp only
           have hij' : i.val < j.val := hij
           have := Nat.mul_lt_mul_of_pos_left (show i.val + 1 < j.val + 1 by omega) hf
           have : 1 ≤ f * (i.val + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
             (by omega))
           omega
         arrive_strictAnti := fun i j hij => by
           (try simp only); have := j.isLt; have : i.val < j.val := hij; omega
         separated := fun i j => by
           try simp only
           have := i.isLt; have := j.isLt
           have := Nat.mul_le_mul_left f (show i.val + 1 ≤ cc by omega)
           have : 1 ≤ f * (i.val + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
             (by omega))
           omega }
  Q := { depart := fun i => u + f * cc + i
         arrive := fun i => u + f * cc + 2 * cc - i
         depart_strictMono := fun i j hij => by exact Nat.add_lt_add_left hij _
         arrive_strictAnti := fun i j hij => by
           (try simp only); have := j.isLt; have : i.val < j.val := hij; omega
         separated := fun i j => by have := i.isLt; have := j.isLt; omega }
  p_arrive := fun c => by
    rw [peak_eq hc]
    try simp only
    have := c.isLt
    have h1 : 1 ≤ f * cc := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have h2 : f * (cc - 1 + 1) = f * cc := by rw [Nat.sub_add_cancel (by omega)]
    rw [h2]
    omega
  q_depart := fun i => by
    rw [peak_eq hc]
    try simp only
    have h1 : 1 ≤ f * cc := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have h2 : f * (cc - 1 + 1) = f * cc := by rw [Nat.sub_add_cancel (by omega)]
    rw [h2]
    omega

theorem late_peak (σ a f : ℕ) (ha : 0 < a) (hf : 0 < f) : (late σ a f ha hf).P.peak = σ + a := by
  rw [peak_eq ha]; simp only [late]; omega

theorem late_trough (σ a f : ℕ) (ha : 0 < a) (hf : 0 < f) :
    (late σ a f ha hf).trough = σ + 2 * a := by
  unfold Shape.trough; rw [late_peak]; omega

theorem late_finish (σ a f : ℕ) (ha : 0 < a) (hf : 0 < f) :
    (late σ a f ha hf).finish ha = σ + 2 * a + f * a := by
  simp [Shape.finish, late]

theorem early_peak (u cc f : ℕ) (hc : 0 < cc) (hf : 0 < f) :
    (early u cc f hc hf).P.peak = u + f * cc := by
  rw [peak_eq hc]
  simp only [early]
  have h1 : 1 ≤ f * cc := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : f * (cc - 1 + 1) = f * cc := by rw [Nat.sub_add_cancel (by omega)]
  rw [h2]
  omega

theorem early_trough (u cc f : ℕ) (hc : 0 < cc) (hf : 0 < f) :
    (early u cc f hc hf).trough = u + f * cc + cc := by
  unfold Shape.trough; rw [early_peak]

theorem early_finish (u cc f : ℕ) (hc : 0 < cc) (hf : 0 < f) :
    (early u cc f hc hf).finish hc = u + f * cc + 2 * cc := by
  simp [Shape.finish, early]

end SourceCovers.Zigzag

namespace SourceCovers.Zigzag

/-- A zigzag segment with its height. -/
structure Seg where
  h : ℕ
  pos : 0 < h
  Z : Shape h

namespace Seg

variable (S : Seg)

abbrev walk : ℕ → ℤ := S.Z.walk
abbrev finish : ℕ := S.Z.finish S.pos

end Seg
end SourceCovers.Zigzag
