import LeanMachine.ShiftedGrid
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Finite row and column partitions with exact group widths and the real
ceiling number of output windows. Arbitrary output orders are permutations
of these literal ordinal windows. -/

namespace LeanMachine.ShiftedGrid
open Finset

theorem label_le_self (g θ x : ℕ) (hg : 0 < g) (hθ : θ < g) : label g θ x ≤ x := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hg).mpr
  have : x ≤ x * g := by nlinarith
  nlinarith

def finiteLabel (d g θ : ℕ) (hg : 0 < g) (hθ : θ < g) (x : Fin d) : Fin d :=
  ⟨label g θ x.val, (label_le_self g θ x.val hg hθ).trans_lt x.isLt⟩

theorem labelFiber_card_le (d g θ a : ℕ) (hg : 0 < g) :
    ((univ : Finset (Fin d)).filter (fun r => label g θ r.val = a)).card ≤ g := by
  let rows := (univ : Finset (Fin d)).filter (fun r => label g θ r.val = a)
  have h := card_le_of_constant (θ := θ) hg
    (S := rows.image Fin.val) (by
      intro x hx y hy
      obtain ⟨r, hr, rfl⟩ := mem_image.mp hx
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hy
      exact (mem_filter.mp hr).2.trans (mem_filter.mp hs).2.symm)
  rwa [card_image_of_injective _ Fin.val_injective] at h

theorem finiteLabel_fiber_card_le (d g θ : ℕ) (hg : 0 < g) (hθ : θ < g) (a : Fin d) :
    ((univ : Finset (Fin d)).filter (fun r => finiteLabel d g θ hg hθ r = a)).card ≤ g := by
  convert labelFiber_card_le d g θ a.val hg using 1
  congr 1
  ext r
  simp only [mem_filter, mem_univ, true_and, Fin.ext_iff, finiteLabel]

/-- A column's write ordinal determines its chronological window. -/
noncomputable def windowLabel (d w : ℕ) (hw : 0 < w) (r : Fin d) :
    Fin ⌈(d : ℝ) / w⌉₊ :=
  ⟨r.val / w, Nat.lt_ceil.mpr (by
    have hdiv := Nat.div_mul_le_self r.val w
    have hdivR : ((r.val / w : ℕ) : ℝ) * w ≤ r.val := by exact_mod_cast hdiv
    apply (lt_div_iff₀ (show (0 : ℝ)<w by exact_mod_cast hw)).mpr
    exact hdivR.trans_lt (by exact_mod_cast r.isLt))⟩

theorem windowLabel_fiber_card_le (d w : ℕ) (hw : 0 < w)
    (a : Fin ⌈(d : ℝ) / w⌉₊) :
    ((univ : Finset (Fin d)).filter (fun r => windowLabel d w hw r = a)).card ≤ w := by
  convert labelFiber_card_le d w 0 a.val hw using 1
  congr 1
  ext r
  simp [Fin.ext_iff, windowLabel, label]

end LeanMachine.ShiftedGrid
