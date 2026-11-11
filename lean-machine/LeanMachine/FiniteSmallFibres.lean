import LeanMachine.FinitePartition
import Mathlib

/-! # Small attained fibres under one deterministic label map

The same event controls all assertions already valid on each sufficiently
large full fibre. There is no union over those assertions or their indices.
-/

namespace LeanMachine.FiniteSmallFibres

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {X Y : Type*} [DecidableEq Y]

noncomputable def small (S : Finset X) (f : X → Y) (L : ℝ) : Finset X :=
  S.filter fun x => ((S.filter fun y => f y = f x).card : ℝ) < L

/-- Strict counting bound for the actual small-fibre event. M bounds attained
labels and may be real. Empty source sets are included. -/
theorem small_card_lt (S : Finset X) (f : X → Y) {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) (hcount : ((S.image f).card : ℝ) ≤ M) :
    ((small S f L).card : ℝ) < M * L := by
  classical
  by_cases hS : S.Nonempty
  · have hfib (z : Y) : ((small S f L).filter fun x => f x = z).card < L := by
      by_cases hz : ((S.filter fun x => f x = z).card : ℝ) < L
      · have hc : ((small S f L).filter fun x => f x = z).card ≤
            (S.filter fun x => f x = z).card :=
          card_le_card (filter_subset_filter _ (filter_subset _ _))
        exact lt_of_le_of_lt (by exact_mod_cast hc) hz
      · have he : ((small S f L).filter fun x => f x = z) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨hx, hfx⟩ := mem_filter.mp hx
          exact hz (by simpa only [hfx] using (mem_filter.mp hx).2)
        simpa only [he, card_empty, Nat.cast_zero] using hL
    have hsum : ∑ z ∈ S.image f, (((small S f L).filter fun x => f x = z).card : ℝ) =
        (small S f L).card := by
      have hh := sum_card_fiberwise_eq_card_filter (small S f L) (S.image f) f
      have he : ((small S f L).filter fun x => f x ∈ S.image f) = small S f L :=
        filter_eq_self.mpr fun x hx => mem_image_of_mem f (mem_filter.mp hx).1
      rw [he] at hh
      exact_mod_cast hh
    calc
      _ = ∑ z ∈ S.image f, (((small S f L).filter fun x => f x = z).card : ℝ) := hsum.symm
      _ < ∑ _z ∈ S.image f, L := sum_lt_sum_of_nonempty (hS.image f) (fun z _ => hfib z)
      _ = ((S.image f).card : ℝ) * L := by simp
      _ ≤ M * L := mul_le_mul_of_nonneg_right hcount hL.le
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp only [he, small, filter_empty, card_empty, Nat.cast_zero]
    exact mul_pos hM hL

/-- Base-b exponential specialization used when each attained trace costs h
bits and a full fibre of rate r already satisfies every desired inequality. -/
theorem small_exponential_card (S : Finset X) (f : X → Y)
    {b h r : ℝ} (hb : 0 < b) (hcount : ((S.image f).card : ℝ) ≤ b ^ h) :
    ((small S f (b ^ r)).card : ℝ) < b ^ (h + r) := by
  simpa only [← Real.rpow_add hb] using
    small_card_lt S f (Real.rpow_pos_of_pos hb r) (Real.rpow_pos_of_pos hb h) hcount

/-- The event preserves every property of every sufficiently large actual
fibre, independently of how many parameters index those properties. -/
theorem good_all {I : Type*} (S : Finset X) (f : X → Y) (L : ℝ)
    (P : I → X → Prop)
    (hP : ∀ z, L ≤ ((S.filter fun x => f x = z).card : ℝ) →
      ∀ x ∈ S, f x = z → ∀ i, P i x) {x : X}
    (hx : x ∈ S) (hgood : x ∉ small S f L) : ∀ i, P i x := by
  have hsize : L ≤ ((S.filter fun y => f y = f x).card : ℝ) := by
    by_contra hn
    exact hgood (mem_filter.mpr ⟨hx, lt_of_not_ge hn⟩)
  exact hP (f x) hsize x hx rfl

end LeanMachine.FiniteSmallFibres
