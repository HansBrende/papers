import TransposeFollowup.GadgetLabels
import TransposeFollowup.ExpanderCutCount

/-! Good gadget vertices retain their slot label; every bad vertex gets its
own fresh label. This gives uniformly small graph label classes for expansion,
even when the original finite slot labeling oscillates at every step.
-/

namespace TransposeFollowup

open Classical
open Transpose.Tape
set_option autoImplicit false

noncomputable def repairedLabel {V : Type*} [Fintype V]
    (lab : ℕ → ℕ) (lo hi : V → ℕ) (i : V) : ℕ ⊕ V :=
  if i ∈ badWindows lab lo hi then Sum.inr i else Sum.inl (lab (lo i))

theorem repairedLabel_good {V : Type*} [Fintype V]
    (lab : ℕ → ℕ) (lo hi : V → ℕ) {i : V} (hi' : i ∉ badWindows lab lo hi) :
    repairedLabel lab lo hi i = Sum.inl (lab (lo i)) := by simp [repairedLabel, hi']

theorem repairedLabel_inl_fiber {V : Type*} [Fintype V]
    (lab : ℕ → ℕ) (lo hi : V → ℕ) (ell : ℕ) :
    labelFiber (repairedLabel lab lo hi) (Sum.inl ell) =
      Finset.univ.filter (fun i => i ∉ badWindows lab lo hi ∧ lab (lo i) = ell) := by
  ext i
  simp only [mem_labelFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : i ∈ badWindows lab lo hi <;> simp [repairedLabel, h]

theorem repairedLabel_inr_fiber_subset {V : Type*} [Fintype V] [DecidableEq V]
    (lab : ℕ → ℕ) (lo hi : V → ℕ) (i : V) :
    labelFiber (repairedLabel lab lo hi) (Sum.inr i) ⊆ {i} := by
  intro j hj
  have he := (mem_labelFiber _ _ _).mp hj
  by_cases h : j ∈ badWindows lab lo hi
  · simpa [repairedLabel, h] using he
  · simp [repairedLabel, h] at he

theorem repairedLabel_small {V : Type*} [Fintype V] [DecidableEq V]
    (lab : ℕ → ℕ) (lo hi : V → ℕ) (N L m : ℕ)
    (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (hN : ∀ i, hi i ≤ N) (hL : ∀ i, L ≤ hi i - lo i)
    (hL2 : 2 ≤ L) (hv : 2 ≤ Fintype.card V) (hmv : m ≤ Fintype.card V)
    (hm : ∀ ell, ((Finset.range N).filter (fun s => lab s = ell)).card ≤ m) :
    ∀ l, 2 * (labelFiber (repairedLabel lab lo hi) l).card ≤ Fintype.card V := by
  intro l
  cases l with
  | inl ell =>
    have h := good_window_class_size lab lo hi N L m ell hsep hN hL (hm ell)
    rw [repairedLabel_inl_fiber]
    exact (Nat.mul_le_mul_right _ hL2).trans (h.trans hmv)
  | inr i =>
    have h := Finset.card_le_card (repairedLabel_inr_fiber_subset lab lo hi i)
    simp only [Finset.card_singleton] at h
    omega

theorem good_window_label_eq {V : Type*} [Fintype V]
    (lab : ℕ → ℕ) (lo hi : V → ℕ) {i : V} (hi' : i ∉ badWindows lab lo hi)
    {s : ℕ} (hs : s ∈ Finset.Ico (lo i) (hi i)) : lab s = lab (lo i) := by
  by_contra h
  exact hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, s, hs, h⟩)

end TransposeFollowup
