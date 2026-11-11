import Mathlib

/-! # Fibre bounds for forgetting heads and erasing coordinates

The erased coordinate set may depend on the head. The fibre encoding pays
for that head and precisely the entries erased at it.
-/

namespace LeanMachine.FiniteMaskFibres

open Finset
open scoped BigOperators

variable {I H A : Type*} [Fintype I] [Fintype H] [Fintype A]
  [DecidableEq I] [DecidableEq H] [DecidableEq A]

def masked (blank : A) (S : Finset I) (v : I → A) : I → A :=
  fun i => if i ∈ S then blank else v i

def maskedVertex (blank : A) (S : H → Finset I) (v : (I → A) × H) : I → A :=
  masked blank (S v.2) v.1

theorem forget_head_fiber (v : I → A) :
    (univ.filter fun x : (I → A) × H => x.1 = v).card = Fintype.card H := by
  classical
  have he : (univ.filter fun x : (I → A) × H => x.1 = v) =
      (univ : Finset H).image (fun h => (v, h)) := by
    ext x
    rcases x with ⟨x, h⟩
    simp [eq_comm]
  rw [he, card_image_of_injective _ (by intro x y h; exact Prod.mk.inj h |>.2), card_univ]

omit [DecidableEq H] in
/-- Exact sum over the possible heads, before replacing each erased-set
cardinality by a common maximum. -/
theorem masked_fiber_sum (blank : A) (S : H → Finset I) (v : I → A) :
    (univ.filter fun x : (I → A) × H => maskedVertex blank S x = v).card ≤
      ∑ h : H, Fintype.card A ^ (S h).card := by
  classical
  let E := {x : (I → A) × H // maskedVertex blank S x = v}
  let encode (x : E) : Σ h : H, ((S h) → A) := ⟨x.val.2, fun i => x.val.1 i⟩
  have hinj : Function.Injective encode := by
    intro x y he
    have hh : x.val.2 = y.val.2 := congrArg Sigma.fst he
    apply Subtype.ext
    apply Prod.ext _ hh
    funext i
    by_cases hi : i ∈ S x.val.2
    · have hentry : x.val.1 i = y.val.1 i := by
        have he' : (fun j : S x.val.2 => x.val.1 j) =
            (fun j : S x.val.2 => y.val.1 j) := by
          cases x with
          | mk x hx =>
            cases y with
            | mk y hy =>
              rcases x with ⟨x, h⟩
              rcases y with ⟨y, h'⟩
              dsimp at hh
              subst h'
              exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
        exact congr_fun he' ⟨i, hi⟩
      exact hentry
    · have hx := congr_fun x.property i
      have hy := congr_fun y.property i
      simpa [maskedVertex, masked, hi, ← hh] using hx.trans hy.symm
  have hc := Fintype.card_le_of_injective encode hinj
  simpa [E, Fintype.card_sigma, Fintype.card_pi, Fintype.card_coe,
    Fintype.card_subtype] using hc

omit [DecidableEq H] in
theorem masked_fiber_le (blank : A) (S : H → Finset I) (v : I → A)
    (L : ℕ) (hS : ∀ h, (S h).card ≤ L) :
    (univ.filter fun x : (I → A) × H => maskedVertex blank S x = v).card ≤
      Fintype.card H * Fintype.card A ^ L := by
  classical
  let : Nonempty A := ⟨blank⟩
  calc
    _ ≤ ∑ h : H, Fintype.card A ^ (S h).card := masked_fiber_sum blank S v
    _ ≤ ∑ _h : H, Fintype.card A ^ L := sum_le_sum fun h _ =>
      Nat.pow_le_pow_right (Fintype.card_pos (α := A)) (hS h)
    _ = _ := by simp

noncomputable def headWindow {n : ℕ} (H : ℕ) (h : Fin n) : Finset (Fin n) :=
  univ.filter fun i => |(i.val : ℤ) - h.val| ≤ H

theorem card_headWindow {n : ℕ} (H : ℕ) (h : Fin n) : (headWindow H h).card ≤ 2 * H + 1 := by
  classical
  calc
    _ = ((headWindow H h).image Fin.val).card := (card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Icc (h.val - H) (h.val + H)).card := by
      apply card_le_card
      intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      have hh := abs_le.mp (mem_filter.mp hi).2
      simp only [mem_Icc]
      omega
    _ ≤ 2 * H + 1 := by simp; omega

theorem masked_headWindow_fiber_le {n : ℕ} (blank : A) (H : ℕ) (v : Fin n → A) :
    (univ.filter fun x : (Fin n → A) × Fin n => maskedVertex blank (headWindow H) x = v).card ≤
      n * Fintype.card A ^ (2 * H + 1) := by
  simpa only [Fintype.card_fin] using masked_fiber_le blank (headWindow H) v (2 * H + 1)
    (card_headWindow H)

end LeanMachine.FiniteMaskFibres
