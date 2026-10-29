import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-! Disjoint nonempty sums over a finite abelian group give a surjective,
balanced map. Coordinates outside every sum remain independent of any
observation that is unchanged when those coordinates are updated. -/

namespace LeanMachine

open Finset
open scoped BigOperators Classical
noncomputable section

/-- Each fibre of a surjective homomorphism has its exact share of the domain. -/
theorem card_fiber_mul_card {A B : Type*} [AddGroup A] [AddGroup B]
    [Fintype A] [Fintype B] [DecidableEq B]
    (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    (univ.filter fun a => f a = b).card * Fintype.card B = Fintype.card A := by
  classical
  have he (c : B) : (univ.filter fun a => f a = c).card =
      (univ.filter fun a => f a = b).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf c) (hf b)
  have hs := card_eq_sum_card_fiberwise (s := (univ : Finset A))
    (t := (univ : Finset B)) (f := f) (fun _ _ => mem_univ _)
  simpa only [he, card_univ, sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm] using hs.symm

/-- A finite bank of sums with nonempty, pairwise disjoint supports. -/
structure DisjointSums (ι κ : Type*) where
  support : κ → Finset ι
  nonempty : ∀ k, (support k).Nonempty
  disjoint : Pairwise fun k l => Disjoint (support k) (support l)

namespace DisjointSums

variable {ι κ A : Type*} (C : DisjointSums ι κ)

def representative (k : κ) : ι := (C.nonempty k).choose

theorem representative_mem (k : κ) : C.representative k ∈ C.support k :=
  (C.nonempty k).choose_spec

theorem representative_mem_iff (k l : κ) : C.representative k ∈ C.support l ↔ k = l := by
  constructor
  · intro h
    by_contra hne
    exact disjoint_left.mp (C.disjoint hne) (C.representative_mem k) h
  · rintro rfl
    exact C.representative_mem k

theorem representative_injective : Function.Injective C.representative := by
  intro k l h
  apply (C.representative_mem_iff k l).mp
  rw [h]
  exact C.representative_mem l

include C in
theorem card_le [Fintype ι] [Fintype κ] : Fintype.card κ ≤ Fintype.card ι :=
  Fintype.card_le_of_injective _ C.representative_injective

/-- The encoder uses the ordinary group sum, including bitwise XOR as the
group operation on words over `ZMod 2`. -/
def encode [AddCommGroup A] : (ι → A) →+ (κ → A) where
  toFun x k := ∑ i ∈ C.support k, x i
  map_zero' := by ext k; simp
  map_add' x y := by ext k; simp [sum_add_distrib]

@[simp] theorem encode_apply [AddCommGroup A] (x : ι → A) (k : κ) :
    C.encode x k = ∑ i ∈ C.support k, x i := rfl

theorem encode_surjective [Fintype κ] [AddCommGroup A] :
    Function.Surjective (C.encode (A := A)) := by
  classical
  intro y
  refine ⟨fun i => ∑ k, if C.representative k = i then y k else 0, ?_⟩
  funext l
  rw [encode_apply, sum_comm]
  simp [C.representative_mem_iff]

theorem fiber_card [Fintype ι] [Fintype κ] [AddCommGroup A] [Fintype A]
    (y : κ → A) :
    (univ.filter fun x : ι → A => C.encode x = y).card =
      Fintype.card A ^ (Fintype.card ι - Fintype.card κ) := by
  classical
  have h := card_fiber_mul_card C.encode C.encode_surjective y
  rw [Fintype.card_fun, Fintype.card_fun] at h
  have hp : 0 < Fintype.card A ^ Fintype.card κ := pow_pos Fintype.card_pos _
  apply Nat.eq_of_mul_eq_mul_right hp
  rw [h, ← pow_add, Nat.sub_add_cancel C.card_le]

/-- Any one summand is determined by its sum and the remaining summands. -/
theorem recover [AddCommGroup A] [DecidableEq ι] (x : ι → A) (k : κ)
    {i : ι} (hi : i ∈ C.support k) :
    x i = C.encode x k - ∑ j ∈ (C.support k).erase i, x j := by
  rw [encode_apply, ← sum_erase_add _ _ hi]
  abel

theorem encode_update [AddCommGroup A] [DecidableEq ι]
    {i : ι} (hi : ∀ k, i ∉ C.support k) (x : ι → A) (a : A) :
    C.encode (Function.update x i a) = C.encode x := by
  ext k
  apply sum_congr rfl
  intro j hj
  exact Function.update_of_ne (fun h : j = i => hi k (h ▸ hj)) _ _

end DisjointSums

/-- Splitting off an ignored coordinate in any observation fibre. -/
def coordinateFiberEquiv {ι A B : Type*} [DecidableEq ι]
    (f : (ι → A) → B) (i : ι) (a : A) (b : B)
    (hf : ∀ x c, f (Function.update x i c) = f x) :
    {x : ι → A // f x = b} ≃ A × {x : ι → A // x i = a ∧ f x = b} where
  toFun x := (x.val i, ⟨Function.update x.val i a, by simp [hf, x.property]⟩)
  invFun z := ⟨Function.update z.2.val i z.1, (hf _ _).trans z.2.property.2⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv z := by
    rcases z with ⟨c, x, hx, hfx⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp [← hx]

/-- Conditional counting form of independence of an ignored coordinate. -/
theorem card_coordinate_fiber {ι A B : Type*} [Fintype ι] [Fintype A]
    [DecidableEq ι] [DecidableEq A] [DecidableEq B]
    (f : (ι → A) → B) (i : ι) (a : A) (b : B)
    (hf : ∀ x c, f (Function.update x i c) = f x) :
    (univ.filter fun x : ι → A => x i = a ∧ f x = b).card * Fintype.card A =
      (univ.filter fun x : ι → A => f x = b).card := by
  have h := Fintype.card_congr (coordinateFiberEquiv f i a b hf)
  simpa only [Fintype.card_prod, Fintype.card_subtype, mul_comm] using h.symm

/-- Unnormalized joint-count identity for independence under the full uniform
input cube. The observation may include every other coordinate. -/
theorem card_independent_coordinate {ι A B : Type*} [Fintype ι] [Fintype A]
    [DecidableEq ι] [DecidableEq A] [DecidableEq B]
    (f : (ι → A) → B) (i : ι) (a : A) (b : B)
    (hf : ∀ x c, f (Function.update x i c) = f x) :
    (univ.filter fun x : ι → A => x i = a ∧ f x = b).card * Fintype.card (ι → A) =
      (univ.filter fun x : ι → A => x i = a).card *
        (univ.filter fun x : ι → A => f x = b).card := by
  have h₁ := card_coordinate_fiber f i a b hf
  have h₂ := card_coordinate_fiber (fun _ : ι → A => ()) i a () (by simp)
  simp only [and_true, filter_true, card_univ] at h₂
  rw [← h₁, ← h₂]
  ring

end
end LeanMachine
