import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Finite random-priority coupling. A uniformly ordered finite universe
selects the same minimum from two nonempty sets exactly when the minimum
of their union lies in their intersection. The exact disagreement count
will supply the finite averaging step in the affine-motion label construction.
No group amenability or return-measure theorem is asserted here. -/
namespace TransposeFollowup.FiniteMinimumCoupling
open Classical Finset
open scoped BigOperators
set_option autoImplicit false

variable {α : Type*} [LinearOrder α]

noncomputable def first (σ : Equiv.Perm α) (A : Finset α) (hA : A.Nonempty) : α :=
  σ.symm ((A.image σ).min' (hA.image σ))

theorem first_mem (σ : Equiv.Perm α) (A : Finset α) (hA : A.Nonempty) :
    first σ A hA ∈ A := by
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp ((A.image σ).min'_mem (hA.image σ))
  simpa only [first, ← he, σ.symm_apply_apply] using ha

theorem first_le (σ : Equiv.Perm α) (A : Finset α) (hA : A.Nonempty) {a : α}
    (ha : a ∈ A) : σ (first σ A hA) ≤ σ a := by
  simp only [first, σ.apply_symm_apply]
  exact (A.image σ).min'_le _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem first_eq_iff (σ : Equiv.Perm α) (A : Finset α) (hA : A.Nonempty) (a : α) :
    first σ A hA=a ↔ a ∈ A ∧ ∀ b ∈ A, σ a ≤ σ b := by
  constructor
  · rintro rfl
    exact ⟨first_mem σ A hA, fun _ hb => first_le σ A hA hb⟩
  · rintro ⟨ha, hmin⟩
    exact σ.injective (le_antisymm (first_le σ A hA ha) (hmin _ (first_mem σ A hA)))

theorem first_comp_swap (σ : Equiv.Perm α) (A : Finset α) (hA : A.Nonempty)
    {a b : α} (ha : a ∈ A) (hb : b ∈ A) :
    first ((Equiv.swap a b).trans σ) A hA=Equiv.swap a b (first σ A hA) := by
  have hswap {x : α} (hx : x ∈ A) : Equiv.swap a b x ∈ A := by
    by_cases hxa : x=a
    · simpa only [hxa, Equiv.swap_apply_left] using hb
    by_cases hxb : x=b
    · simpa only [hxb, Equiv.swap_apply_right] using ha
    simpa only [Equiv.swap_apply_of_ne_of_ne hxa hxb] using hx
  apply (first_eq_iff _ A hA _).mpr
  refine ⟨hswap (first_mem σ A hA), ?_⟩
  intro x hx
  simpa only [Equiv.trans_apply, Equiv.swap_apply_self] using first_le σ A hA (hswap hx)

variable [Fintype α]

theorem first_fibers_card_eq (A : Finset α) (hA : A.Nonempty) {a b : α}
    (ha : a ∈ A) (hb : b ∈ A) :
    (univ.filter (fun σ : Equiv.Perm α => first σ A hA=a)).card=
      (univ.filter (fun σ : Equiv.Perm α => first σ A hA=b)).card := by
  let e : Equiv.Perm α ≃ Equiv.Perm α :=
    { toFun := fun σ => (Equiv.swap a b).trans σ
      invFun := fun σ => (Equiv.swap a b).trans σ
      left_inv := by intro σ; ext x; simp
      right_inv := by intro σ; ext x; simp }
  apply Finset.card_equiv e
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change first σ A hA=a ↔ first ((Equiv.swap a b).trans σ) A hA=b
  rw [first_comp_swap σ A hA ha hb]
  constructor
  · intro h
    rw [h, Equiv.swap_apply_left]
  · intro h
    have hh := congrArg (Equiv.swap a b) h
    simpa only [Equiv.swap_apply_self, Equiv.swap_apply_right] using hh

theorem first_mem_count (A B : Finset α) (hA : A.Nonempty) (hBA : B ⊆ A) :
    (univ.filter (fun σ : Equiv.Perm α => first σ A hA ∈ B)).card*A.card=
      Fintype.card (Equiv.Perm α)*B.card := by
  let a := hA.choose
  have ha : a ∈ A := hA.choose_spec
  let q := (univ.filter (fun σ : Equiv.Perm α => first σ A hA=a)).card
  have hcount (C : Finset α) (hC : C ⊆ A) :
      (univ.filter (fun σ : Equiv.Perm α => first σ A hA ∈ C)).card=C.card*q := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.sum_const_nat (fun b hb => first_fibers_card_eq A hA (hC hb) ha)
  have htotal : Fintype.card (Equiv.Perm α)=A.card*q := by
    have h := hcount A (fun _ hx => hx)
    simpa only [first_mem, Finset.filter_true, Finset.card_univ] using h
  rw [hcount B hBA, htotal]
  ring

omit [Fintype α] in
theorem first_eq_iff_union_first_mem (σ : Equiv.Perm α) (A B : Finset α)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    first σ A hA=first σ B hB ↔ first σ (A ∪ B) (hA.mono (Finset.subset_union_left)) ∈ A ∩ B := by
  let hU := hA.mono (Finset.subset_union_left (s₂:=B))
  constructor
  · intro he
    have hmin : first σ (A ∪ B) hU=first σ A hA := by
      apply (first_eq_iff _ _ _ _).mpr
      refine ⟨Finset.mem_union_left _ (first_mem σ A hA), ?_⟩
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact first_le σ A hA hx
      · rw [he]
        exact first_le σ B hB hx
    rw [hmin]
    exact Finset.mem_inter.mpr ⟨first_mem σ A hA, he.symm ▸ first_mem σ B hB⟩
  · intro h
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp h
    have hea : first σ A hA=first σ (A ∪ B) hU :=
      (first_eq_iff _ _ _ _).mpr ⟨ha, fun x hx => first_le σ (A ∪ B) hU (Finset.mem_union_left _ hx)⟩
    have heb : first σ B hB=first σ (A ∪ B) hU :=
      (first_eq_iff _ _ _ _).mpr ⟨hb, fun x hx => first_le σ (A ∪ B) hU (Finset.mem_union_right _ hx)⟩
    exact hea.trans heb.symm

theorem disagreement_count (A B : Finset α) (hA : A.Nonempty) (hB : B.Nonempty) :
    (univ.filter (fun σ : Equiv.Perm α => first σ A hA ≠ first σ B hB)).card*(A ∪ B).card=
      Fintype.card (Equiv.Perm α)*((A ∪ B) \ (A ∩ B)).card := by
  let hU := hA.mono (Finset.subset_union_left (s₂:=B))
  have he : (univ.filter (fun σ : Equiv.Perm α => first σ A hA ≠ first σ B hB))=
      univ.filter (fun σ : Equiv.Perm α => first σ (A ∪ B) hU ∈ (A ∪ B) \ (A ∩ B)) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
      first_eq_iff_union_first_mem, Finset.mem_sdiff, first_mem]
  rw [he]
  exact first_mem_count (A ∪ B) _ hU Finset.sdiff_subset

end TransposeFollowup.FiniteMinimumCoupling
