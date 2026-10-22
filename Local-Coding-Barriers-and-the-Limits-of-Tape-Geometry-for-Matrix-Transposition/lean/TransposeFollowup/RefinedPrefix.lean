import Mathlib.InformationTheory.Coding.Kraft

/-! Appending a leaf-dependent, fixed-width separator record to a prefix-free
transcript preserves prefix freedom. The separator choice itself is already
determined by the transcript. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

theorem prefix_refinement_first {L α : Type*} (first suffix : L → List α)
    (hfirst : InformationTheory.IsPrefixFree (Set.range first))
    {x y : L} (h : first x ++ suffix x <+: first y ++ suffix y) :
    first x = first y := by
  have hx := (List.prefix_append (first x) (suffix x)).trans h
  have hy := List.prefix_append (first y) (suffix y)
  rcases List.prefix_or_prefix_of_prefix hx hy with hxy | hyx
  · exact hfirst _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  · exact (hfirst _ ⟨y, rfl⟩ _ ⟨x, rfl⟩ hyx).symm

theorem prefix_refinement {L α : Type*} (first suffix : L → List α)
    (hfirst : InformationTheory.IsPrefixFree (Set.range first))
    (hlen : ∀ x y, first x = first y → (suffix x).length = (suffix y).length) :
    InformationTheory.IsPrefixFree (Set.range (fun x => first x ++ suffix x)) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  have hxy := prefix_refinement_first first suffix hfirst h
  apply h.eq_of_length
  simp only [List.length_append, hxy, hlen x y hxy]

theorem kraft_indexed {L : Type*} [Fintype L]
    (code : L → List Bool) (hinj : Function.Injective code)
    (hprefix : InformationTheory.IsPrefixFree (Set.range code)) :
    (∑ l, (1 / 2 : ℝ) ^ (code l).length) ≤ 1 := by
  classical
  let S := Finset.univ.image code
  have hS : InformationTheory.IsPrefixFree (S : Set (List Bool)) := by
    apply hprefix.anti
    intro w hw
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨l, rfl⟩
  have hsum : (∑ l, (1 / 2 : ℝ) ^ (code l).length) =
      ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length := by
    symm
    apply Finset.sum_image
    intro x _ y _ hxy
    exact hinj hxy
  rw [hsum]
  simpa using hS.finsetSum_one_div_card_pow_length_le_one

end TransposeFollowup
