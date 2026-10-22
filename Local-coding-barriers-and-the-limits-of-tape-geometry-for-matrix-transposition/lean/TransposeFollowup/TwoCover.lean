import TransposeFollowup.CoordinateEntropy

/-! The decoding two-cover argument, with arbitrary correlated inputs and
arbitrary nonlinear local decoding. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

def ownedCoordinates {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (owner : ι → κ) (a : κ) : Finset ι := Finset.univ.filter (fun i => owner i = a)

def internalCoordinates {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (owner demander : ι → κ) : Finset ι :=
  Finset.univ.filter (fun i => owner i = demander i)

theorem coordinateEntropy_union_of_decoding {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) (I O : Finset ι)
    (hdecode : (fun x => bitView O (X x)).FactorsThrough (fun x => bitView I (X x))) :
    coordinateEntropy p X (I ∪ O) = coordinateEntropy p X I := by
  apply le_antisymm
  · apply observationEntropy_le_of_factorsThrough p hp
    intro x y hxy
    apply (bitView_eq_iff _ _ _).mpr
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (bitView_eq_iff _ _ _).mp hxy i hi
    · exact (bitView_eq_iff _ _ _).mp (hdecode hxy) i hi
  · exact coordinateEntropy_mono p hp X Finset.subset_union_left

/-- Individual group recovery yields a two-cover inequality. A group can
have an empty initial block; its requested bits must then be fixed on the
sample family. No independence or linearity is assumed. -/
theorem two_cover_decoding_entropy {Ω ι κ : Type*}
    [Fintype Ω] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → ι → Bool) (owner demander : ι → κ)
    (hdecode : ∀ a,
      (fun x => bitView (ownedCoordinates demander a) (X x)).FactorsThrough
        (fun x => bitView (ownedCoordinates owner a) (X x))) :
    2 * observationEntropy p X ≤
      (∑ a, coordinateEntropy p X (ownedCoordinates owner a)) +
        coordinateEntropy p X (internalCoordinates owner demander) := by
  classical
  let S : Option κ → Finset ι
    | none => internalCoordinates owner demander
    | some a => ownedCoordinates owner a ∪ ownedCoordinates demander a
  have hcover : ∀ i, (2 : ℝ) ≤ ∑ a, if i ∈ S a then (1 : ℝ) else 0 := by
    intro i
    by_cases hd : owner i = demander i
    · norm_num [S, Fintype.sum_option, ownedCoordinates, internalCoordinates, hd]
    · have hpoint : ∀ a,
          (if owner i = a ∨ demander i = a then (1 : ℝ) else 0) =
            (if owner i = a then 1 else 0) + (if demander i = a then 1 else 0) := by
        intro a
        by_cases ho : owner i = a <;> by_cases hr : demander i = a
        · exact (hd (ho.trans hr.symm)).elim
        · simp [ho, hr]
        · simp [ho, hr]
        · simp [ho, hr]
      simp only [Fintype.sum_option, S, ownedCoordinates, internalCoordinates,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hd, ite_false]
      simp_rw [hpoint]
      norm_num [Finset.sum_add_distrib]
  have h := coordinateEntropy_cover p hp hp1 X S 2 hcover
  simp only [Fintype.sum_option, S] at h
  simp_rw [coordinateEntropy_union_of_decoding p hp X _ _ (hdecode _)] at h
  simpa only [add_comm] using h

theorem two_cover_decoding {Ω ι κ : Type*}
    [Fintype Ω] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → ι → Bool) (owner demander : ι → κ)
    (hdecode : ∀ a,
      (fun x => bitView (ownedCoordinates demander a) (X x)).FactorsThrough
        (fun x => bitView (ownedCoordinates owner a) (X x))) :
    2 * observationEntropy p X ≤
      (∑ a, coordinateEntropy p X (ownedCoordinates owner a)) +
        ((internalCoordinates owner demander).card : ℝ) * Real.log 2 := by
  exact (two_cover_decoding_entropy p hp hp1 X owner demander hdecode).trans
    (add_le_add le_rfl (coordinateEntropy_le_card p hp hp1 X _))

end TransposeFollowup
