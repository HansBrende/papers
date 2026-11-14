import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import LeanMachine.LastRowSupport

/-!
# Rank across a closed principal cut

If the rows in `P` vanish outside `P`, the ranks of the two principal
submatrices sum to at most the rank of the full matrix. The proof projects
the full row space onto the complementary coordinates and uses rank–nullity.
-/

namespace LeanMachine.ClosedCutRank

open Module Submodule

set_option autoImplicit false

variable {F V : Type*} [Field F] [Fintype V] [DecidableEq V]

private def restrict (P : Finset V) : (V → F) →ₗ[F] (P → F) where
  toFun x p := x p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq V] in
private theorem finrank_add_map_le
    {W : Type*} [AddCommGroup W] [Module F W]
    (S U : Submodule F (V → F)) (f : (V → F) →ₗ[F] W)
    (hUS : U ≤ S) (hUk : U ≤ LinearMap.ker f) :
    finrank F U + finrank F (S.map f) ≤ finrank F S := by
  let j : U →ₗ[F] LinearMap.ker (f.domRestrict S) :=
    { toFun := fun x => ⟨⟨x, hUS x.property⟩, hUk x.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (congrArg (fun z => (z.val : V → F)) h)
  have hdim := LinearMap.finrank_le_finrank_of_injective hj
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.domRestrict S)
  rw [LinearMap.range_domRestrict] at hrn
  exact (Nat.add_le_add_right hdim _).trans_eq (by simpa [Nat.add_comm] using hrn)

/-- A closed principal cut gives a lower bound by the sum of its diagonal
block ranks. No diagonal or support-degree hypothesis is needed. -/
theorem rank_principal_add_compl_le (B : Matrix V V F) (P : Finset V)
    (hzero : ∀ p ∈ P, ∀ q ∉ P, B p q = 0) :
    (B.submatrix (fun p : P => p.val) (fun p : P => p.val)).rank +
      (B.submatrix (fun q : ↥Pᶜ => q.val) (fun q : ↥Pᶜ => q.val)).rank ≤ B.rank := by
  let S : Submodule F (V → F) := span F (Set.range B.row)
  let U : Submodule F (V → F) := span F (Set.range fun p : P => B.row p)
  have hUS : U ≤ S := by
    apply span_mono
    rintro _ ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  have hUk : U ≤ LinearMap.ker (restrict (F := F) Pᶜ) := by
    apply span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext q
    exact hzero p p.property q (Finset.mem_compl.mp q.property)
  have hA : span F (Set.range (B.submatrix
      (fun p : P => p.val) (fun p : P => p.val)).row) = U.map (restrict P) := by
    dsimp only [U]
    rw [LinearMap.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨B.row p, ⟨p, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, rfl⟩
  have hD : span F (Set.range (B.submatrix
      (fun q : ↥Pᶜ => q.val) (fun q : ↥Pᶜ => q.val)).row) ≤ S.map (restrict Pᶜ) := by
    apply span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact ⟨B.row q, subset_span ⟨q, rfl⟩, rfl⟩
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row,
    Matrix.rank_eq_finrank_span_row, hA]
  exact (Nat.add_le_add (Submodule.finrank_map_le _ _) (Submodule.finrank_mono hD)).trans
    (finrank_add_map_le S U (restrict Pᶜ) hUS hUk)

/-- Rank at most one, a nonzero diagonal and the four-arc exclusion leave
at most two indices. This includes the empty matrix. -/
theorem card_le_two_of_rank_le_one (B : Matrix V V F)
    (hdiag : ∀ v, B v v ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (hrank : B.rank ≤ 1) : Fintype.card V ≤ 2 := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h => simp
  | inr h =>
    let v : V := Classical.choice h
    let S : Submodule F (V → F) := span F (Set.range B.row)
    have hv0 : B.row v ≠ 0 := by
      intro hz
      exact hdiag v (congrFun hz v)
    have hvS : B.row v ∈ S := subset_span ⟨v, rfl⟩
    have hpos : 1 ≤ finrank F S := by
      have hl : span F {B.row v} ≤ S := span_le.mpr (Set.singleton_subset_iff.mpr hvS)
      simpa [finrank_span_singleton hv0] using Submodule.finrank_mono hl
    have hdim : finrank F S = 1 := by
      have he : B.rank = finrank F S := B.rank_eq_finrank_span_row
      omega
    have hS := eq_span_singleton_of_mem_of_finrank_eq_one hdim hvS hv0
    have hc := LastRowSupport.card_le_one_of_rows_mem_span_insert B ∅ v
      (Finset.univ.erase v) hpattern
      (fun j _ => by
        have hj : B.row j ∈ S := subset_span ⟨j, rfl⟩
        rw [hS] at hj
        simpa [Matrix.row_apply'] using hj)
      (by simp) (fun j _ => hdiag j) (by simp)
    have hn := Finset.card_erase_add_one (s := Finset.univ) (a := v) (Finset.mem_univ v)
    rw [Finset.card_univ] at hn
    omega

end LeanMachine.ClosedCutRank

#print axioms LeanMachine.ClosedCutRank.rank_principal_add_compl_le
#print axioms LeanMachine.ClosedCutRank.card_le_two_of_rank_le_one
