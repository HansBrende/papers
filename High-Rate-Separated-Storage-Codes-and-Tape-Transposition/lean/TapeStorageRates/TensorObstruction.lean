import TapeStorageRates.SyndromeFibres
import DirectedRecovery.IncidenceSeparator
import AboveHalfRate.Incidence
import LeanMachine.MatrixRankCertificate

/-! # Literal tensor checks have many short paired paths

The coordinate pairing is the natural pairing of the displayed Kronecker
matrix. No claim is made about other choices of checks for the same kernel.
-/

namespace TapeStorageRates

open Finset DirectedRecovery Module
open scoped Kronecker

set_option autoImplicit false
noncomputable section

variable {V W K : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [Field K]

open Classical in
/-- Rows with at least one nonzero off-diagonal coefficient. -/
def matrixActiveRows (H : Matrix V V K) : Finset V :=
  univ.filter fun v => (matrixHelpers H v).Nonempty

/-- Columns with at least one nonzero off-diagonal coefficient. -/
def matrixActiveColumns (H : Matrix V V K) : Finset V :=
  matrixActiveRows H.transpose

/-- The deficiency of a diagonal-one matrix is bounded by its active rows. -/
theorem matrix_deficiency_le_activeRows (H : Matrix V V K)
    (hd : ∀ v, H v v = 1) :
    Fintype.card V - H.rank ≤ (matrixActiveRows H).card := by
  classical
  have hs : (1 - H).rank ≤ (matrixActiveRows H).card := by
    apply Matrix.rank_le_card_of_support_subset
    intro i hi
    by_contra hnot
    apply hi
    ext j
    by_cases hij : j = i
    · subst j
      simp [Matrix.row, hd]
    · have hz : H i j = 0 := by
        by_contra hn
        exact hnot (mem_filter.mpr ⟨mem_univ _,
          ⟨j, mem_filter.mpr ⟨mem_univ _, hij, hn⟩⟩⟩)
      simp [Matrix.row, Ne.symm hij, hz]
  have h := LeanMachine.MatrixRankCertificate.rank_add_le H (1 - H)
  rw [add_sub_cancel, Matrix.rank_one] at h
  omega

/-- The analogous bound for active columns uses no symmetry assumption. -/
theorem matrix_deficiency_le_activeColumns (H : Matrix V V K)
    (hd : ∀ v, H v v = 1) :
    Fintype.card V - H.rank ≤ (matrixActiveColumns H).card := by
  simpa only [matrixActiveColumns, Matrix.rank_transpose] using
    matrix_deficiency_le_activeRows H.transpose hd

omit [DecidableEq V] in
/-- Matrix deficiency agrees with the dimension of its kernel. -/
theorem matrix_finrank_ker_eq_deficiency (H : Matrix V V K) :
    finrank K (LinearMap.ker H.mulVecLin) = Fintype.card V - H.rank := by
  have h := H.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at h
  change H.rank + finrank K (LinearMap.ker H.mulVecLin) = Fintype.card V at h
  omega

private theorem short_of_cross_witness (A : Matrix V V K) (B : Matrix W W K)
    (ha : ∀ v, A v v = 1) (hb : ∀ w, B w w = 1)
    {a b : V} {c d : W} (hba : b ≠ a) (hdc : d ≠ c)
    (hab : A a b ≠ 0) (hdc' : B d c ≠ 0) :
    (a, c) ∈ shortPairedCoordinates (matrixHelpers (A ⊗ₖ B)) 3 := by
  classical
  let N := matrixHelpers (A ⊗ₖ B)
  have h₁ : (pairedIncidenceGraph N).Adj (Sum.inl (a, c)) (Sum.inr (a, d)) := by
    change (a, c) ∈ matrixHelpers (A ⊗ₖ B) (a, d)
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · intro he
      exact hdc (congrArg Prod.snd he).symm
    · simpa only [Matrix.kroneckerMap_apply, ha, one_mul] using hdc'
  have h₂ : (pairedIncidenceGraph N).Adj (Sum.inr (a, d)) (Sum.inl (b, c)) := by
    change (b, c) ∈ matrixHelpers (A ⊗ₖ B) (a, d)
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · intro he
      exact hba (congrArg Prod.fst he)
    · exact mul_ne_zero hab hdc'
  have h₃ : (pairedIncidenceGraph N).Adj (Sum.inl (b, c)) (Sum.inr (a, c)) := by
    change (b, c) ∈ matrixHelpers (A ⊗ₖ B) (a, c)
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · intro he
      exact hba (congrArg Prod.fst he)
    · simpa only [Matrix.kroneckerMap_apply, hb, mul_one] using hab
  let p : (pairedIncidenceGraph N).Walk (Sum.inl (a, c)) (Sum.inr (a, c)) :=
    .cons h₁ (.cons h₂ (.cons h₃ .nil))
  apply mem_filter.mpr
  exact ⟨mem_univ _, (SimpleGraph.edist_le p).trans (by simp [p])⟩

/-- Every active-row/active-column pair has an explicit three-edge paired walk. -/
theorem active_product_subset_shortPaired (A : Matrix V V K) (B : Matrix W W K)
    (ha : ∀ v, A v v = 1) (hb : ∀ w, B w w = 1) :
    matrixActiveRows A ×ˢ matrixActiveColumns B ⊆
      shortPairedCoordinates (matrixHelpers (A ⊗ₖ B)) 3 := by
  classical
  rintro ⟨a, c⟩ h
  obtain ⟨hA, hB⟩ := mem_product.mp h
  obtain ⟨b, hba⟩ := (mem_filter.mp hA).2
  obtain ⟨d, hdc⟩ := (mem_filter.mp hB).2
  exact short_of_cross_witness A B ha hb (mem_filter.mp hba).2.1
    (mem_filter.mp hdc).2.1 (mem_filter.mp hba).2.2 (mem_filter.mp hdc).2.2

private def transposePortHom (H : Matrix V V K) :
    pairedIncidenceGraph (matrixHelpers H.transpose) →g
      pairedIncidenceGraph (matrixHelpers H) where
  toFun := Sum.swap
  map_rel' := by
    classical
    intro u v huv
    rcases u with p | p <;> rcases v with q | q
    · exact False.elim huv
    · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp huv).2.1.symm,
        (mem_filter.mp huv).2.2⟩
    · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp huv).2.1.symm,
        (mem_filter.mp huv).2.2⟩
    · exact False.elim huv

/-- Transposing a matrix merely swaps the left and right ports. -/
theorem shortPaired_matrix_transpose_subset (H : Matrix V V K) (r : ℕ) :
    shortPairedCoordinates (matrixHelpers H.transpose) r ⊆
      shortPairedCoordinates (matrixHelpers H) r := by
  intro q hq
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  have h := AboveHalf.edist_map_le (transposePortHom H) (Sum.inl q) (Sum.inr q)
  change (pairedIncidenceGraph (matrixHelpers H)).edist (Sum.inr q) (Sum.inl q) ≤ _ at h
  rw [SimpleGraph.edist_comm] at h
  exact h.trans (mem_filter.mp hq).2

/-- Both crossed active products give short paired paths, without reciprocity. -/
theorem active_cross_union_subset_shortPaired (A : Matrix V V K) (B : Matrix W W K)
    (ha : ∀ v, A v v = 1) (hb : ∀ w, B w w = 1) :
    (matrixActiveRows A ×ˢ matrixActiveColumns B) ∪
      (matrixActiveColumns A ×ˢ matrixActiveRows B) ⊆
      shortPairedCoordinates (matrixHelpers (A ⊗ₖ B)) 3 := by
  intro q hq
  rcases mem_union.mp hq with hq | hq
  · exact active_product_subset_shortPaired A B ha hb hq
  · exact shortPaired_matrix_transpose_subset (A ⊗ₖ B) 3
      (active_product_subset_shortPaired A.transpose B.transpose ha hb hq)

/-- Natural-pairing tensor checks have at least the product of the factor
nullities in coordinates whose paired distance is at most three. -/
theorem tensor_shortPaired_card_ge_nullities (A : Matrix V V K) (B : Matrix W W K)
    (ha : ∀ v, A v v = 1) (hb : ∀ w, B w w = 1) :
    finrank K (LinearMap.ker A.mulVecLin) * finrank K (LinearMap.ker B.mulVecLin) ≤
      (shortPairedCoordinates (matrixHelpers (A ⊗ₖ B)) 3).card := by
  rw [matrix_finrank_ker_eq_deficiency, matrix_finrank_ker_eq_deficiency]
  calc
    _ ≤ (matrixActiveRows A).card * (matrixActiveColumns B).card :=
      Nat.mul_le_mul (matrix_deficiency_le_activeRows A ha)
        (matrix_deficiency_le_activeColumns B hb)
    _ = (matrixActiveRows A ×ˢ matrixActiveColumns B).card := by simp
    _ ≤ _ := card_le_card (active_product_subset_shortPaired A B ha hb)

end
end TapeStorageRates
