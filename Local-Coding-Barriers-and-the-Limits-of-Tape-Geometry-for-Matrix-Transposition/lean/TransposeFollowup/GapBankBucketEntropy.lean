import TransposeFollowup.GapBankGroupedGeometry
import TransposeFollowup.GapBankLeafEntropy

/-! The exact bucket-count leaf bound, using concrete gap records and the
single globally counted near-coordinate set. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

namespace GapBankCode

variable {d b sigma M K : ℕ} (C : GapBankCode d b sigma)

theorem bucket_leaf_entropy
    {Ω A : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hc : C.CorrectOn (Set.range X))
    (m : List Bool) (hm : ∀ x, C.transcript (X x) = m)
    (B : RowBuckets d M) (label : MatrixBit d b → A)
    (hM : 0 < M) (hK : 0 < K)
    (hsize : ∀ a, (occupiedBuckets label (fun v => B.bucket v.1) a).card ≤ K)
    (R : Finset (MatrixBit d b → Bool))
    (hR : CoordinateRectangle (B.groupedOwner label hsize) R)
    (hXR : ∀ x, C.bank.recode (X x) ∈ R)
    (rows : Fin d → Finset (Fin d)) (L nu : ℕ)
    (hrows : ∀ r, (rows r).card ≤ nu)
    (hclass : ∀ v w : MatrixBit d b, label v = label w → w.1 ∈ rows v.1)
    (hpad : ∀ a, (B.paddedFiber sigma a).card ≤ L + 2 * sigma)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : C.bank.StateBudget s) :
    observationEntropy p X ≤
      ((d * b * nu * (L + 2 * sigma) : ℕ) + ((K + 1) * bucketPatternCount M K : ℕ) * s) * Real.log 2 +
      ((bucketPatternCount M K : ℝ) - 1) * (Real.log (R.card : ℝ) - observationEntropy p X) := by
  let : Nonempty (BucketPattern M K) := ⟨⟨{⟨0,hM⟩}, by
    exact ⟨Finset.singleton_nonempty _, by simp; omega⟩⟩⟩
  apply C.grouped_leaf_entropy p hp hp1 X hc m hm
    (B.groupedOwner label hsize) R hR hXR
    (B.groupedNear label hsize sigma rows) (fun U => B.GapIndex U.val)
    (fun U => B.gap U.val)
    (fun U j => B.gap_interval U.val j)
    (fun U j i hi c t => B.grouped_gap_outside label hsize U j i hi c t)
    (fun U v hv hn => B.grouped_gap_cover label hsize sigma rows hclass U v hv hn)
    K (d * b * nu * (L + 2 * sigma)) (bucketPatternCount M K)
  · rw [B.groupedNear_sum]
    exact B.nearCoordinates_card b sigma L nu rows hrows hpad
  · exact fun U => B.grouped_gap_count U
  · exact (card_bucketPattern M K).le
  · exact hs0
  · exact hs

end GapBankCode
end TransposeFollowup
