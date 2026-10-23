import TransposeFollowup.GapBankGroups
import TransposeFollowup.GapBankNear

/-! Concrete group records from exact occupied bucket sets. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {d b M K : ℕ} {A : Type*} [DecidableEq A]

namespace RowBuckets

variable (B : RowBuckets d M) (label : MatrixBit d b → A)
    (hsize : ∀ a, (occupiedBuckets label (fun v => B.bucket v.1) a).card ≤ K)

noncomputable def groupedOwner : MatrixBit d b → BucketPattern M K :=
  bucketGroup label (fun v => B.bucket v.1) hsize

noncomputable def groupedNear (sigma : ℕ) (rows : Fin d → Finset (Fin d))
    (U : BucketPattern M K) : Finset (MatrixBit d b) :=
  (B.nearCoordinates b sigma rows).filter (fun v => B.groupedOwner label hsize v = U)

theorem groupedNear_sum (sigma : ℕ) (rows : Fin d → Finset (Fin d)) :
    (∑ U : BucketPattern M K, (B.groupedNear label hsize sigma rows U).card) =
      (B.nearCoordinates b sigma rows).card := by
  classical
  simpa [groupedNear] using Finset.sum_card_fiberwise_eq_card_filter
    (B.nearCoordinates b sigma rows) Finset.univ (B.groupedOwner label hsize)

theorem grouped_gap_outside (U : BucketPattern M K) (j : B.GapIndex U.val)
    (i : Fin d) (hi : i ∈ B.gap U.val j) (c : Fin d) (t : Fin b) :
    (i,(c,t)) ∉ ownedCoordinates (B.groupedOwner label hsize) U := by
  intro hv
  have he : B.groupedOwner label hsize (i,(c,t)) = U := by
    simpa [ownedCoordinates] using hv
  have hm := bucketGroup_contains label (fun v => B.bucket v.1) hsize (i,(c,t))
  change B.bucket i ∈ (B.groupedOwner label hsize (i,(c,t))).val at hm
  rw [he] at hm
  exact B.gap_avoids U.val j hi hm

theorem grouped_gap_cover (sigma : ℕ) (rows : Fin d → Finset (Fin d))
    (hrows : ∀ v w : MatrixBit d b, label v = label w → w.1 ∈ rows v.1)
    (U : BucketPattern M K) (v : MatrixBit d b)
    (hv : v ∈ ownedCoordinates (B.groupedOwner label hsize) U)
    (hn : v ∉ B.groupedNear label hsize sigma rows U) :
    ∃ j : B.GapIndex U.val, columnWindow sigma v.2.1 ⊆ B.gap U.val j := by
  have he : B.groupedOwner label hsize v = U := by simpa [ownedCoordinates] using hv
  apply B.interval_in_gap U.val _ (columnWindow_interval sigma v.2.1)
  intro c hc hmem
  apply hn
  apply Finset.mem_filter.mpr
  refine ⟨?_, he⟩
  rw [← he] at hmem
  obtain ⟨w, hw, hbw⟩ := (mem_occupiedBuckets label (fun v => B.bucket v.1) (label v) (B.bucket c)).mp hmem
  exact (B.mem_nearCoordinates b sigma rows v).mpr
    ⟨w.1, hrows v w hw.symm, c, hc, hbw.symm⟩

theorem grouped_gap_count (U : BucketPattern M K) :
    Fintype.card (B.GapIndex U.val) ≤ K + 1 :=
  (B.gap_count U.val).trans (Nat.add_le_add_right U.property.2 1)

end RowBuckets

end TransposeFollowup
