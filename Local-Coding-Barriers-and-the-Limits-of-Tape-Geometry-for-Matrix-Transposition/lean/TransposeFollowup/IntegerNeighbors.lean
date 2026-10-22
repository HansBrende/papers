import TransposeFollowup.IntegerOperandSize

/-! Integer division supplies the neighbor start on nonempty clipped cells.
Empty cells are discarded first. The resulting bounded integer enumeration
agrees with the earlier rational neighbor set for every grid size. -/

namespace TransposeFollowup
namespace RationalMobius

set_option autoImplicit false
variable (F : RationalMobius)

def integerNeighborStart {n : ℕ} (i : Fin n) : ℕ :=
  let L := F.imagePair (F.leftPair i)
  (((n : ℤ) * L.1) / L.2).toNat

theorem integerNeighborStart_eq {n : ℕ} (i : Fin n) (h : F.sourceLeft i < F.sourceRight i) :
    F.integerNeighborStart i = F.neighborStart i := by
  let L := F.imagePair (F.leftPair i)
  have hd : 0 < L.2 := (F.imagePair_den_pos i h).1
  have hdn : (L.2.toNat : ℤ) = L.2 := Int.toNat_of_nonneg hd.le
  have hdQ : (L.2.toNat : ℚ) = (L.2 : ℚ) := by exact_mod_cast hdn
  have he : (n : ℚ) * F.evalQ (F.sourceLeft i) =
      (((n : ℤ) * L.1 : ℤ) : ℚ) / (L.2.toNat : ℚ) := by
    rw [hdQ, ← F.leftImagePair_value i]
    simp only [Int.cast_mul, Int.cast_natCast]
    change (n : ℚ) * ((L.1 : ℚ) / L.2) = (n * L.1) / L.2
    ring
  rw [neighborStart, he, ← Int.floor_toNat, Rat.floor_intCast_div_natCast, hdn]
  rfl

def integerNeighborCandidates {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  if (F.leftPair i).1 * (F.rightPair i).2 < (F.rightPair i).1 * (F.leftPair i).2 then
    ((Finset.Ico (F.integerNeighborStart i) (F.integerNeighborStart i + F.distortion + 1)).filter
      (fun j => j < n)).attach.image (fun j =>
        (⟨j.val, ((Finset.mem_filter (p := fun k : ℕ => k < n)).mp j.property).2⟩ : Fin n))
  else ∅

def integerNeighbors {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  (F.integerNeighborCandidates i).filter (fun j => F.integerOverlapTest i j = true)

theorem integerNeighborCandidates_of_open {n : ℕ} (i : Fin n)
    (h : F.sourceLeft i < F.sourceRight i) :
    F.integerNeighborCandidates i = F.neighborCandidates i := by
  rw [integerNeighborCandidates, ite_eq_left ((F.sourcePair_lt_iff i).mpr h)]
  ext j
  rw [F.mem_neighborCandidates i j]
  constructor
  · intro hj
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hj
    have hv : x.val = j.val := congrArg Fin.val hx
    have hm := (Finset.mem_filter.mp x.property).1
    simpa only [Finset.mem_Ico, hv, F.integerNeighborStart_eq i h] using hm
  · intro hj
    have hi : F.integerNeighborStart i ≤ j.val ∧
        j.val < F.integerNeighborStart i + F.distortion + 1 := by
      rwa [F.integerNeighborStart_eq i h]
    let x : {v // v ∈ (Finset.Ico (F.integerNeighborStart i)
        (F.integerNeighborStart i + F.distortion + 1)).filter (fun k => k < n)} :=
      ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hi, j.isLt⟩⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, Fin.ext rfl⟩

theorem integerNeighborCandidates_of_closed {n : ℕ} (i : Fin n)
    (h : ¬F.sourceLeft i < F.sourceRight i) : F.integerNeighborCandidates i = ∅ := by
  rw [integerNeighborCandidates, ite_eq_right (fun hp => h ((F.sourcePair_lt_iff i).mp hp))]

theorem integerNeighbors_eq {n : ℕ} (i : Fin n) : F.integerNeighbors i = F.neighbors i := by
  by_cases h : F.sourceLeft i < F.sourceRight i
  · ext j
    simp only [integerNeighbors, F.integerNeighborCandidates_of_open i h, neighbors,
      Finset.mem_filter, F.integerOverlapTest_spec, F.overlapTest_spec]
  · ext j
    have hj : ¬F.bounded.Overlap i j := fun ho => h ((F.overlap_iff_endpoints i j).mp ho).1
    simp [integerNeighbors, F.integerNeighborCandidates_of_closed i h, F.mem_neighbors, hj]

theorem integerNeighborCandidates_card_le {n : ℕ} (i : Fin n) :
    (F.integerNeighborCandidates i).card ≤ F.distortion + 1 := by
  by_cases h : F.sourceLeft i < F.sourceRight i
  · rw [F.integerNeighborCandidates_of_open i h]
    exact F.neighborCandidates_card_le i
  · rw [F.integerNeighborCandidates_of_closed i h]
    simp

theorem integerNeighbors_card_le {n : ℕ} (i : Fin n) :
    (F.integerNeighbors i).card ≤ F.distortion + 1 := by
  rw [F.integerNeighbors_eq i]
  exact F.neighbors_card_le i

end RationalMobius
end TransposeFollowup
