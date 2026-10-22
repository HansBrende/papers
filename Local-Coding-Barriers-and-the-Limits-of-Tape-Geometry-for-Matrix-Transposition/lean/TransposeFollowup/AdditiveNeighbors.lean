import TransposeFollowup.IntegerNeighbors
import TransposeFollowup.CappedAdditiveDivision

/-! Replace neighbor-start division by at most n additions/comparisons.
Clipping the quotient at n loses no candidate with index below n. The loop
is an exact reference algorithm; its fixed native controller is still needed. -/

namespace TransposeFollowup
set_option autoImplicit false

def rangeCandidates (n s B : ℕ) : Finset (Fin n) :=
  ((Finset.Ico s (s + B + 1)).filter (fun j => j < n)).attach.image (fun j =>
    ⟨j.val, ((Finset.mem_filter (p := fun k : ℕ => k < n)).mp j.property).2⟩)

theorem mem_rangeCandidates {n : ℕ} (s B : ℕ) (j : Fin n) :
    j ∈ rangeCandidates n s B ↔ s ≤ j.val ∧ j.val < s + B + 1 := by
  constructor
  · intro hj
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hj
    have hv : x.val = j.val := congrArg Fin.val hx
    have hm := (Finset.mem_filter.mp x.property).1
    simpa only [Finset.mem_Ico, hv] using hm
  · intro hj
    let x : {v // v ∈ (Finset.Ico s (s + B + 1)).filter (fun k => k < n)} :=
      ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hj, j.isLt⟩⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, Fin.ext rfl⟩

theorem rangeCandidates_cap (n s B : ℕ) :
    rangeCandidates n (min n s) B = rangeCandidates n s B := by
  ext j
  rw [mem_rangeCandidates, mem_rangeCandidates]
  have hj := j.isLt
  omega

namespace RationalMobius
variable (F : RationalMobius)

def additiveNeighborStart {n : ℕ} (i : Fin n) : ℕ :=
  let L := F.imagePair (F.leftPair i)
  (quotientRun (repeatedAdd L.1 n) L.2 n).1

theorem additiveNeighborStart_eq {n : ℕ} (i : Fin n)
    (h : F.sourceLeft i < F.sourceRight i) :
    F.additiveNeighborStart i = min n (F.integerNeighborStart i) := by
  have hd := (F.imagePair_den_pos i h).1
  simp only [additiveNeighborStart, repeatedAdd_eq, quotientRun_eq _ _ hd,
    integerNeighborStart]

def additiveNeighborCandidates {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  if (F.leftPair i).1 * (F.rightPair i).2 < (F.rightPair i).1 * (F.leftPair i).2 then
    rangeCandidates n (F.additiveNeighborStart i) F.distortion
  else ∅

def additiveNeighbors {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  (F.additiveNeighborCandidates i).filter (fun j => F.integerOverlapTest i j = true)

theorem additiveNeighborCandidates_eq {n : ℕ} (i : Fin n) :
    F.additiveNeighborCandidates i = F.integerNeighborCandidates i := by
  unfold additiveNeighborCandidates integerNeighborCandidates
  split_ifs with h
  · change rangeCandidates n (F.additiveNeighborStart i) F.distortion =
      rangeCandidates n (F.integerNeighborStart i) F.distortion
    rw [F.additiveNeighborStart_eq i ((F.sourcePair_lt_iff i).mp h), rangeCandidates_cap]
  · rfl

theorem additiveNeighbors_eq {n : ℕ} (i : Fin n) : F.additiveNeighbors i = F.neighbors i := by
  rw [← F.integerNeighbors_eq i]
  unfold additiveNeighbors integerNeighbors
  rw [F.additiveNeighborCandidates_eq]

theorem additiveNeighborCandidates_card_le {n : ℕ} (i : Fin n) :
    (F.additiveNeighborCandidates i).card ≤ F.distortion + 1 := by
  rw [F.additiveNeighborCandidates_eq]
  exact F.integerNeighborCandidates_card_le i

theorem additiveTrial_bits {n : ℕ} (i : Fin n)
    (h : F.sourceLeft i < F.sourceRight i) (t : ℕ) (ht : t ≤ n) :
    (quotientRun (repeatedAdd (F.imagePair (F.leftPair i)).1 n)
      (F.imagePair (F.leftPair i)).2 t).2.natAbs.size ≤
      F.integerOperandConstant.size + 2 * (n + 1).size + 1 := by
  let L := F.imagePair (F.leftPair i)
  have hd : 0 < L.2 := (F.imagePair_den_pos i h).1
  have hb := quotientRun_bounds (repeatedAdd L.1 n) L.2 hd t
  have hD : L.2.natAbs ≤ F.integerOperandConstant * (n + 1) :=
    (F.endpointImagePairs_bounds i).2.1
  apply natSize_le_poly
  have hcast : L.2 ≤ (F.integerOperandConstant : ℤ) * (n + 1) := by
    have hD' : (L.2.natAbs : ℤ) ≤ (F.integerOperandConstant : ℤ) * (n + 1) := by
      exact_mod_cast hD
    exact (show L.2 ≤ (L.2.natAbs : ℤ) from Int.le_natAbs).trans hD'
  have hq : 0 ≤ (quotientRun (repeatedAdd L.1 n) L.2 t).2 := by omega
  have hbound : (quotientRun (repeatedAdd L.1 n) L.2 t).2 ≤
      (F.integerOperandConstant : ℤ) * (n + 1) ^ 2 := by
    calc
      _ ≤ ((t : ℤ) + 1) * L.2 := hb.2.2
      _ ≤ ((n : ℤ) + 1) * ((F.integerOperandConstant : ℤ) * (n + 1)) := by
        gcongr
      _ = _ := by ring
  have habs : ((quotientRun (repeatedAdd L.1 n) L.2 t).2.natAbs : ℤ) =
      (quotientRun (repeatedAdd L.1 n) L.2 t).2 := by
    rw [Int.natCast_natAbs, abs_of_nonneg hq]
  change (quotientRun (repeatedAdd L.1 n) L.2 t).2.natAbs ≤ _
  exact_mod_cast habs.trans_le hbound

end RationalMobius
end TransposeFollowup
