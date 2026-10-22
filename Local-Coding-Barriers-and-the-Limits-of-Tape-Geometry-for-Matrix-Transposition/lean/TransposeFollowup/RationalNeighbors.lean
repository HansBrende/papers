import TransposeFollowup.RationalOverlapTest

/-! Enumerate only a fixed number of possible target cells, then run the exact
rational overlap test. No scan over all n target indices occurs in the definition. -/

namespace TransposeFollowup
namespace RationalMobius

open Set
set_option autoImplicit false

variable (F : RationalMobius)

def neighborStart {n : ℕ} (i : Fin n) : ℕ := ⌊(n : ℚ) * F.evalQ (F.sourceLeft i)⌋₊

def neighborCandidates {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  ((Finset.Ico (F.neighborStart i) (F.neighborStart i + F.distortion + 1)).filter
    (fun j => j < n)).attach.image (fun j =>
      (⟨j.val, ((Finset.mem_filter (p := fun k : ℕ => k < n)).mp j.property).2⟩ : Fin n))

def neighbors {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  (F.neighborCandidates i).filter (fun j => F.overlapTest i j = true)

theorem neighborStart_real {n : ℕ} (i : Fin n) :
    F.neighborStart i = ⌊(n : ℝ) * F.eval (F.sourceLeft i : ℝ)⌋₊ := by
  have hcast (q : ℚ) : ⌊(q : ℝ)⌋₊ = ⌊q⌋₊ := by
    simp only [← Int.floor_toNat, Rat.floor_cast]
  rw [neighborStart, ← hcast]
  congr 1
  simp only [Rat.cast_mul, Rat.cast_natCast, F.eval_cast]

theorem mem_neighborCandidates {n : ℕ} (i j : Fin n) :
    j ∈ F.neighborCandidates i ↔
      F.neighborStart i ≤ j.val ∧ j.val < F.neighborStart i + F.distortion + 1 := by
  unfold neighborCandidates
  constructor
  · intro hj
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hj
    have hv : x.val = j.val := congrArg Fin.val hx
    have hm := (Finset.mem_filter.mp x.property).1
    simpa only [hv, Finset.mem_Ico] using hm
  · intro hj
    let x : {v // v ∈ (Finset.Ico (F.neighborStart i)
        (F.neighborStart i + F.distortion + 1)).filter (fun k => k < n)} :=
      ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hj, j.isLt⟩⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, Fin.ext rfl⟩

theorem overlap_in_candidates {n : ℕ} {i j : Fin n} (he : F.bounded.Overlap i j) :
    j ∈ F.neighborCandidates i := by
  obtain ⟨x, hxd, hxi, hxj⟩ := he
  change x ∈ Ioo (F.lo : ℝ) F.hi at hxd
  change InGridCell j (F.eval x) at hxj
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  have hix : (i.val : ℝ) / n < x := (div_lt_iff₀ hn).mpr (by simpa [mul_comm] using hxi.1)
  have hLx : (F.sourceLeft i : ℝ) < x := by rw [F.sourceLeft_cast]; exact max_lt hxd.1 hix
  have hlo : (F.lo : ℝ) ≤ F.sourceLeft i := by rw [F.sourceLeft_cast]; exact le_max_left _ _
  have hL : (F.sourceLeft i : ℝ) ∈ Icc (F.lo : ℝ) F.hi := ⟨hlo, hLx.le.trans hxd.2.le⟩
  have hx : x ∈ Icc (F.lo : ℝ) F.hi := Ioo_subset_Icc_self hxd
  have hFx := F.strictMonoOn_eval hL hx hLx
  have hbound := F.forward_bound hx hL
  rw [abs_of_pos (sub_pos.mpr hFx), abs_of_pos (sub_pos.mpr hLx)] at hbound
  have hLindex : (i.val : ℝ) ≤ (F.sourceLeft i : ℝ) * n := by
    apply (div_le_iff₀ hn).mp
    rw [F.sourceLeft_cast]
    exact le_max_right _ _
  have hspan : (n : ℝ) * (x - F.sourceLeft i) ≤ 1 := by
    have := hxi.2
    nlinarith
  have hs := mul_le_mul_of_nonneg_left hbound hn.le
  have hb := mul_le_mul_of_nonneg_left hspan (Nat.cast_nonneg F.distortion : (0 : ℝ) ≤ F.distortion)
  have htarget : (n : ℝ) * F.eval x ≤ n * F.eval (F.sourceLeft i) + F.distortion := by
    nlinarith only [hs, hb]
  apply (F.mem_neighborCandidates i j).mpr
  rw [F.neighborStart_real]
  constructor
  · apply Nat.lt_succ_iff.mp
    apply (Nat.floor_lt' (Nat.succ_ne_zero j.val)).mpr
    have hmul := mul_lt_mul_of_pos_left hFx hn
    have := hxj.2
    push_cast
    linarith
  · have hf := Nat.lt_floor_add_one ((n : ℝ) * F.eval (F.sourceLeft i))
    have hj := hxj.1
    have hr : (j.val : ℝ) <
        (⌊(n : ℝ) * F.eval (F.sourceLeft i)⌋₊ + F.distortion + 1 : ℕ) := by
      push_cast
      linarith
    exact_mod_cast hr

theorem mem_neighbors {n : ℕ} (i j : Fin n) :
    j ∈ F.neighbors i ↔ F.bounded.Overlap i j := by
  rw [neighbors, Finset.mem_filter, F.overlapTest_spec]
  exact ⟨And.right, fun h => ⟨F.overlap_in_candidates h, h⟩⟩

theorem neighborCandidates_card_le {n : ℕ} (i : Fin n) :
    (F.neighborCandidates i).card ≤ F.distortion + 1 := by
  unfold neighborCandidates
  calc
    _ ≤ (((Finset.Ico (F.neighborStart i) (F.neighborStart i + F.distortion + 1)).filter
        (fun j => j < n)).attach).card := Finset.card_image_le
    _ = ((Finset.Ico (F.neighborStart i) (F.neighborStart i + F.distortion + 1)).filter
        (fun j => j < n)).card := Finset.card_attach
    _ ≤ (Finset.Ico (F.neighborStart i) (F.neighborStart i + F.distortion + 1)).card :=
      Finset.card_filter_le _ _
    _ = F.distortion + 1 := by simp only [Nat.card_Ico]; omega

theorem neighbors_card_le {n : ℕ} (i : Fin n) :
    (F.neighbors i).card ≤ F.distortion + 1 :=
  (Finset.card_filter_le _ _).trans (F.neighborCandidates_card_le i)

end RationalMobius
end TransposeFollowup
