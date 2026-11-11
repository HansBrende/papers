import AdaptiveTransfer.TransferClock

/-! Computed whole-batch guards for the actual aligned clock. The extra
terminal complete batch and the final partial drain are included. A source
vertex charges at most four physical batches, with endpoint cuts included. -/
namespace AdaptiveTransfer.TransferGuards
open Finset TapeStorageRates AdaptiveTransfer.TransferClock

noncomputable def affectedBatches (s t b : ℕ) : Finset ℕ :=
  (range (t / s + 2)).filter fun j => min (j * s) (t - 1) ≤ b ∧
    b ≤ min ((j + 1) * s) (t - 1)

noncomputable def batchCells (s t j : ℕ) : Finset ℕ :=
  Ico (batchLength s * j) (min (batchLength s * (j + 1)) (alignedTime s t))

noncomputable def batchGuard (s t : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.biUnion fun b => (affectedBatches s t b).biUnion (batchCells s t)

theorem affectedBatches_card_le {s t b : ℕ} (hs : 1 ≤ s) (hb : b < t) :
    (affectedBatches s t b).card ≤ 4 := by
  have hsub : affectedBatches s t b ⊆ Icc (b / s - 1) (b / s + 2) := by
    intro j hj
    obtain ⟨hjr, hlo, hhi⟩ := mem_filter.mp hj
    have hjT : j < t / s + 2 := mem_range.mp hjr
    have hbupper : b ≤ (j + 1) * s := hhi.trans (min_le_left _ _)
    have hlow : b / s ≤ j + 1 := by
      have hh := Nat.div_le_div_right (c := s) hbupper
      simpa only [Nat.mul_div_cancel _ (by omega : 0 < s)] using hh
    have hhigh : j ≤ b / s + 2 := by
      by_cases he : b = t - 1
      · have htb : t ≤ b + s := by omega
        have hh := Nat.div_le_div_right (c := s) htb
        have hediv : (b + s) / s = b / s + 1 := by simp [Nat.add_div_right, (by omega : 0 < s)]
        rw [hediv] at hh
        omega
      · have hjs : j * s ≤ b := (min_le_iff.mp hlo).resolve_right (by omega)
        have hh := Nat.div_le_div_right (c := s) hjs
        have hjb : j ≤ b / s := by simpa only [Nat.mul_div_cancel _ (by omega : 0 < s)] using hh
        omega
    exact mem_Icc.mpr ⟨by omega, hhigh⟩
  exact (card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)

theorem batchCells_card_le (s t j : ℕ) : (batchCells s t j).card ≤ batchLength s := by
  simp only [batchCells, Nat.card_Ico, Nat.mul_add, Nat.mul_one]
  have hh := min_le_left (batchLength s * j + batchLength s) (alignedTime s t)
  omega

theorem batchGuard_card_le {s t : ℕ} (hs : 1 ≤ s) (B : Finset ℕ)
    (hB : ∀ b ∈ B, b < t) : (batchGuard s t B).card ≤ 4 * batchLength s * B.card := by
  classical
  unfold batchGuard
  calc
    _ ≤ ∑ b ∈ B, ((affectedBatches s t b).biUnion (batchCells s t)).card := card_biUnion_le
    _ ≤ ∑ b ∈ B, 4 * batchLength s := by
      apply sum_le_sum
      intro b hb
      calc
        _ ≤ ∑ j ∈ affectedBatches s t b, (batchCells s t j).card := card_biUnion_le
        _ ≤ ∑ _j ∈ affectedBatches s t b, batchLength s :=
          sum_le_sum fun j _ => batchCells_card_le s t j
        _ = (affectedBatches s t b).card * batchLength s := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ (affectedBatches_card_le hs (hB b hb))
    _ = _ := by simp [Nat.mul_comm]

theorem own_batch_bounds (s u : ℕ) :
    batchLength s * (u / batchLength s) ≤ u ∧ u < batchLength s * (u / batchLength s + 1) := by
  constructor
  · simpa only [Nat.mul_comm] using Nat.div_mul_le_self u (batchLength s)
  · have he : batchLength s * (u / batchLength s) + u % batchLength s = u := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod' u (batchLength s)
    have hr := Nat.mod_lt u (batchLength_pos s)
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem live_batch_index {s t u : ℕ} (hu : u < alignedTime s t) :
    u / batchLength s < t / s + 2 := by
  have hb := (own_batch_bounds s u).1
  have hs : s < batchLength s := by unfold batchLength; omega
  unfold alignedTime at hu
  change u < batchLength s * (t / s + 1) + s at hu
  by_contra hn
  have hh := Nat.mul_le_mul_left (batchLength s) (show t / s + 2 ≤ u / batchLength s by omega)
  nlinarith

theorem live_mem_own_batch {s t u : ℕ} (hu : u < alignedTime s t) :
    u ∈ batchCells s t (u / batchLength s) :=
  mem_Ico.mpr ⟨(own_batch_bounds s u).1, lt_min (own_batch_bounds s u).2 hu⟩

theorem mem_batchGuard_of_between {s t u b : ℕ} {B : Finset ℕ}
    (hu : u < alignedTime s t) (hb : b ∈ B)
    (hlo : min ((u / batchLength s) * s) (t - 1) ≤ b)
    (hhi : b ≤ sourceClock s t u) : u ∈ batchGuard s t B := by
  apply mem_biUnion.mpr
  refine ⟨b, hb, mem_biUnion.mpr ⟨u / batchLength s, ?_, live_mem_own_batch hu⟩⟩
  exact mem_filter.mpr ⟨mem_range.mpr (live_batch_index hu), hlo, hhi⟩

/-- Every projected endpoint cut marks its complete physical batch. -/
theorem endpoint_in_batchGuard {s t u : ℕ} {B : Finset ℕ}
    (hu : u < alignedTime s t) (hb : sourceClock s t u ∈ B) : u ∈ batchGuard s t B := by
  apply mem_batchGuard_of_between hu hb _ le_rfl
  exact min_le_min (Nat.mul_le_mul_right s (Nat.le_succ _)) le_rfl

/-- A surviving physical state edge has its entire closed source-spine
interval disjoint from the source cut. -/
theorem state_interval_in_batchGuard {s t u v b : ℕ} {B : Finset ℕ}
    (hu : u < alignedTime s t) (hv : v + 1 = u) (hb : b ∈ B)
    (hlo : sourceClock s t v ≤ b) (hhi : b ≤ sourceClock s t u) : u ∈ batchGuard s t B := by
  apply mem_batchGuard_of_between hu hb _ hhi
  have hj : u / batchLength s ≤ v / batchLength s + 1 := by
    have hvb := (own_batch_bounds s v).2
    have hh := Nat.div_le_div_right (c := batchLength s)
      (show u ≤ (v / batchLength s + 1) * batchLength s by nlinarith)
    simpa only [Nat.mul_div_cancel _ (batchLength_pos s)] using hh
  exact (min_le_min (Nat.mul_le_mul_right s hj) le_rfl).trans hlo

end AdaptiveTransfer.TransferGuards
