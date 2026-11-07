import TapeStorageRates.PartitionPadding
import TapeStorageRates.PacketExpansion
import LeanMachine.SlowIndex
import LeanMachine.FinitePartition

/-! # Separated index partitions at every integer length

Repeat a slowly selected block and record leftover coordinates as raw bits.
The same encoder is fixed before a source subset or confidence level is chosen.
-/

namespace TapeStorageRates.AllLengthPartitions

open Finset Filter DirectedRecovery MotionDepthCodes
set_option autoImplicit false
noncomputable section

variable (n : ℕ → ℕ) (Y : ℕ → Type)

abbrev level (M : ℕ) : ℕ := LeanMachine.SlowIndex.index n M
abbrev blockSize (M : ℕ) : ℕ := n (level n M)
abbrev copies (M : ℕ) : ℕ := M / blockSize n M
abbrev leftover (M : ℕ) : ℕ := M % blockSize n M
abbrev Coordinates (M : ℕ) : Type :=
  PartitionPadding.Coordinates (Fin (blockSize n M)) (copies n M) (leftover n M)
abbrev Labels (M : ℕ) : Type :=
  (Fin (copies n M) → Y (level n M)) × (Fin (leftover n M) → Bool)

def coordinateEquiv (M : ℕ) : Coordinates n M ≃ Fin M :=
  Fintype.equivFinOfCardEq (by
    simp only [Coordinates, PartitionPadding.card_coordinates, Fintype.card_fin]
    simpa only [copies, leftover, Nat.mul_comm, Nat.add_comm] using
      Nat.mod_add_div M (blockSize n M))

variable {n Y}

def relation (N : (j : ℕ) → Fin (n j) → Finset (Fin (n j))) (M : ℕ) :
    Fin M → Finset (Fin M) :=
  relabelRelation (coordinateEquiv n M)
    (PartitionPadding.relation (N (level n M)) (copies n M) (leftover n M))

def encoder (f : (j : ℕ) → (Fin (n j) → Bool) → Y j) (M : ℕ)
    (x : Fin M → Bool) : Labels n Y M :=
  PartitionPadding.encoder (f (level n M)) (x ∘ coordinateEquiv n M)

theorem isIndexCode (N : (j : ℕ) → Fin (n j) → Finset (Fin (n j)))
    (f : (j : ℕ) → (Fin (n j) → Bool) → Y j)
    (hf : ∀ j, IsIndexCode (N j) (f j)) (M : ℕ) :
    IsIndexCode (relation N M) (encoder f M) := by
  intro x y hxy q hhelp
  have h := PartitionPadding.isIndexCode (hf (level n M))
    (x ∘ coordinateEquiv n M) (y ∘ coordinateEquiv n M) hxy
    ((coordinateEquiv n M).symm q) (fun p hp =>
      hhelp (coordinateEquiv n M p) (mem_map.mpr ⟨p, hp, rfl⟩))
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h

open Classical in
theorem degree_le (N : (j : ℕ) → Fin (n j) → Finset (Fin (n j))) {Δ : ℕ}
    (hdeg : ∀ j v, (pairedIncidenceGraph (N j)).degree v ≤ Δ) (M : ℕ) :
    ∀ v, (pairedIncidenceGraph (relation N M)).degree v ≤ Δ := by
  intro v
  exact (degree_le_of_pairedEmbedding (relabelPorts (coordinateEquiv n M) _) v).trans
    (PartitionPadding.degree_le _ _ _ _ (hdeg _) _)

theorem paired_far (hn : ∀ j, 0 < n j)
    (N : (j : ℕ) → Fin (n j) → Finset (Fin (n j)))
    (hfar : ∀ r : ℕ, ∀ᶠ j in atTop, ∀ q,
      ¬ (pairedIncidenceGraph (N j)).edist (Sum.inl q) (Sum.inr q) ≤ r) :
    ∀ r : ℕ, ∀ᶠ M in atTop, ∀ q,
      ¬ (pairedIncidenceGraph (relation N M)).edist (Sum.inl q) (Sum.inr q) ≤ r := by
  intro r
  filter_upwards [(LeanMachine.SlowIndex.tendsto_index n).eventually (hfar r)] with M hM
  intro q hq
  apply PartitionPadding.paired_far (N (level n M)) (copies n M) (leftover n M) r
    (⟨0, hn _⟩ : Fin (blockSize n M)) hM ((coordinateEquiv n M).symm q)
  exact (AboveHalf.edist_map_le (relabelPorts (coordinateEquiv n M) _).toHom
    (Sum.inl q) (Sum.inr q)).trans hq

open Classical in
/-- Coordinate renaming is surjective on words and does not add labels. -/
theorem encoder_image_card_le (f : (j : ℕ) → (Fin (n j) → Bool) → Y j) (M : ℕ) :
    (univ.image (encoder f M)).card ≤
      (univ.image (f (level n M))).card ^ copies n M * 2 ^ leftover n M := by
  classical
  have hsub : univ.image (encoder f M) ⊆
      univ.image (PartitionPadding.encoder (c := copies n M) (a := leftover n M)
        (f (level n M))) := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := mem_image.mp hz
    exact mem_image_of_mem _ (mem_univ _)
  exact (card_le_card hsub).trans (PartitionPadding.encoder_image_card_le _ _ _)

open Classical in
/-- The overhead is at most a square root of the requested length, with
coefficient one because leftover coordinates are transmitted as raw bits. -/
theorem encoder_image_card_le_rpow (hn : ∀ j, 0 < n j)
    (f : (j : ℕ) → (Fin (n j) → Bool) → Y j) {ε : ℝ} (hε : 0 ≤ ε)
    (hcount : ∀ j, ((univ.image (f j)).card : ℝ) ≤ (2 : ℝ) ^ (ε * n j)) :
    ∀ᶠ M : ℕ in atTop, ((univ.image (encoder f M)).card : ℝ) ≤
      (2 : ℝ) ^ (ε * M + Real.sqrt M) := by
  filter_upwards [eventually_ge_atTop (n 0 * n 0)] with M hM
  have hrem : (leftover n M : ℝ) ≤ Real.sqrt M :=
    (Nat.cast_le.mpr (LeanMachine.SlowIndex.remainder_le_sqrt n hn hM)).trans
      (Real.nat_sqrt_le_real_sqrt (a := M))
  have htotal : (copies n M : ℝ) * blockSize n M + leftover n M = M := by
    have h : copies n M * blockSize n M + leftover n M = M := by
      simpa only [copies, leftover, Nat.mul_comm, Nat.add_comm] using
        Nat.mod_add_div M (blockSize n M)
    exact_mod_cast h
  calc
    _ ≤ ((univ.image (f (level n M))).card : ℝ) ^ copies n M *
        (2 : ℝ) ^ leftover n M := by exact_mod_cast encoder_image_card_le f M
    _ ≤ ((2 : ℝ) ^ (ε * blockSize n M)) ^ copies n M *
        (2 : ℝ) ^ leftover n M :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (hcount _) _)
        (by positivity)
    _ = (2 : ℝ) ^ (ε * blockSize n M * copies n M + leftover n M) := by
      rw [← Real.rpow_natCast _ (leftover n M), ← Real.rpow_mul_natCast (by norm_num),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      nlinarith [mul_nonneg hε (Nat.cast_nonneg (leftover n M) : (0 : ℝ) ≤ leftover n M)])

open Classical in
/-- Every cell, after restricting to any source subset, is still recovered
on the same full set of coordinates. -/
theorem fibre_storage (N : (j : ℕ) → Fin (n j) → Finset (Fin (n j)))
    (f : (j : ℕ) → (Fin (n j) → Bool) → Y j)
    (hf : ∀ j, IsIndexCode (N j) (f j)) (M : ℕ)
    (G : Finset (Fin M → Bool)) (z : Labels n Y M) :
    IsStorageCode (relation N M) (G.filter fun x => encoder f M x = z) := by
  intro x hx y hy q hhelp
  exact isIndexCode N f hf M x y
    ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) q hhelp

open Classical in
/-- At every sufficiently large integer length, one partition works for all
nonempty source subsets and all confidence parameters. -/
theorem rate_tail (hn : ∀ j, 0 < n j)
    (f : (j : ℕ) → (Fin (n j) → Bool) → Y j) {ε : ℝ} (hε : 0 ≤ ε)
    (hcount : ∀ j, ((univ.image (f j)).card : ℝ) ≤ (2 : ℝ) ^ (ε * n j)) :
    ∀ᶠ M : ℕ in atTop, ∀ G : Finset (Fin M → Bool), G.Nonempty → ∀ u : ℝ,
      ((G.filter fun x => Real.logb 2
        (G.filter fun y => encoder f M y = encoder f M x).card / M <
        Real.logb 2 G.card / M - (ε + Real.sqrt M / M) - u).card : ℝ) / G.card ≤
          (2 : ℝ) ^ (-u * M) := by
  filter_upwards [encoder_image_card_le_rpow hn f hε hcount,
    eventually_gt_atTop (0 : ℕ)] with M hM hpos
  intro G hG u
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hpos
  have hlabels : ((G.image (encoder f M)).card : ℝ) ≤
      (2 : ℝ) ^ (ε * M + Real.sqrt M) :=
    (Nat.cast_le.mpr (card_le_card (image_subset_image (subset_univ _)))).trans hM
  have h := LeanMachine.FinitePartition.normalized_tail G hG (encoder f M)
    (by norm_num : (1 : ℝ) < 2) hMR hlabels u
  rwa [add_div, mul_div_cancel_right₀ _ hMR.ne'] at h

open Classical in
/-- A fixed positive allowance absorbs the vanishing padding charge. -/
theorem encoder_image_card_le_double (hn : ∀ j, 0 < n j)
    (f : (j : ℕ) → (Fin (n j) → Bool) → Y j) {ε : ℝ} (hε : 0 < ε)
    (hcount : ∀ j, ((univ.image (f j)).card : ℝ) ≤ (2 : ℝ) ^ (ε * n j)) :
    ∀ᶠ M : ℕ in atTop, ((univ.image (encoder f M)).card : ℝ) ≤
      (2 : ℝ) ^ ((2 * ε) * M) := by
  filter_upwards [encoder_image_card_le_rpow hn f hε.le hcount,
    LeanMachine.SlowIndex.eventually_sqrt_le_mul hε] with M hM hroot
  exact hM.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith))

end
end TapeStorageRates.AllLengthPartitions
