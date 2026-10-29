import LeanMachine.CyclicSelection
import LeanMachine.GapErosion
import LeanMachine.PartitionEnergy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

/-!
# Weighted gaps of an actual finite circular subdivision

Vertices and elementary edges use the same indices: edge `e` starts at vertex
`e` and ends at the next vertex. Each gap contains its starting edge and excludes
the edge starting at its next anchor. Arbitrary nonnegative real edge weights
allow nonuniform subdivisions of a real circle.
-/

namespace LeanMachine.WeightedCircularGap

open Finset CyclicSelection
open scoped BigOperators
noncomputable section

def edges (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (i : ℕ) : Finset ℕ :=
  arc N (point N S hS i) (gap N S hS i)

def weightedGap (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ e ∈ edges N S hS i, w e

def circumference (N : ℕ) (w : ℕ → ℝ) : ℝ := ∑ e ∈ range N, w e

def energy (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range S.card, weightedGap N S hS w i ^ 2

def area (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (w : ℕ → ℝ) : ℝ :=
  energy N S hS w / (2 * circumference N w ^ 2)

theorem cycle_pos {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSN : S ⊆ range N) :
    0 < N := by
  obtain ⟨s, hs⟩ := hS
  exact Nat.zero_lt_of_lt (mem_range.mp (hSN hs))

theorem edges_subset {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) (i : ℕ) : edges N S hS i ⊆ range N :=
  arc_subset (cycle_pos hS hSN)

theorem edges_card {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {i : ℕ} (hi : i < S.card) :
    (edges N S hS i).card = gap N S hS i :=
  arc_card (gap_le hS hSN hi)

theorem edges_lift {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {i e : ℕ} (hi : i < S.card)
    (he : e ∈ edges N S hS i) :
    ∃ q, e = q % N ∧ point N S hS i ≤ q ∧ q < point N S hS (i + 1) ∧
      q ∈ Ico (S.min' hS) (S.min' hS + N) := by
  obtain ⟨k, hk, rfl⟩ := mem_image.mp he
  have hk' := mem_range.mp hk
  have hlow := point_mono hS hSN (Nat.zero_le i)
  have hupp := point_mono hS hSN (show i + 1 ≤ S.card by omega)
  rw [point_zero] at hlow
  rw [point_card] at hupp
  unfold gap at hk'
  refine ⟨point N S hS i + k, rfl, by omega, by omega, ?_⟩
  simp only [mem_Ico]
  omega

theorem edges_pairwiseDisjoint {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) :
    (↑(range S.card) : Set ℕ).PairwiseDisjoint (edges N S hS) := by
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro e hei hej
  obtain ⟨qi, hqi, hli, hui, hri⟩ := edges_lift hS hSN (mem_range.mp hi) hei
  obtain ⟨qj, hqj, hlj, huj, hrj⟩ := edges_lift hS hSN (mem_range.mp hj) hej
  have heq := Nat.mod_injOn_Ico (S.min' hS) N hri hrj (hqi.symm.trans hqj)
  rcases lt_or_gt_of_ne hij with h | h
  · have := point_mono hS hSN (show i + 1 ≤ j by omega)
    omega
  · have := point_mono hS hSN (show j + 1 ≤ i by omega)
    omega

theorem biUnion_edges {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) : (range S.card).biUnion (edges N S hS) = range N := by
  have hsub : (range S.card).biUnion (edges N S hS) ⊆ range N := by
    intro e he
    obtain ⟨i, hi, hei⟩ := mem_biUnion.mp he
    exact edges_subset hS hSN i hei
  apply eq_of_subset_of_card_le hsub
  rw [card_biUnion (edges_pairwiseDisjoint hS hSN), card_range]
  calc
    N ≤ ∑ i ∈ range S.card, gap N S hS i := (sum_gap hS hSN).ge
    _ = ∑ i ∈ range S.card, (edges N S hS i).card :=
      sum_congr rfl fun _ hi => (edges_card hS hSN (mem_range.mp hi)).symm

/-- The index of the preceding anchor gap. The default outside the circle is
irrelevant; every actual edge has exactly one such index. -/
def edgeLabel (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (e : ℕ) : ℕ :=
  if h : ∃ i < S.card, e ∈ edges N S hS i then Classical.choose h else 0

theorem edgeLabel_spec {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {e : ℕ} (he : e < N) :
    edgeLabel N S hS e < S.card ∧ e ∈ edges N S hS (edgeLabel N S hS e) := by
  have heU : e ∈ (range S.card).biUnion (edges N S hS) := by
    rw [biUnion_edges hS hSN]
    exact mem_range.mpr he
  obtain ⟨i, hi, hei⟩ := mem_biUnion.mp heU
  have hex : ∃ i < S.card, e ∈ edges N S hS i := ⟨i, mem_range.mp hi, hei⟩
  simp only [edgeLabel, dite_eq_left hex]
  exact Classical.choose_spec hex

theorem edgeLabel_lt {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {e : ℕ} (he : e < N) : edgeLabel N S hS e < S.card :=
  (edgeLabel_spec hS hSN he).1

theorem edgeLabel_eq_of_mem {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {i e : ℕ} (hi : i < S.card) (he : e ∈ edges N S hS i) :
    edgeLabel N S hS e = i := by
  have heN := mem_range.mp (edges_subset hS hSN i he)
  obtain ⟨hi', he'⟩ := edgeLabel_spec hS hSN heN
  by_contra hne
  exact disjoint_left.mp
    (edges_pairwiseDisjoint hS hSN (mem_range.mpr hi') (mem_range.mpr hi) hne) he' he

theorem mem_edges_iff_label {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {i e : ℕ} (hi : i < S.card) :
    e ∈ edges N S hS i ↔ e < N ∧ edgeLabel N S hS e = i := by
  constructor
  · intro he
    exact ⟨mem_range.mp (edges_subset hS hSN i he), edgeLabel_eq_of_mem hS hSN hi he⟩
  · rintro ⟨he, rfl⟩
    exact (edgeLabel_spec hS hSN he).2

theorem edges_eq_filter {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {i : ℕ} (hi : i < S.card) :
    edges N S hS i = (range N).filter (fun e => edgeLabel N S hS e = i) := by
  ext e
  simp only [mem_edges_iff_label hS hSN hi, mem_filter, mem_range]

theorem label_image {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) : (range N).image (edgeLabel N S hS) = range S.card := by
  ext i
  constructor
  · intro hi
    obtain ⟨e, he, rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (edgeLabel_lt hS hSN (mem_range.mp he))
  · intro hi
    have hcard : 0 < (edges N S hS i).card := by
      rw [edges_card hS hSN (mem_range.mp hi)]
      exact gap_pos hS hSN (mem_range.mp hi)
    obtain ⟨e, he⟩ := card_pos.mp hcard
    exact mem_image.mpr ⟨e, edges_subset hS hSN i he,
      edgeLabel_eq_of_mem hS hSN (mem_range.mp hi) he⟩

theorem next_anchor_mem {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {i : ℕ} (hi : i < S.card) :
    point N S hS (i + 1) % N ∈ S := by
  by_cases hnext : i + 1 < S.card
  · have hm := point_mem (L := N) hS hnext
    rwa [Nat.mod_eq_of_lt (mem_range.mp (hSN hm))]
  · have hn : i + 1 = S.card := by omega
    have hm := S.min'_mem hS
    rw [hn, point_card, Nat.add_mod_left, Nat.mod_eq_of_lt (mem_range.mp (hSN hm))]
    exact hm

theorem forward_mod_add {N e t : ℕ} (he : e < N) (ht : t < N) :
    forward N e ((e + t) % N) = t := by
  have h := forward_rotate (L := N) e (show 0 < N by omega) ht
  simpa [Nat.mod_eq_of_lt he, forward] using h

/-- In the clockwise interval strictly after an edge and ending at another
edge, crossing no anchor keeps the same gap label. -/
theorem edgeLabel_eq_of_no_target_between {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {e f : ℕ} (he : e < N) (hf : f < N)
    (hno : ∀ z ∈ S, ¬(0 < forward N e z ∧ forward N e z ≤ forward N e f)) :
    edgeLabel N S hS e = edgeLabel N S hS f := by
  let i := edgeLabel N S hS e
  obtain ⟨hi, hei⟩ := edgeLabel_spec hS hSN he
  change i < S.card at hi
  change e ∈ edges N S hS i at hei
  obtain ⟨k, hk, hke⟩ := mem_image.mp hei
  have hk' := mem_range.mp hk
  let t := forward N e f
  have ht : t < N := forward_lt he hf
  have hmono := point_mono hS hSN (Nat.le_succ i)
  change point N S hS i ≤ point N S hS (i + 1) at hmono
  have hnext : point N S hS i + gap N S hS i = point N S hS (i + 1) := by
    unfold gap
    omega
  have hkt : k + t < gap N S hS i := by
    by_contra hkt
    let δ := gap N S hS i - k
    have hδpos : 0 < δ := by omega
    have hδle : δ ≤ t := by omega
    have hδN : δ < N := hδle.trans_lt ht
    let z := point N S hS (i + 1) % N
    have hz : z ∈ S := next_anchor_mem hS hSN hi
    have hzrepr : z = (e + δ) % N := by
      have heq : point N S hS i + k + δ = point N S hS (i + 1) := by omega
      dsimp [z]
      rw [← heq, Nat.add_mod, hke, Nat.mod_eq_of_lt hδN]
    have hdist : forward N e z = δ := by
      rw [hzrepr, forward_mod_add he hδN]
    exact hno z hz (by rw [hdist]; exact ⟨hδpos, hδle⟩)
  have hfi : f ∈ edges N S hS i := by
    apply mem_image.mpr
    refine ⟨k + t, mem_range.mpr hkt, ?_⟩
    rw [← Nat.add_assoc, Nat.add_mod, hke, Nat.mod_eq_of_lt ht]
    exact mod_add_forward he hf
  exact (edgeLabel_eq_of_mem hS hSN hi hfi).symm

theorem sum_weightedGap {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) (w : ℕ → ℝ) :
    ∑ i ∈ range S.card, weightedGap N S hS w i = circumference N w := by
  rw [circumference, ← biUnion_edges hS hSN, sum_biUnion (edges_pairwiseDisjoint hS hSN)]
  rfl

/-- Squared actual gap masses are exactly the energy of the partition by
preceding-anchor labels. No sign restriction on the weights is needed. -/
theorem energy_eq_partitionEnergy {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) (w : ℕ → ℝ) :
    energy N S hS w = PartitionEnergy.energy (range N) w (edgeLabel N S hS) := by
  rw [PartitionEnergy.energy_eq_sum_fibers, label_image hS hSN]
  unfold energy
  apply sum_congr rfl
  intro i hi
  rw [weightedGap, edges_eq_filter hS hSN (mem_range.mp hi)]

theorem energy_eq_pairSum {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) (w : ℕ → ℝ) :
    energy N S hS w = ∑ e ∈ range N, ∑ f ∈ range N,
      if edgeLabel N S hS e = edgeLabel N S hS f then w e * w f else 0 := by
  rw [energy_eq_partitionEnergy hS hSN]
  unfold PartitionEnergy.energy
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro f _
  by_cases h : edgeLabel N S hS e = edgeLabel N S hS f <;> simp only [h, ite_true, ite_false]

theorem weightedGap_nonneg {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {w : ℕ → ℝ} (hw : ∀ e < N, 0 ≤ w e) (i : ℕ) :
    0 ≤ weightedGap N S hS w i :=
  sum_nonneg fun _ he => hw _ (mem_range.mp (edges_subset hS hSN i he))

theorem circumference_nonneg {N : ℕ} {w : ℕ → ℝ} (hw : ∀ e < N, 0 ≤ w e) :
    0 ≤ circumference N w := sum_nonneg fun _ he => hw _ (mem_range.mp he)

theorem energy_nonneg (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (w : ℕ → ℝ) :
    0 ≤ energy N S hS w := sum_nonneg fun _ _ => sq_nonneg _

theorem area_nonneg (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (w : ℕ → ℝ) :
    0 ≤ area N S hS w := div_nonneg (energy_nonneg N S hS w) (by positivity)

theorem energy_le_circumference_sq {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {w : ℕ → ℝ} (hw : ∀ e < N, 0 ≤ w e) :
    energy N S hS w ≤ circumference N w ^ 2 := by
  have h := sum_sq_le_sq_sum_of_nonneg
    (s := range S.card) (fun i _ => weightedGap_nonneg hS hSN hw i)
  rwa [sum_weightedGap hS hSN] at h

theorem area_le_half {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {w : ℕ → ℝ} (hw : ∀ e < N, 0 ≤ w e) :
    area N S hS w ≤ 1 / 2 := by
  by_cases hzero : circumference N w = 0
  · simp [area, hzero]
  · have hpos : 0 < circumference N w :=
      lt_of_le_of_ne (circumference_nonneg hw) (Ne.symm hzero)
    apply (div_le_iff₀ (by positivity : 0 < 2 * circumference N w ^ 2)).mpr
    have := energy_le_circumference_sq hS hSN hw
    nlinarith

theorem weightedGap_one {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {i : ℕ} (hi : i < S.card) :
    weightedGap N S hS (fun _ => 1) i = (gap N S hS i : ℝ) := by
  simp only [weightedGap, sum_const, nsmul_eq_mul, mul_one, edges_card hS hSN hi]

theorem area_one {N : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSN : S ⊆ range N) :
    area N S hS (fun _ => 1) = GapErosion.pointArea (range S.card) (gap N S hS) N := by
  unfold area energy GapErosion.pointArea
  simp only [circumference, sum_const, card_range, nsmul_eq_mul, mul_one]
  congr 1
  exact sum_congr rfl fun _ hi => congrArg (· ^ 2) (weightedGap_one hS hSN (mem_range.mp hi))

end
end LeanMachine.WeightedCircularGap
