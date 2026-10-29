import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Cyclic gap selection

Concrete finite-circle geometry for common cut-and-orientation selections.
The anchor enumeration is the increasing enumeration supplied by Mathlib.
-/

namespace LeanMachine.CyclicSelection

open Finset
noncomputable section

/-- Circular interval of `ell` consecutive integer coordinates. -/
def arc (L a ell : ℕ) : Finset ℕ :=
  (range ell).image fun k => (a + k) % L

/-- Clockwise rank in the total order whose first point is `cut`. -/
def rank (L cut z : ℕ) : ℤ := ((z : ℤ) - cut) % L

theorem rank_rotate (L a t k : ℕ) :
    rank L ((a + t) % L) ((a + k) % L) = ((k : ℤ) - t) % L := by
  unfold rank
  simp only [Int.natCast_mod, Nat.cast_add]
  rw [← Int.sub_emod]
  congr 1
  ring

theorem rank_lt {L cut z : ℕ} (hL : 0 < L) : rank L cut z < L := by
  exact Int.emod_lt_of_pos _ (by exact_mod_cast hL)

theorem rank_nonneg {L cut z : ℕ} (hL : 0 < L) : 0 ≤ rank L cut z := by
  exact Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hL))

def forward (L a z : ℕ) : ℕ := if a ≤ z then z - a else L + z - a

theorem forward_of_le {L a z : ℕ} (h : a ≤ z) : forward L a z = z - a := ite_eq_left h

theorem forward_of_gt {L a z : ℕ} (h : z < a) : forward L a z = L + z - a :=
  ite_eq_right (by omega)

theorem rank_eq_forward {L a z : ℕ} (ha : a < L) (hz : z < L) :
    rank L a z = forward L a z := by
  unfold rank forward
  split_ifs with haz
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · rw [← Int.add_emod_left (L : ℤ) ((z : ℤ) - a),
      Int.emod_eq_of_lt (by omega) (by omega)]
    omega

theorem forward_lt {L a z : ℕ} (ha : a < L) (hz : z < L) : forward L a z < L := by
  unfold forward
  split_ifs <;> omega

theorem mod_add_forward {L a z : ℕ} (ha : a < L) (hz : z < L) :
    (a + forward L a z) % L = z := by
  unfold forward
  split_ifs with h
  · have : a + (z - a) = z := by omega
    rw [this, Nat.mod_eq_of_lt hz]
  · have : a + (L + z - a) = L + z := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hz]

theorem forward_rotate {L s d : ℕ} (a : ℕ) (hs : s < L) (hd : d < L) :
    forward L ((a + s) % L) ((a + d) % L) = forward L s d := by
  have hL : 0 < L := by omega
  have h := rank_rotate L a s d
  change rank L ((a + s) % L) ((a + d) % L) = rank L s d at h
  rw [rank_eq_forward (Nat.mod_lt _ hL) (Nat.mod_lt _ hL), rank_eq_forward hs hd] at h
  exact_mod_cast h

/-- Circular radius overcover of a set of anchors. -/
def covered (L : ℕ) (S : Finset ℕ) (r z : ℕ) : Prop :=
  ∃ a ∈ S, forward L a z ≤ r ∨ forward L z a ≤ r

def overcover (L : ℕ) (S : Finset ℕ) (r : ℕ) : Finset ℕ := by
  classical
  exact (range L).filter (covered L S r)

theorem mem_overcover {L r z : ℕ} {S : Finset ℕ} :
    z ∈ overcover L S r ↔ z < L ∧ covered L S r z := by
  classical
  simp [overcover]

theorem overcover_subset (L : ℕ) (S : Finset ℕ) (r : ℕ) :
    overcover L S r ⊆ range L := by
  classical
  exact filter_subset _ _

theorem anchors_subset_overcover {L r : ℕ} {S : Finset ℕ} (hSL : S ⊆ range L) :
    S ⊆ overcover L S r := by
  intro a ha
  refine mem_overcover.mpr ⟨mem_range.mp (hSL ha), a, ha, Or.inl ?_⟩
  simp [forward]

theorem overcover_nonempty {L r : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) : (overcover L S r).Nonempty :=
  hS.mono (anchors_subset_overcover hSL)

theorem covered_of_dist_le {L r z a : ℕ} {S : Finset ℕ}
    (ha : a ∈ S) (hd : Nat.dist z a ≤ r) : covered L S r z := by
  refine ⟨a, ha, ?_⟩
  by_cases h : a ≤ z
  · left
    simpa [forward, h, Nat.dist_eq_sub_of_le_right h] using hd
  · right
    have h' : z ≤ a := by omega
    simpa [forward, h', Nat.dist_eq_sub_of_le h'] using hd

theorem arc_subset {L a ell : ℕ} (hL : 0 < L) : arc L a ell ⊆ range L := by
  intro z hz
  rcases mem_image.mp hz with ⟨k, hk, rfl⟩
  exact mem_range.mpr (Nat.mod_lt _ hL)

theorem arc_card {L a ell : ℕ} (hell : ell ≤ L) : (arc L a ell).card = ell := by
  rw [arc, card_image_of_injOn, card_range]
  intro i hi j hj heq
  have hi' : a + i ∈ Ico a (a + L) := by
    simp only [mem_Ico]
    have := mem_range.mp hi
    omega
  have hj' : a + j ∈ Ico a (a + L) := by
    simp only [mem_Ico]
    have := mem_range.mp hj
    omega
  have := Nat.mod_injOn_Ico a L hi' hj' heq
  omega

/-- Increasing anchors, extended constantly after one circuit. -/
noncomputable def point (L : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (i : ℕ) : ℕ :=
  if hi : i < S.card then S.orderEmbOfFin rfl ⟨i, hi⟩ else L + S.min' hS

def gap (L : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (i : ℕ) : ℕ :=
  point L S hS (i + 1) - point L S hS i

theorem point_mem {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty) {i : ℕ}
    (hi : i < S.card) : point L S hS i ∈ S := by
  simp only [point, dite_eq_left hi]
  exact S.orderEmbOfFin_mem rfl _

theorem point_zero (L : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    point L S hS 0 = S.min' hS := by
  simp only [point, dite_eq_left (card_pos.mpr hS)]
  exact S.orderEmbOfFin_zero rfl _

theorem point_card (L : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    point L S hS S.card = L + S.min' hS := by
  simp [point]

theorem point_mono {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) : Monotone (point L S hS) := by
  intro i j hij
  unfold point
  split_ifs with hi hj hj
  · exact (S.orderEmbOfFin rfl).monotone (show (⟨i, hi⟩ : Fin S.card) ≤ ⟨j, hj⟩ from hij)
  · have hx : S.orderEmbOfFin rfl ⟨i, hi⟩ < L :=
      mem_range.mp (hSL (S.orderEmbOfFin_mem rfl _))
    omega
  · omega
  · rfl

theorem point_strict {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i j : ℕ} (hij : i < j) (hj : j ≤ S.card) :
    point L S hS i < point L S hS j := by
  have hi : i < S.card := lt_of_lt_of_le hij hj
  by_cases hj' : j < S.card
  · simp only [point, dite_eq_left hi, dite_eq_left hj']
    exact (S.orderEmbOfFin rfl).strictMono hij
  · have hje : j = S.card := by omega
    rw [hje, point_card]
    have hx : point L S hS i < L := mem_range.mp (hSL (point_mem hS hi))
    omega

theorem gap_pos {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i : ℕ} (hi : i < S.card) : 0 < gap L S hS i := by
  exact Nat.sub_pos_of_lt (point_strict hS hSL (by omega) (by omega))

theorem sum_gap {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) : ∑ i ∈ range S.card, gap L S hS i = L := by
  simp only [gap]
  rw [sum_range_tsub (point_mono hS hSL), point_card, point_zero]
  omega

theorem gap_le {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i : ℕ} (hi : i < S.card) : gap L S hS i ≤ L := by
  have hlow := point_mono hS hSL (Nat.zero_le i)
  have hupp := point_mono hS hSL (show i + 1 ≤ S.card by omega)
  rw [point_zero] at hlow
  rw [point_card] at hupp
  unfold gap
  omega

theorem exists_point_eq {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty) {a : ℕ}
    (ha : a ∈ S) : ∃ i < S.card, point L S hS i = a := by
  let i := (S.orderIsoOfFin rfl).symm ⟨a, ha⟩
  refine ⟨i, i.isLt, ?_⟩
  simp only [point, dite_eq_left i.isLt]
  change ((S.orderIsoOfFin rfl) i).val = a
  exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨a, ha⟩)

/-- No anchor lies strictly between consecutive anchors in clockwise order. -/
theorem anchor_offset_zero_or_gap_le {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i a : ℕ} (hi : i < S.card) (ha : a ∈ S) :
    forward L (point L S hS i) a = 0 ∨
      gap L S hS i ≤ forward L (point L S hS i) a := by
  obtain ⟨k, hk, hka⟩ := exists_point_eq (L := L) hS ha
  subst a
  by_cases hki : k = i
  · subst k
    simp [forward]
  · right
    by_cases hik : i < k
    · have hle := point_mono hS hSL (Nat.le_of_lt hik)
      have hnext := point_mono hS hSL (show i + 1 ≤ k by omega)
      simp only [forward, ite_eq_left hle, gap]
      omega
    · have hlt := point_strict hS hSL (show k < i by omega) (Nat.le_of_lt hi)
      have hlow := point_mono hS hSL (Nat.zero_le k)
      have hupp := point_mono hS hSL (show i + 1 ≤ S.card by omega)
      rw [point_zero] at hlow
      rw [point_card] at hupp
      simp only [forward, ite_eq_right (by omega : ¬point L S hS i ≤ point L S hS k), gap]
      omega

/-- Interior surviving deletion of `r` coordinates at each end of an anchor gap. -/
def erodedArc (L : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (r i : ℕ) : Finset ℕ :=
  arc L (point L S hS i + r + 1) (gap L S hS i - 1 - 2 * r)

theorem erodedArc_uncovered {L r : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i z : ℕ} (hi : i < S.card)
    (hz : z ∈ erodedArc L S hS r i) : ¬covered L S r z := by
  rcases mem_image.mp hz with ⟨k, hk, rfl⟩
  have hk' := mem_range.mp hk
  have hgap := gap_le hS hSL hi
  have hs : r + 1 + k < L := by omega
  have hsr : r < r + 1 + k := by omega
  have hsg : r + 1 + k + r < gap L S hS i := by omega
  have hp : point L S hS i < L := mem_range.mp (hSL (point_mem hS hi))
  rintro ⟨a, ha, hcover⟩
  have haL : a < L := mem_range.mp (hSL ha)
  let d := forward L (point L S hS i) a
  have hd : d < L := forward_lt hp haL
  have had : (point L S hS i + d) % L = a := mod_add_forward hp haL
  have hdf := anchor_offset_zero_or_gap_le hS hSL hi ha
  change d = 0 ∨ gap L S hS i ≤ d at hdf
  have hadd : point L S hS i + r + 1 + k = point L S hS i + (r + 1 + k) := by omega
  have h1 : forward L a ((point L S hS i + r + 1 + k) % L) =
      forward L d (r + 1 + k) := by
    calc
      _ = forward L ((point L S hS i + d) % L)
          ((point L S hS i + (r + 1 + k)) % L) := by rw [had, hadd]
      _ = _ := forward_rotate _ hd hs
  have h2 : forward L ((point L S hS i + r + 1 + k) % L) a =
      forward L (r + 1 + k) d := by
    calc
      _ = forward L ((point L S hS i + (r + 1 + k)) % L)
          ((point L S hS i + d) % L) := by rw [had, hadd]
      _ = _ := forward_rotate _ hs hd
  rw [h1, h2] at hcover
  rcases hdf with hd0 | hdg
  · rw [hd0, forward_of_le (by omega : 0 ≤ r + 1 + k),
      forward_of_gt (by omega : 0 < r + 1 + k)] at hcover
    omega
  · rw [forward_of_gt (by omega : r + 1 + k < d),
      forward_of_le (by omega : r + 1 + k ≤ d)] at hcover
    omega

theorem erodedArc_card {L r : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i : ℕ} (hi : i < S.card) :
    (erodedArc L S hS r i).card = gap L S hS i - 1 - 2 * r := by
  apply arc_card
  have := gap_le hS hSL hi
  omega

theorem erodedArc_disjoint_overcover {L r : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i : ℕ} (hi : i < S.card) :
    Disjoint (erodedArc L S hS r i) (overcover L S r) := by
  apply disjoint_left.mpr
  intro z hz hcover
  exact erodedArc_uncovered hS hSL hi hz (mem_overcover.mp hcover).2

theorem erodedArc_lift {L r : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i z : ℕ} (hi : i < S.card)
    (hz : z ∈ erodedArc L S hS r i) :
    ∃ q, z = q % L ∧ point L S hS i < q ∧ q < point L S hS (i + 1) ∧
      q ∈ Ico (S.min' hS) (S.min' hS + L) := by
  rcases mem_image.mp hz with ⟨k, hk, rfl⟩
  have hk' := mem_range.mp hk
  have hmono := point_mono hS hSL (Nat.le_succ i)
  have hlow := point_mono hS hSL (Nat.zero_le i)
  have hupp := point_mono hS hSL (show i + 1 ≤ S.card by omega)
  rw [point_zero] at hlow
  rw [point_card] at hupp
  unfold gap at hk'
  refine ⟨point L S hS i + r + 1 + k, rfl, by omega, by omega, ?_⟩
  simp only [mem_Ico]
  omega

theorem erodedArc_pairwiseDisjoint {L r : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) :
    (↑(range S.card) : Set ℕ).PairwiseDisjoint (erodedArc L S hS r) := by
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro z hzi hzj
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  obtain ⟨qi, hqi, hli, hui, hri⟩ := erodedArc_lift hS hSL hi' hzi
  obtain ⟨qj, hqj, hlj, huj, hrj⟩ := erodedArc_lift hS hSL hj' hzj
  have heq : qi = qj := Nat.mod_injOn_Ico (S.min' hS) L hri hrj (hqi.symm.trans hqj)
  rcases lt_or_gt_of_ne hij with h | h
  · have := point_mono hS hSL (show i + 1 ≤ j by omega)
    omega
  · have := point_mono hS hSL (show j + 1 ≤ i by omega)
    omega

def activeGaps (L : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (r : ℕ) : Finset ℕ :=
  (range S.card).filter fun i => 0 < gap L S hS i - 1 - 2 * r

theorem sum_active_lengths_add_one_le {L r : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) :
    (∑ i ∈ activeGaps L S hS r, (gap L S hS i - 1 - 2 * r + 1)) ≤ L := by
  calc
    _ ≤ ∑ i ∈ activeGaps L S hS r, gap L S hS i := by
      apply sum_le_sum
      intro i hi
      have := (mem_filter.mp hi).2
      omega
    _ ≤ ∑ i ∈ range S.card, gap L S hS i :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
    _ = L := sum_gap hS hSL
end
end LeanMachine.CyclicSelection
