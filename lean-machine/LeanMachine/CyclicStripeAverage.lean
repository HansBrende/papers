import LeanMachine.CyclicArcSelection
import LeanMachine.SelectionAverage
import LeanMachine.PeriodicStripe
import LeanMachine.GapErosion

/-! Sharp per-column selection averages for actual transpose stripes and cyclic source gaps. -/

namespace LeanMachine.CyclicStripeAverage

open Finset CyclicSelection PeriodicStripe

noncomputable section

/-- Sum pointwise safe-order credits on disjoint regions using one common experiment set. -/
theorem sum_credit_le_selectingOrders {ι : Type*}
    (L : ℕ) (D T : Finset ℕ) (I : Finset ι) (A : ι → Finset ℕ) (credit : ι → ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint A)
    (hcredit : ∀ i ∈ I, ∀ z ∈ D ∩ A i,
      credit i ≤ (selectingOrders L T z).card) :
    (∑ i ∈ I, credit i * (D ∩ A i).card) ≤
      ∑ z ∈ D, (selectingOrders L T z).card := by
  classical
  let E : Finset (ℕ × Bool) := (range L) ×ˢ univ
  let chosen := fun e => D.filter (fun z => e ∈ selectingOrders L T z)
  have hp (z : ℕ) (hz : z ∈ D) :
      SelectionAverage.pointCount E chosen z = (selectingOrders L T z).card := by
    unfold SelectionAverage.pointCount
    congr 1
    simp only [chosen, mem_filter, hz, true_and]
    rw [filter_mem_eq_inter, inter_eq_right]
    exact filter_subset _ _
  have h := SelectionAverage.sum_credit_mul_card_inter_le E D chosen I A credit hdisj
    (fun i hi z hz => by rw [hp z (mem_inter.mp hz).1]; exact hcredit i hi z hz)
  rw [SelectionAverage.sum_card_inter_eq_sum_pointCount] at h
  exact h.trans_eq (sum_congr rfl hp)

/-- The actual circular source gaps yield the claimed selection average on each
transpose column, with the sharp periodic-stripe error. -/
theorem erodedArea_lower {d b j r : ℕ} (hd : 0 < d) (hb : 0 < b) (hj : j < d)
    (S : Finset ℕ) (hS : S.Nonempty) (hSL : S ⊆ range (d * (d * b))) :
    (d * b : ℝ) * GapErosion.erodedArea (range S.card)
        (gap (d * (d * b)) S hS) (d * (d * b)) r -
      (b : ℝ) * (1 - 1 / d) / 2 ≤
        (∑ z ∈ stripe d b j,
          ((selectingOrders (d * (d * b)) (overcover (d * (d * b)) S r) z).card : ℝ)) /
          (2 * (d * (d * b) : ℝ)) := by
  let L := d * (d * b)
  let I := activeGaps L S hS r
  let len := fun i => gap L S hS i - 1 - 2 * r
  let start := fun i => point L S hS i + r + 1
  let credit := fun i => len i + 1
  let T := overcover L S r
  have hL : 0 < L := Nat.mul_pos hd (Nat.mul_pos hd hb)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hi (i : ℕ) (hiI : i ∈ I) : i < S.card :=
    mem_range.mp (mem_filter.mp hiI).1
  have hlen (i : ℕ) (hiI : i ∈ I) : len i ≤ L := by
    have : gap L S hS i ≤ L := gap_le hS hSL (hi i hiI)
    dsimp [len]
    omega
  have hdisj : (I : Set ℕ).PairwiseDisjoint (erodedArc L S hS r) := by
    intro i hiI k hkI hik
    exact (erodedArc_pairwiseDisjoint hS hSL)
      (mem_filter.mp hiI).1 (mem_filter.mp hkI).1 hik
  have hsafe := sum_credit_le_selectingOrders L (stripe d b j) T I
    (erodedArc L S hS r) credit hdisj (fun i hiI z hz => by
      exact arc_selection_card_lower_of_mem (hlen i hiI) (mem_inter.mp hz).2
        (overcover_subset L S r) (erodedArc_disjoint_overcover hS hSL (hi i hiI)))
  have hsafeR : (∑ i ∈ I, (credit i : ℝ) *
      ((stripe d b j ∩ erodedArc L S hS r i).card : ℝ)) ≤
      ∑ z ∈ stripe d b j, ((selectingOrders L T z).card : ℝ) := by
    exact_mod_cast hsafe
  have hstripe := weighted_arcCount_lower_bound hd hb hj I (fun i => (credit i : ℝ)) start len
    (fun _ _ => by positivity)
  have hcounts : (∑ i ∈ I, (credit i : ℝ) * (arcCount d b j (start i) (len i) : ℝ)) =
      ∑ i ∈ I, (credit i : ℝ) * ((stripe d b j ∩ erodedArc L S hS r i).card : ℝ) := by
    apply sum_congr rfl
    intro i hiI
    rw [show erodedArc L S hS r i = arc L (start i) (len i) from rfl]
    rw [arc, stripe_inter_arc_card hd hb j (start i) (len i) (hlen i hiI)]
  rw [hcounts] at hstripe
  have hweight : (∑ i ∈ I, (credit i : ℝ)) ≤ L := by
    exact_mod_cast sum_active_lengths_add_one_le (r := r) hS hSL
  have hc : (0 : ℝ) ≤ b * (1 - 1 / d) := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have : (1 : ℝ) / d ≤ 1 := (div_le_one hdR).mpr hd1
    positivity
  have hbase : (∑ i ∈ I, (credit i : ℝ) * (len i : ℝ)) / d -
      (b : ℝ) * (1 - 1 / d) * L ≤
      ∑ z ∈ stripe d b j, ((selectingOrders L T z).card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hweight hc
    linarith
  have hnum : (∑ i ∈ I, (credit i : ℝ) * (len i : ℝ)) =
      ∑ i ∈ range S.card, (GapErosion.remaining (gap L S hS i) r : ℝ) *
        (GapErosion.remaining (gap L S hS i) r + 1) := by
    change (∑ i ∈ (range S.card).filter (fun i => 0 < len i),
      ((len i + 1 : ℕ) : ℝ) * (len i : ℝ)) = _
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    change (if 0 < len i then ((len i + 1 : ℕ) : ℝ) * (len i : ℝ) else 0) =
      (len i : ℝ) * (len i + 1)
    by_cases hp : 0 < len i
    · simp only [hp, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      ring
    · have hz : len i = 0 := by omega
      simp [hz]
  rw [hnum] at hbase
  have hLeq : (L : ℝ) = (d : ℝ) * (d * b) := by
    dsimp [L]
    push_cast
    ring
  rw [← hLeq]
  change (d * b : ℝ) * GapErosion.erodedArea (range S.card) (gap L S hS) L r -
    (b : ℝ) * (1 - 1 / d) / 2 ≤
      (∑ z ∈ stripe d b j, ((selectingOrders L T z).card : ℝ)) / (2 * (L : ℝ))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mpr
  unfold GapErosion.erodedArea
  convert hbase using 1
  rw [hLeq]
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  field_simp

/-- The erosion loss is independent of the number of source slots or distinct anchors. -/
theorem pointArea_lower {d b j r : ℕ} (hd : 0 < d) (hb : 0 < b) (hj : j < d)
    (S : Finset ℕ) (hS : S.Nonempty) (hSL : S ⊆ range (d * (d * b))) :
    (d * b : ℝ) * GapErosion.pointArea (range S.card)
        (gap (d * (d * b)) S hS) (d * (d * b)) -
      (2 * r + 1 / 2 : ℝ) / d - (b : ℝ) * (1 - 1 / d) / 2 ≤
        (∑ z ∈ stripe d b j,
          ((selectingOrders (d * (d * b)) (overcover (d * (d * b)) S r) z).card : ℝ)) /
          (2 * (d * (d * b) : ℝ)) := by
  let L := d * (d * b)
  have hL : 0 < L := Nat.mul_pos hd (Nat.mul_pos hd hb)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hratio : (d * b : ℝ) * ((2 * r + 1 / 2 : ℝ) / (L : ℝ)) =
      (2 * r + 1 / 2 : ℝ) / d := by
    dsimp [L]
    push_cast
    field_simp
  have hloss := GapErosion.area_loss (range S.card) (gap L S hS) hL
    (sum_gap hS hSL) r
  calc
    _ = (d * b : ℝ) * (GapErosion.pointArea (range S.card) (gap L S hS) L -
          (2 * r + 1 / 2 : ℝ) / L) - (b : ℝ) * (1 - 1 / d) / 2 := by
      simp only [mul_sub, hratio]
      rfl
    _ ≤ (d * b : ℝ) * GapErosion.erodedArea (range S.card) (gap L S hS) L r -
          (b : ℝ) * (1 - 1 / d) / 2 :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left hloss (by positivity)) _
    _ ≤ _ := erodedArea_lower hd hb hj S hS hSL

end
end LeanMachine.CyclicStripeAverage
