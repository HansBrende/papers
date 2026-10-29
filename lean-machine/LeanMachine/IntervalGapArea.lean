import LeanMachine.CyclicSelection
import LeanMachine.GapErosion
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

/-!
# Circular point-gap area from an interval cover

The actual sorted anchors determine which gaps are contained in a supplied
closed natural interval. Exposed gaps are charged to their covered left
endpoints; each interval can receive at most one such charge.
-/

namespace LeanMachine.IntervalGapArea

open Finset CyclicSelection
open scoped BigOperators
noncomputable section

variable {κ : Type*}

def containsGap (L : ℕ) (S : Finset ℕ) (hS : S.Nonempty)
    (I : Finset κ) (lo hi : κ → ℕ) (i : ℕ) : Prop :=
  ∃ a ∈ I, lo a ≤ point L S hS i ∧ point L S hS (i + 1) ≤ hi a

def exposed (L : ℕ) (S : Finset ℕ) (hS : S.Nonempty)
    (I : Finset κ) (lo hi : κ → ℕ) : Finset ℕ := by
  classical
  exact (range S.card).filter fun i => ¬containsGap L S hS I lo hi i

def contained (L : ℕ) (S : Finset ℕ) (hS : S.Nonempty)
    (I : Finset κ) (lo hi : κ → ℕ) : Finset ℕ := by
  classical
  exact (range S.card).filter (containsGap L S hS I lo hi)

/-- One supplied interval contains the left endpoint of at most one exposed gap. -/
theorem exposed_left_card_le_one {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (I : Finset κ) (lo hi : κ → ℕ) {a : κ} (ha : a ∈ I) :
    ((exposed L S hS I lo hi).filter
      (fun i => lo a ≤ point L S hS i ∧ point L S hS i ≤ hi a)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro i hiE j hjE
  obtain ⟨hiE, hili, hihi⟩ := mem_filter.mp hiE
  obtain ⟨hjE, hjli, hjhi⟩ := mem_filter.mp hjE
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hnext := point_mono hS hSL (show i + 1 ≤ j by omega)
    exact (mem_filter.mp hiE).2 ⟨a, ha, hili, hnext.trans hjhi⟩
  · have hnext := point_mono hS hSL (show j + 1 ≤ i by omega)
    exact (mem_filter.mp hjE).2 ⟨a, ha, hjli, hnext.trans hihi⟩

/-- Exposed gaps require at most one charge per covering interval. The intervals
need not be disjoint, nonempty, or contained in the input coordinate range. -/
theorem exposed_card_le {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (I : Finset κ) (lo hi : κ → ℕ)
    (hcover : ∀ z ∈ S, ∃ a ∈ I, lo a ≤ z ∧ z ≤ hi a) :
    (exposed L S hS I lo hi).card ≤ I.card := by
  classical
  let A := fun a => (exposed L S hS I lo hi).filter
    (fun i => lo a ≤ point L S hS i ∧ point L S hS i ≤ hi a)
  have hsub : exposed L S hS I lo hi ⊆ I.biUnion A := by
    intro i hiE
    have hi' := mem_range.mp (mem_filter.mp hiE).1
    obtain ⟨a, ha, hlo, hhi⟩ := hcover _ (point_mem hS hi')
    exact mem_biUnion.mpr ⟨a, ha, mem_filter.mpr ⟨hiE, hlo, hhi⟩⟩
  calc
    _ ≤ (I.biUnion A).card := card_le_card hsub
    _ ≤ ∑ a ∈ I, (A a).card := card_biUnion_le
    _ ≤ ∑ _a ∈ I, 1 := sum_le_sum fun a ha => exposed_left_card_le_one hS hSL I lo hi ha
    _ = I.card := by simp

theorem gapEdges_pairwiseDisjoint {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) :
    (↑(range S.card) : Set ℕ).PairwiseDisjoint
      (fun i => Ico (point L S hS i) (point L S hS (i + 1))) := by
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨hli, hui⟩ := mem_Ico.mp hzi
  obtain ⟨hlj, huj⟩ := mem_Ico.mp hzj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have := point_mono hS hSL (show i + 1 ≤ j by omega)
    omega
  · have := point_mono hS hSL (show j + 1 ≤ i by omega)
    omega

/-- Covered circular gap lengths fit into the union of the supplied interval
edge sets, so overlapping intervals are never needed for this upper bound. -/
theorem sum_contained_gap_le {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (I : Finset κ) (lo hi : κ → ℕ) :
    (∑ i ∈ contained L S hS I lo hi, gap L S hS i) ≤ ∑ a ∈ I, (hi a - lo a) := by
  classical
  let C := contained L S hS I lo hi
  let edges := fun i => Ico (point L S hS i) (point L S hS (i + 1))
  have hdisj : (C : Set ℕ).PairwiseDisjoint edges := by
    intro i hiC j hjC hij
    exact gapEdges_pairwiseDisjoint hS hSL (mem_filter.mp hiC).1
      (mem_filter.mp hjC).1 hij
  have hsub : C.biUnion edges ⊆ I.biUnion (fun a => Ico (lo a) (hi a)) := by
    intro z hz
    obtain ⟨i, hiC, hzi⟩ := mem_biUnion.mp hz
    obtain ⟨a, ha, hlo, hhi⟩ := (mem_filter.mp hiC).2
    have hz' := mem_Ico.mp hzi
    exact mem_biUnion.mpr ⟨a, ha, mem_Ico.mpr ⟨hlo.trans hz'.1, hz'.2.trans_le hhi⟩⟩
  calc
    _ = (C.biUnion edges).card := by
      rw [card_biUnion hdisj]
      simp only [edges, Nat.card_Ico, gap, C]
    _ ≤ (I.biUnion (fun a => Ico (lo a) (hi a))).card := card_le_card hsub
    _ ≤ ∑ a ∈ I, (Ico (lo a) (hi a)).card := card_biUnion_le
    _ = _ := by simp only [Nat.card_Ico]

theorem sum_contained_add_exposed {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (I : Finset κ) (lo hi : κ → ℕ) :
    (∑ i ∈ contained L S hS I lo hi, gap L S hS i) +
      (∑ i ∈ exposed L S hS I lo hi, gap L S hS i) = L := by
  classical
  simpa only [contained, exposed, sum_gap hS hSL] using
    sum_filter_add_sum_filter_not (range S.card) (containsGap L S hS I lo hi) (gap L S hS)

/-- The full interval-length bill can only decrease the guaranteed exposed mass. -/
theorem exposed_mass_lower {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (I : Finset κ) (lo hi : κ → ℕ) :
    max ((L : ℝ) - ∑ a ∈ I, ((hi a - lo a : ℕ) : ℝ)) 0 ≤
      ∑ i ∈ exposed L S hS I lo hi, (gap L S hS i : ℝ) := by
  have hcovered : (∑ i ∈ contained L S hS I lo hi, (gap L S hS i : ℝ)) ≤
      ∑ a ∈ I, ((hi a - lo a : ℕ) : ℝ) := by
    exact_mod_cast sum_contained_gap_le hS hSL I lo hi
  have hsplit : (∑ i ∈ contained L S hS I lo hi, (gap L S hS i : ℝ)) +
      (∑ i ∈ exposed L S hS I lo hi, (gap L S hS i : ℝ)) = L := by
    exact_mod_cast sum_contained_add_exposed hS hSL I lo hi
  exact max_le (by linarith) (sum_nonneg fun _ _ => Nat.cast_nonneg _)

/-- Cauchy--Schwarz retains the actual number and total length of exposed gaps. -/
theorem exposed_mass_sq_le_energy {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (I : Finset κ) (lo hi : κ → ℕ) :
    (∑ i ∈ exposed L S hS I lo hi, (gap L S hS i : ℝ)) ^ 2 ≤
      ((exposed L S hS I lo hi).card : ℝ) *
        ∑ i ∈ exposed L S hS I lo hi, (gap L S hS i : ℝ) ^ 2 := by
  simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using
    sum_mul_sq_le_sq_mul_sq (exposed L S hS I lo hi)
      (fun _ => (1 : ℝ)) (fun i => (gap L S hS i : ℝ))

/-- An arbitrary natural interval cover bounds the energy of the actual
circular point gaps. Overlaps, empty intervals, and out-of-range endpoints
are all allowed. -/
theorem point_energy_lower {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (I : Finset κ) (lo hi : κ → ℕ)
    (hcover : ∀ z ∈ S, ∃ a ∈ I, lo a ≤ z ∧ z ≤ hi a) {V : ℝ}
    (hV : (∑ a ∈ I, ((hi a - lo a : ℕ) : ℝ)) ≤ V) :
    (max ((L : ℝ) - V) 0) ^ 2 ≤
      (I.card : ℝ) * ∑ i ∈ range S.card, (gap L S hS i : ℝ) ^ 2 := by
  classical
  have hmass : max ((L : ℝ) - V) 0 ≤
      ∑ i ∈ exposed L S hS I lo hi, (gap L S hS i : ℝ) :=
    (max_le_max_right 0 (sub_le_sub_left hV _)).trans (exposed_mass_lower hS hSL I lo hi)
  have hsq : (max ((L : ℝ) - V) 0) ^ 2 ≤
      (∑ i ∈ exposed L S hS I lo hi, (gap L S hS i : ℝ)) ^ 2 := by
    nlinarith [le_max_right ((L : ℝ) - V) 0]
  have hcard : ((exposed L S hS I lo hi).card : ℝ) ≤ I.card := by
    exact_mod_cast exposed_card_le hS hSL I lo hi hcover
  have henergy : (∑ i ∈ exposed L S hS I lo hi, (gap L S hS i : ℝ) ^ 2) ≤
      ∑ i ∈ range S.card, (gap L S hS i : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
  calc
    _ ≤ _ := hsq
    _ ≤ _ := exposed_mass_sq_le_energy hS I lo hi
    _ ≤ (I.card : ℝ) * ∑ i ∈ exposed L S hS I lo hi, (gap L S hS i : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg _)

/-- Denominator-free point-area form, convenient for fractional-cover bounds. -/
theorem point_area_lower {L : ℕ} (hL : 0 < L) {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (I : Finset κ) (lo hi : κ → ℕ)
    (hcover : ∀ z ∈ S, ∃ a ∈ I, lo a ≤ z ∧ z ≤ hi a) {V : ℝ}
    (hV : (∑ a ∈ I, ((hi a - lo a : ℕ) : ℝ)) ≤ V) :
    (max ((L : ℝ) - V) 0) ^ 2 ≤
      2 * (L : ℝ) ^ 2 * I.card *
        GapErosion.pointArea (range S.card) (gap L S hS) L := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  convert point_energy_lower hS hSL I lo hi hcover hV using 1
  unfold GapErosion.pointArea
  field_simp

/-- Normalized interval-count and total-length budgets. Positivity of the
count budget follows from covering a nonempty set, rather than being assumed. -/
theorem point_area_lower_of_budgets {L : ℕ} (hL : 0 < L) {S : Finset ℕ}
    (hS : S.Nonempty) (hSL : S ⊆ range L) (I : Finset κ) (lo hi : κ → ℕ)
    (hcover : ∀ z ∈ S, ∃ a ∈ I, lo a ≤ z ∧ z ≤ hi a) {α M : ℝ}
    (hV : (∑ a ∈ I, ((hi a - lo a : ℕ) : ℝ)) ≤ α * L)
    (hM : (I.card : ℝ) ≤ M) :
    (max (1 - α) 0) ^ 2 / (2 * M) ≤
      GapErosion.pointArea (range S.card) (gap L S hS) L := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hS' := hS
  obtain ⟨z, hz⟩ := hS'
  obtain ⟨a, ha, _, _⟩ := hcover z hz
  have hcard : 0 < I.card := card_pos.mpr ⟨a, ha⟩
  have hMR : 0 < M := lt_of_lt_of_le (by exact_mod_cast hcard) hM
  have harea : 0 ≤ GapErosion.pointArea (range S.card) (gap L S hS) L := by
    unfold GapErosion.pointArea
    positivity
  have hbase := point_area_lower hL hS hSL I lo hi hcover hV
  have hmax : max ((L : ℝ) - α * L) 0 = L * max (1 - α) 0 := by
    by_cases hα : α ≤ 1
    · rw [max_eq_left (by nlinarith), max_eq_left (by linarith)]
      ring
    · rw [max_eq_right (by nlinarith), max_eq_right (by linarith)]
      ring
  rw [hmax] at hbase
  have hcancel : (max (1 - α) 0) ^ 2 ≤
      2 * I.card * GapErosion.pointArea (range S.card) (gap L S hS) L := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hLR)).mp
    nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M)).mpr
  have hmono := mul_le_mul_of_nonneg_right hM harea
  nlinarith

end
end LeanMachine.IntervalGapArea
