import SourceCovers.CoreFractionalCover
import LeanMachine.FractionalIntervalGap

set_option autoImplicit false

/-!
# Fractional raw-source gap bounds

Canonical time components are fixed from the original nondistinguished spans,
before choosing any covering roots or weights. Their internal time edges are
disjoint. This removes the need to merge cover-dependent hulls afterwards.
-/

namespace SourceCovers

open Classical Finset LeanMachine
open scoped BigOperators ENNReal
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- Distinct canonical time components actually met by the complete orbit. -/
def coreVisitedComponents (I J D : Finset (CoreFamily K)) (u : Fin T) :
    Finset (TimeComponents.components (nondistinguishedEdges J D) (T - 1)) :=
  univ.filter fun c => c.val ∈
    (coreOrbit I u.val).image (TimeComponents.label (nondistinguishedEdges J D))

theorem coreVisitedComponents_card_le (hc : HasSpanColoring K 2)
    (I J D : Finset (CoreFamily K)) (hIJ : I ⊆ J) (u : Fin T) :
    (coreVisitedComponents I J D u).card ≤ 1 + 2 * markedBefore I D u.val := by
  apply le_trans ?_ (core_orbit_component_card_le hc I J D hIJ u.val)
  apply card_le_card_of_injOn Subtype.val
  · intro c hc
    exact (mem_filter.mp hc).2
  · intro a _ b _ hab
    exact Subtype.ext hab

/-- Every raw source in an orbit is in the range interval of a component
visited by that very orbit. -/
theorem coreVisitedComponents_cover (I J D : Finset (CoreFamily K)) (x : ℕ → ℕ)
    (u : Fin T) {a : ℕ} (ha : a ∈ (coreOrbit I u.val).image x) :
    ∃ c ∈ coreVisitedComponents I J D u,
      TimeComponents.rawLower x c ≤ a ∧ a ≤ TimeComponents.rawUpper x c := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp ha
  have htT : t ≤ T - 1 := by
    have := coreOrbit_le I ht
    have := u.isLt
    omega
  let c := TimeComponents.ofTime (nondistinguishedEdges J D) (T - 1) t htT
  refine ⟨c, mem_filter.mpr ⟨mem_univ _, mem_image_of_mem _ ht⟩, ?_⟩
  exact mem_Icc.mp (TimeComponents.mem_rawInterval_ofTime x htT)

/-- A union of full spans never costs more variation than their sum. This
does not require unit-speed motion, disjoint spans, or a coloring. -/
theorem nondistinguished_union_variation_le (J D : Finset (CoreFamily K)) (x : ℕ → ℕ) :
    (∑ e ∈ nondistinguishedEdges J D ∩ range (T - 1),
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤
    ∑ q ∈ J \ D, ∑ e ∈ q.val.edges, dist (x e : ℝ) (x (e + 1) : ℝ) := by
  let B := nondistinguishedEdges J D
  have hsub : ∀ q ∈ J \ D, q.val.edges ⊆ B := by
    intro q hq e he
    exact mem_biUnion.mpr ⟨q, hq, he⟩
  calc
    _ ≤ ∑ e ∈ B, dist (x e : ℝ) (x (e + 1) : ℝ) :=
      sum_le_sum_of_subset_of_nonneg inter_subset_left (fun _ _ _ => dist_nonneg)
    _ ≤ _ := by
      rw [FiniteIncidence.sum_eq_sum_multiplicity (J \ D) B
        (fun q => q.val.edges) (fun e => dist (x e : ℝ) (x (e + 1) : ℝ)) hsub]
      apply sum_le_sum
      intro e he
      obtain ⟨q, hq, heq⟩ := mem_biUnion.mp he
      have hcard : 1 ≤ ((J \ D).filter (fun q => e ∈ q.val.edges)).card :=
        card_pos.mpr ⟨q, mem_filter.mpr ⟨hq, heq⟩⟩
      have hcardR : (1 : ℝ) ≤ ((J \ D).filter (fun q => e ∈ q.val.edges)).card := by
        exact_mod_cast hcard
      simp only [nsmul_eq_mul]
      convert mul_le_mul_of_nonneg_right hcardR
        (dist_nonneg : 0 ≤ dist (x e : ℝ) (x (e + 1) : ℝ)) using 1 <;> simp
      left
      congr 1
      ext a
      simp

/-- Exact incidence form: any feasible weights may be used, with the actual
number of distinct time components visited by each covering orbit. -/
theorem fractional_core_gap_of_weights (I J D : Finset (CoreFamily K)) (x : ℕ → ℕ)
    {L : ℕ} (hL : 0 < L) {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L)
    {w : Fin T → ℝ} (hw : FractionalCover.Covers S (coreRawSets I x) w) {α : ℝ}
    (hV : (∑ e ∈ nondistinguishedEdges J D ∩ range (T - 1),
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * L) :
    (max (1 - α) 0) ^ 2 /
      (2 * ∑ u, ((coreVisitedComponents I J D u).card : ℝ) * w u) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L :=
  FractionalIntervalGap.point_area_lower_of_incidence_budget hL hS hSL
    (coreVisitedComponents I J D) (TimeComponents.rawLower x) (TimeComponents.rawUpper x)
    (fun u _ ha => coreVisitedComponents_cover I J D x u ha) hw
    ((TimeComponents.sum_rawWidth_le x univ).trans hV) le_rfl

/-- Stronger union-variation form: every original nondistinguished time edge
is billed once, even when it belongs to several selected family spans. The
retained subset is arbitrary; no phase, rank, or path-length premise is needed. -/
theorem fractional_core_gap_of_union_variation (hc : HasSpanColoring K 2)
    (I J D : Finset (CoreFamily K)) (hIJ : I ⊆ J) (x : ℕ → ℕ)
    {L r : ℕ} (hL : 0 < L) (hD : D.card ≤ r) {S : Finset ℕ}
    (hS : S.Nonempty) (hSL : S ⊆ range L)
    (hfinite : fractionalCoreCover I x S ≠ ⊤) {α : ℝ}
    (hV : (∑ e ∈ nondistinguishedEdges J D ∩ range (T - 1),
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * L) :
    (max (1 - α) 0) ^ 2 / (2 * (2 * (r : ℝ) + 1) * (fractionalCoreCover I x S).toReal) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L := by
  apply FractionalIntervalGap.point_area_lower_of_finite_number hL hS hSL
    (coreVisitedComponents I J D) (TimeComponents.rawLower x) (TimeComponents.rawUpper x)
    (fun u _ ha => coreVisitedComponents_cover I J D x u ha) hfinite
  · exact (TimeComponents.sum_rawWidth_le x univ).trans hV
  · intro u
    have hcount := coreVisitedComponents_card_le hc I J D hIJ u
    have hmarked := markedBefore_le I D u.val
    exact_mod_cast (show (coreVisitedComponents I J D u).card ≤ 2 * r + 1 by omega)

/-- Full original-span bill, allowing any selected/retained subsets and any
natural raw-coordinate path. Counting the common root once saves one component. -/
theorem fractional_core_gap (hc : HasSpanColoring K 2)
    (I J D : Finset (CoreFamily K)) (hIJ : I ⊆ J) (x : ℕ → ℕ)
    {L r : ℕ} (hL : 0 < L) (hD : D.card ≤ r) {S : Finset ℕ}
    (hS : S.Nonempty) (hSL : S ⊆ range L)
    (hfinite : fractionalCoreCover I x S ≠ ⊤) {α : ℝ}
    (hV : (∑ q ∈ J \ D, ∑ e ∈ q.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * L) :
    (max (1 - α) 0) ^ 2 / (2 * (2 * (r : ℝ) + 1) * (fractionalCoreCover I x S).toReal) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L :=
  fractional_core_gap_of_union_variation hc I J D hIJ x hL hD hS hSL hfinite
    ((nondistinguished_union_variation_le J D x).trans hV)

/-- The paper's phase cover, using all original nondistinguished spans.
For legal phases, `coreRawSets_phase_eq` identifies the complete core orbit. -/
theorem fractional_phase_gap (hc : HasSpanColoring K 2)
    (D : Finset (CoreFamily K)) (M ρ : ℕ) (x : ℕ → ℕ)
    {L r : ℕ} (hL : 0 < L) (hD : D.card ≤ r) {S : Finset ℕ}
    (hS : S.Nonempty) (hSL : S ⊆ range L)
    (hfinite : fractionalCoreCover (phaseSurvivors K M ρ) x S ≠ ⊤) {α : ℝ}
    (hV : (∑ q ∈ univ \ D, ∑ e ∈ q.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * L) :
    (max (1 - α) 0) ^ 2 /
      (2 * (2 * (r : ℝ) + 1) * (fractionalCoreCover (phaseSurvivors K M ρ) x S).toReal) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L :=
  fractional_core_gap hc (phaseSurvivors K M ρ) univ D (subset_univ _) x
    hL hD hS hSL hfinite hV

end
end SourceCovers
