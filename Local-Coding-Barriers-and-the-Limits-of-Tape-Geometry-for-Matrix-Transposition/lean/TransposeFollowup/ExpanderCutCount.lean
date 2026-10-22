import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-! Finite expansion counting for the padding proof. Expansion is an explicit
hypothesis here: this file does not assert existence of a uniform expander.
Every small label class supplies crossing edges; discarding bad vertices costs
at most maximum degree times their number.
-/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

def crossingGraph {V L : Type*} (G : SimpleGraph V) (label : V → L) : SimpleGraph V where
  Adj i j := G.Adj i j ∧ label i ≠ label j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

noncomputable def labelFiber {V L : Type*} [Fintype V] (label : V → L) (l : L) : Finset V :=
  Finset.univ.filter (fun i => label i = l)

theorem mem_labelFiber {V L : Type*} [Fintype V] (label : V → L) (l : L) (i : V) :
    i ∈ labelFiber label l ↔ label i = l := by simp [labelFiber]

noncomputable def outsideNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S.biUnion (fun i => G.neighborFinset i) \ S

theorem outsideNeighbors_fiber {V L : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → L) (l : L) :
    outsideNeighbors G (labelFiber label l) =
      (labelFiber label l).biUnion (fun i => (crossingGraph G label).neighborFinset i) := by
  ext j
  simp only [outsideNeighbors, Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i, hi, hij⟩, hj⟩
    refine ⟨i, hi, ((crossingGraph G label).mem_neighborFinset i j).mpr ?_⟩
    refine ⟨(G.mem_neighborFinset i j).mp hij, ?_⟩
    intro he
    apply hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm.trans (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi, hij⟩
    obtain ⟨hadj, hne⟩ := ((crossingGraph G label).mem_neighborFinset i j).mp hij
    refine ⟨⟨i, hi, (G.mem_neighborFinset i j).mpr hadj⟩, ?_⟩
    intro hj
    exact hne ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

/-- Vertex expansion summed over label fibers. The factor two counts the two
ends of an undirected edge, via Mathlib's degree-sum theorem. -/
theorem expanding_label_cut {V L : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eta : ℝ)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (label : V → L) (hsmall : ∀ l, 2 * (labelFiber label l).card ≤ Fintype.card V) :
    eta * Fintype.card V ≤ 2 * ((crossingGraph G label).edgeFinset.card : ℝ) := by
  let labs := Finset.univ.image label
  have hcard : (∑ l ∈ labs, (labelFiber label l).card) = Fintype.card V := by
    simpa only [labelFiber, Finset.card_univ] using
      (Finset.card_eq_sum_card_image label (Finset.univ : Finset V)).symm
  have hdeg : (∑ l ∈ labs, ∑ i ∈ labelFiber label l, (crossingGraph G label).degree i) =
      2 * (crossingGraph G label).edgeFinset.card := by
    calc
      _ = ∑ i : V, (crossingGraph G label).degree i :=
        Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem label hi) _
      _ = _ := (crossingGraph G label).sum_degrees_eq_twice_card_edges
  have hpoint : ∀ l, eta * (labelFiber label l).card ≤
      ∑ i ∈ labelFiber label l, ((crossingGraph G label).degree i : ℝ) := by
    intro l
    have h := hexp (labelFiber label l) (hsmall l)
    have hN : (outsideNeighbors G (labelFiber label l)).card ≤
        ∑ i ∈ labelFiber label l, (crossingGraph G label).degree i := by
      rw [outsideNeighbors_fiber]
      exact Finset.card_biUnion_le.trans_eq (by simp)
    exact h.trans (by exact_mod_cast hN)
  calc
    _ = ∑ l ∈ labs, eta * ((labelFiber label l).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast hcard.symm
    _ ≤ ∑ l ∈ labs, ∑ i ∈ labelFiber label l, ((crossingGraph G label).degree i : ℝ) :=
      Finset.sum_le_sum (fun l _ => hpoint l)
    _ = _ := by exact_mod_cast hdeg

noncomputable def incidentTo {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bad : Finset V) : Finset (Sym2 V) :=
  bad.biUnion (fun i => G.incidenceFinset i)

noncomputable def goodCrossEdges {V L : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → L) (bad : Finset V) : Finset (Sym2 V) :=
  (crossingGraph G label).edgeFinset \ incidentTo G bad

theorem mem_goodCrossEdges {V L : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → L) (bad : Finset V) (i j : V) :
    s(i, j) ∈ goodCrossEdges G label bad ↔
      G.Adj i j ∧ label i ≠ label j ∧ i ∉ bad ∧ j ∉ bad := by
  simp only [goodCrossEdges, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨⟨hadj, hne⟩, hbad⟩
    refine ⟨hadj, hne, ?_, ?_⟩
    · intro hi
      exact hbad (Finset.mem_biUnion.mpr ⟨i, hi,
        SimpleGraph.mem_incidenceFinset.mpr (G.mk'_mem_incidenceSet_left_iff.mpr hadj)⟩)
    · intro hj
      exact hbad (Finset.mem_biUnion.mpr ⟨j, hj,
        SimpleGraph.mem_incidenceFinset.mpr (G.mk'_mem_incidenceSet_right_iff.mpr hadj)⟩)
  · rintro ⟨hadj, hne, hi, hj⟩
    refine ⟨⟨hadj, hne⟩, ?_⟩
    intro he
    obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp he
    have hm := (G.mk'_mem_incidenceSet_iff).mp (SimpleGraph.mem_incidenceFinset.mp he)
    rcases hm.2 with rfl | rfl
    · exact hi hv
    · exact hj hv

theorem incidentTo_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bad : Finset V) (q : ℕ)
    (hdeg : ∀ i, G.degree i ≤ q) : (incidentTo G bad).card ≤ q * bad.card := by
  calc
    _ ≤ ∑ i ∈ bad, (G.incidenceFinset i).card := Finset.card_biUnion_le
    _ = ∑ i ∈ bad, G.degree i := by simp
    _ ≤ ∑ _i ∈ bad, q := Finset.sum_le_sum (fun i _ => hdeg i)
    _ = _ := by simp [Nat.mul_comm]

theorem cut_discard_bad {V L : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → L) (bad : Finset V) (q : ℕ)
    (hdeg : ∀ i, G.degree i ≤ q) :
    (crossingGraph G label).edgeFinset.card ≤ (goodCrossEdges G label bad).card + q * bad.card := by
  have hsub : (crossingGraph G label).edgeFinset ⊆ goodCrossEdges G label bad ∪ incidentTo G bad := by
    intro e he
    by_cases hb : e ∈ incidentTo G bad
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he, hb⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (incidentTo_card_le G bad q hdeg) _))

theorem expanding_good_cut {V L : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eta : ℝ)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (label : V → L) (hsmall : ∀ l, 2 * (labelFiber label l).card ≤ Fintype.card V)
    (bad : Finset V) (q : ℕ) (hdeg : ∀ i, G.degree i ≤ q) :
    eta * Fintype.card V / 2 - q * bad.card ≤ (goodCrossEdges G label bad).card := by
  have hex := expanding_label_cut G eta hexp label hsmall
  have hn := cut_discard_bad G label bad q hdeg
  have hr : ((crossingGraph G label).edgeFinset.card : ℝ) ≤
      (goodCrossEdges G label bad).card + q * bad.card := by exact_mod_cast hn
  linarith

end TransposeFollowup
