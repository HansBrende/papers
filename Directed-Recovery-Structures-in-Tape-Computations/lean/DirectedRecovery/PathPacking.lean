import DirectedRecovery.IncidenceSeparator
import LeanMachine.PathPacking
import LeanMachine.GraphBall
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# The finite counting implication in the native paired-distance theorem

The graph and its short prescribed pairs are the actual paired incidence
objects. Simple shortest paths are selected in the proof. Their odd lengths,
the degree-to-ball estimate, and the maximal-disjoint packing loss are proved.
Only the disjoint-path transport estimate is a hypothesis; its derivation from
native tape semantics is not claimed here.
-/

namespace DirectedRecovery

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The two incidence ports supply the actual bipartition. -/
def pairedIncidenceBicoloring (N : V → Finset V) :
    (pairedIncidenceGraph N).Coloring Bool :=
  SimpleGraph.Coloring.mk (Sum.elim (fun _ => false) (fun _ => true)) (by
    intro u v h
    cases u <;> cases v <;> simp_all [pairedIncidenceGraph])

omit [Fintype V] [DecidableEq V] in
/-- Every walk between the prescribed opposite ports has odd length. -/
theorem paired_walk_length_odd (N : V → Finset V) (u v : V)
    (p : (pairedIncidenceGraph N).Walk (Sum.inl u) (Sum.inr v)) : Odd p.length := by
  apply ((pairedIncidenceBicoloring N).odd_length_iff_not_congr p).mpr
  simp [pairedIncidenceBicoloring, SimpleGraph.Coloring.mk]

omit [DecidableEq V] in
/-- A short prescribed pair has a simple shortest path of length at most `r`. -/
theorem short_paired_exists_path (N : V → Finset V) (r : ℕ)
    (i : shortPairedCoordinates N r) :
    ∃ p : (pairedIncidenceGraph N).Walk (Sum.inl i.val) (Sum.inr i.val),
      p.IsPath ∧
        p.length = (pairedIncidenceGraph N).dist (Sum.inl i.val) (Sum.inr i.val) ∧
        p.length ≤ r := by
  have hd : (pairedIncidenceGraph N).edist (Sum.inl i.val) (Sum.inr i.val) ≤
      (r : ℕ∞) := (Finset.mem_filter.mp i.property).2
  have hr := SimpleGraph.reachable_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hd)
  obtain ⟨p, hp, hlen⟩ := hr.exists_path_of_dist
  refine ⟨p, hp, hlen, ?_⟩
  rw [hlen]
  exact_mod_cast (SimpleGraph.natCast_dist_le_edist.trans hd)

/-- The exact finite short-pair packing bound. The transport hypothesis is
uniform over simple path families for the short coordinate set and all their
vertex-disjoint equal-length subfamilies. No desired total-count bound is
assumed. In the native theorem `M s` is the proved path-transport cost. -/
theorem short_paired_count_of_disjoint_transport (N : V → Finset V) (r Δ : ℕ)
    (hdegree : ∀ v, (pairedIncidenceGraph N).degree v ≤ Δ) (M : ℕ → ℝ)
    (htransport :
      ∀ p : ∀ i : shortPairedCoordinates N r,
        (pairedIncidenceGraph N).Walk (Sum.inl i.val) (Sum.inr i.val),
      (∀ i, (p i).IsPath) →
      ∀ s, Odd s → s ≤ r → ∀ J : Finset (shortPairedCoordinates N r),
      (∀ i ∈ J, (p i).length = s) →
      (J : Set (shortPairedCoordinates N r)).PairwiseDisjoint
        (fun i => (p i).support.toFinset) → (J.card : ℝ) ≤ M s) :
    ((shortPairedCoordinates N r).card : ℝ) ≤
      ∑ s ∈ (Finset.range (r + 1)).filter Odd,
        ((s + 1 : ℕ) : ℝ) *
          (∑ j ∈ Finset.range (r + 1), (max 1 Δ) ^ j : ℕ) * M s := by
  choose p hp _hshortest hlen using short_paired_exists_path N r
  have hinj : Function.Injective
      (fun i : shortPairedCoordinates N r => (Sum.inl i.val : V ⊕ V)) :=
    Sum.inl_injective.comp Subtype.val_injective
  have hcount := LeanMachine.PathPacking.odd_length_count (pairedIncidenceGraph N)
    (fun i : shortPairedCoordinates N r => Sum.inl i.val)
    (fun i : shortPairedCoordinates N r => Sum.inr i.val) hinj p
    r (∑ j ∈ Finset.range (r + 1), (max 1 Δ) ^ j) hlen
    (fun i => paired_walk_length_odd N i.val i.val (p i))
    (fun z => LeanMachine.GraphBall.card_edist_le (pairedIncidenceGraph N) Δ hdegree z r)
    M (htransport p hp)
  simpa only [Fintype.card_coe] using hcount

end DirectedRecovery
