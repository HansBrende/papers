import TransposeFollowup.ExpanderCutCount
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Prescribed pairs in damaged expanders

The deletion budget counts undirected edges once and counts deleted vertices
separately.  Prescribed endpoints are globally disjoint within each copy.
-/

namespace DirectedRecovery.DamagedExpanders

open Classical TransposeFollowup
open scoped BigOperators
set_option autoImplicit false

variable {V P κ : Type*} [Fintype V] [DecidableEq V]

/-- Crossing edges between surviving vertices must belong to the deleted set. -/
theorem goodCrossEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (label : V → κ) (F : Finset (Sym2 V)) (Z : Finset V)
    (hkeep : ∀ u v, G.Adj u v → s(u,v) ∉ F → u ∉ Z → v ∉ Z →
      label u = label v) : goodCrossEdges G label Z ⊆ F := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨hadj, hne, hu, hv⟩ := (mem_goodCrossEdges G label Z u v).mp he
    by_contra hf
    exact hne (hkeep u v hadj hf hu hv)

/-- The outside neighbors of the complement of one label class inject into
crossing edges: every such edge has a unique endpoint outside the set. -/
theorem outside_complement_fiber_le_cross (G : SimpleGraph V) [DecidableRel G.Adj]
    (label : V → κ) (c : κ) :
    (outsideNeighbors G (Finset.univ \ labelFiber label c)).card ≤
      (crossingGraph G label).edgeFinset.card := by
  let S := Finset.univ \ labelFiber label c
  let O := outsideNeighbors G S
  have hn : ∀ j ∈ O, ∃ i, i ∈ S ∧ G.Adj i j := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hj).1
    exact ⟨i, hi, (G.mem_neighborFinset i j).mp hij⟩
  let pick (j : O) : V := (hn j j.property).choose
  have hpick (j : O) : pick j ∈ S ∧ G.Adj (pick j) j :=
    (hn j j.property).choose_spec
  have hout (j : O) : j.val ∉ S := (Finset.mem_sdiff.mp j.property).2
  let f : O → (crossingGraph G label).edgeFinset := fun j =>
    ⟨s(pick j, j.val), by
      apply SimpleGraph.mem_edgeFinset.mpr
      refine ⟨(hpick j).2, ?_⟩
      have hin : label (pick j) ≠ c := by
        simpa [S, mem_labelFiber] using (Finset.mem_sdiff.mp (hpick j).1).2
      have hout' : label j.val = c := by
        have h := hout j
        simpa [S, mem_labelFiber] using h
      exact fun he => hin (he.trans hout')⟩
  have hf : Function.Injective f := by
    intro j k h
    have he : s(pick j, j.val) = s(pick k, k.val) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp he with h | h
    · exact Subtype.ext h.2
    · exact False.elim (hout k (h.1 ▸ (hpick j).1))
  exact Finset.card_le_card_of_injective hf

variable [Fintype P]

omit [Fintype V] [DecidableEq V] [Fintype P] in
/-- Every family of bad pairs can be charged to distinct endpoints in a set. -/
theorem charge_pairs (ends : P × Bool → V) (hinj : Function.Injective ends)
    (bad : Finset P) (U : Finset V)
    (hcharge : ∀ p ∈ bad, ∃ b, ends (p,b) ∈ U) : bad.card ≤ U.card := by
  let pick (p : bad) : Bool := (hcharge p p.property).choose
  let f : bad → U := fun p => ⟨ends (p.val, pick p), (hcharge p p.property).choose_spec⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact congrArg Prod.fst (hinj (congrArg Subtype.val h))
  exact Finset.card_le_card_of_injective hf

noncomputable def survivingPairs (label : V → κ) (Z : Finset V)
    (ends : P × Bool → V) : Finset P :=
  Finset.univ.filter (fun p => ends (p,false) ∉ Z ∧ ends (p,true) ∉ Z ∧
    label (ends (p,false)) = label (ends (p,true)))

/-- The exact finite loss budget for any labels constant along the edges
that survive the stated edge and vertex deletions. -/
theorem labeled_pairs_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (m Δ : ℕ) (hcard : Fintype.card V = 2 * m)
    (η : ℝ) (hη : 0 < η)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      η * S.card ≤ (outsideNeighbors G S).card)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (F : Finset (Sym2 V)) (Z : Finset V) (label : V → κ)
    (hkeep : ∀ u v, G.Adj u v → s(u,v) ∉ F → u ∉ Z → v ∉ Z →
      label u = label v)
    (ends : P × Bool → V) (hinj : Function.Injective ends) :
    η * Fintype.card P ≤ η * (survivingPairs label Z ends).card +
      F.card + (η + Δ) * Z.card := by
  have hgood : (goodCrossEdges G label Z).card ≤ F.card :=
    Finset.card_le_card (goodCrossEdges_subset G label F Z hkeep)
  have hgoodR : ((goodCrossEdges G label Z).card : ℝ) ≤ F.card := by exact_mod_cast hgood
  have hpair : Fintype.card P ≤ m := by
    have hc := Fintype.card_le_of_injective ends hinj
    simp only [Fintype.card_prod, Fintype.card_bool, hcard] at hc
    omega
  by_cases hsmall : ∀ c, 2 * (labelFiber label c).card ≤ Fintype.card V
  · have hcut := expanding_good_cut G η hexp label hsmall Z Δ hdeg
    rw [hcard] at hcut
    have hpR : (Fintype.card P : ℝ) ≤ m := by exact_mod_cast hpair
    have hn : (0 : ℝ) ≤ (survivingPairs label Z ends).card := Nat.cast_nonneg _
    have hz : (0 : ℝ) ≤ Z.card := Nat.cast_nonneg _
    push_cast at hcut
    nlinarith
  · push Not at hsmall
    obtain ⟨c, hc⟩ := hsmall
    let S := Finset.univ \ labelFiber label c
    have hpart : S.card + (labelFiber label c).card = Fintype.card V := by
      simpa [S] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (labelFiber label c))
    have hS : 2 * S.card ≤ Fintype.card V := by omega
    have hcross := cut_discard_bad G label Z Δ hdeg
    have hO := outside_complement_fiber_le_cross G label c
    change (outsideNeighbors G S).card ≤ (crossingGraph G label).edgeFinset.card at hO
    have hbound : (outsideNeighbors G S).card ≤ F.card + Δ * Z.card := by omega
    have hboundR : ((outsideNeighbors G S).card : ℝ) ≤ F.card + Δ * Z.card := by
      exact_mod_cast hbound
    have hex := hexp S hS
    let bad := Finset.univ \ survivingPairs label Z ends
    have hcharge : ∀ p ∈ bad, ∃ b, ends (p,b) ∈ S ∪ Z := by
      intro p hp
      by_contra! hn
      have hfalse : ends (p,false) ∉ S ∧ ends (p,false) ∉ Z := by
        simpa only [Finset.mem_union, not_or] using hn false
      have htrue : ends (p,true) ∉ S ∧ ends (p,true) ∉ Z := by
        simpa only [Finset.mem_union, not_or] using hn true
      have hl : label (ends (p,false)) = c := by
        simpa [S, mem_labelFiber] using hfalse.1
      have hr : label (ends (p,true)) = c := by
        simpa [S, mem_labelFiber] using htrue.1
      exact (Finset.mem_sdiff.mp hp).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfalse.2, htrue.2, hl.trans hr.symm⟩)
    have hbad : bad.card ≤ S.card + Z.card :=
      (charge_pairs ends hinj bad (S ∪ Z) hcharge).trans (Finset.card_union_le _ _)
    have hpairs : bad.card + (survivingPairs label Z ends).card = Fintype.card P := by
      simpa [bad] using Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ (survivingPairs label Z ends))
    have hbR : (bad.card : ℝ) ≤ S.card + Z.card := by exact_mod_cast hbad
    have hpR : (bad.card : ℝ) + (survivingPairs label Z ends).card = Fintype.card P := by
      exact_mod_cast hpairs
    nlinarith

/-- Delete the given edges and isolate every deleted vertex.  Reachability
between retained vertices is exactly reachability after actual vertex deletion. -/
def damagedGraph (G : SimpleGraph V) (F : Finset (Sym2 V)) (Z : Finset V) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ s(u,v) ∉ F ∧ u ∉ Z ∧ v ∉ Z
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_, h.2.2.2, h.2.2.1⟩
    simpa only [Sym2.eq_swap] using h.2.1⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- The conventional graph obtained by edge deletion followed by restricting
the vertex type to retained vertices. -/
abbrev deletedGraph (G : SimpleGraph V) (F : Finset (Sym2 V)) (Z : Finset V) :
    SimpleGraph {v // v ∉ Z} :=
  (G.deleteEdges (F : Set (Sym2 V))).induce {v | v ∉ Z}

omit [Fintype V] [DecidableEq V] in
/-- Isolating deleted vertices and removing them from the vertex type give
exactly the same reachability relation on surviving endpoints. -/
theorem damaged_reachable_iff_deleted (G : SimpleGraph V)
    (F : Finset (Sym2 V)) (Z : Finset V) {u v : V} (hu : u ∉ Z) (hv : v ∉ Z) :
    (damagedGraph G F Z).Reachable u v ↔
      (deletedGraph G F Z).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  constructor
  · rintro ⟨w⟩
    revert hu hv
    induction w with
    | nil =>
      intro hu hv
      exact SimpleGraph.Reachable.rfl
    | @cons a b c hab w ih =>
      intro ha hc
      have hbc := ih hab.2.2.2 hc
      have hab' : (deletedGraph G F Z).Adj ⟨a, ha⟩ ⟨b, hab.2.2.2⟩ :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hab.1, hab.2.1⟩
      exact hab'.reachable.trans hbc
  · intro h
    let f : deletedGraph G F Z →g damagedGraph G F Z :=
      { toFun := Subtype.val
        map_rel' := by
          intro a b hab
          have h := SimpleGraph.deleteEdges_adj.mp hab
          exact ⟨h.1, h.2, a.property, b.property⟩ }
    exact h.map f

/-- Prescribed pairs whose two endpoints survive and remain connected. -/
noncomputable def connectedSurvivingPairs (G : SimpleGraph V)
    (F : Finset (Sym2 V)) (Z : Finset V) (ends : P × Bool → V) : Finset P :=
  survivingPairs (damagedGraph G F Z).connectedComponentMk Z ends

theorem mem_connectedSurvivingPairs (G : SimpleGraph V)
    (F : Finset (Sym2 V)) (Z : Finset V) (ends : P × Bool → V) (p : P) :
    p ∈ connectedSurvivingPairs G F Z ends ↔
      ends (p,false) ∉ Z ∧ ends (p,true) ∉ Z ∧
        (damagedGraph G F Z).Reachable (ends (p,false)) (ends (p,true)) := by
  simp [connectedSurvivingPairs, survivingPairs, SimpleGraph.ConnectedComponent.eq]

/-- The whole one-copy estimate with actual edge and vertex deletions. -/
theorem damaged_pairs_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (m Δ : ℕ) (hcard : Fintype.card V = 2 * m)
    (η : ℝ) (hη : 0 < η)
    (hexp : ∀ S : Finset V, S.card ≤ m →
      η * S.card ≤ (outsideNeighbors G S).card)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (F : Finset (Sym2 V)) (Z : Finset V)
    (ends : P × Bool → V) (hinj : Function.Injective ends) :
    η * Fintype.card P ≤ η * (connectedSurvivingPairs G F Z ends).card +
      F.card + (η + Δ) * Z.card := by
  apply labeled_pairs_bound G m Δ hcard η hη _ hdeg F Z
    (damagedGraph G F Z).connectedComponentMk _ ends hinj
  · intro S hS
    exact hexp S (by omega)
  · intro u v hadj hf hu hv
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show (damagedGraph G F Z).Adj u v from ⟨hadj, hf, hu, hv⟩)

/-- The precise real-valued loss formula of the prescribed-pairs lemma. -/
theorem damaged_pairs_loss_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (m Δ : ℕ) (hcard : Fintype.card V = 2 * m)
    (η : ℝ) (hη : 0 < η)
    (hexp : ∀ S : Finset V, S.card ≤ m →
      η * S.card ≤ (outsideNeighbors G S).card)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (F : Finset (Sym2 V)) (Z : Finset V)
    (ends : P × Bool → V) (hinj : Function.Injective ends) :
    (Fintype.card P : ℝ) - F.card / η - (1 + Δ / η) * Z.card ≤
      (connectedSurvivingPairs G F Z ends).card := by
  have h := damaged_pairs_bound G m Δ hcard η hη hexp hdeg F Z ends hinj
  apply (mul_le_mul_iff_right₀ hη).mp
  calc
    η * ((Fintype.card P : ℝ) - F.card / η - (1 + Δ / η) * Z.card) =
        η * Fintype.card P - F.card - (η + Δ) * Z.card := by
      field_simp
    _ ≤ η * (connectedSurvivingPairs G F Z ends).card := by linarith

/-- The full all-copy statement.  Copies are disjoint by their index, each
has `2*m` vertices, and pair counts and deletion counts can vary arbitrarily.
The sums of the local deletion counts are the global `f` and `z`. -/
theorem damaged_expander_copies {W : Type*} [Fintype W]
    (m Δ : ℕ) (η : ℝ) (hη : 0 < η)
    (G : W → SimpleGraph (Fin (2 * m))) [∀ w, DecidableRel (G w).Adj]
    (hexp : ∀ w (S : Finset (Fin (2 * m))), S.card ≤ m →
      η * S.card ≤ (outsideNeighbors (G w) S).card)
    (hdeg : ∀ w v, (G w).degree v ≤ Δ)
    (F : W → Finset (Sym2 (Fin (2 * m)))) (Z : W → Finset (Fin (2 * m)))
    (Pairs : W → Type*) [∀ w, Fintype (Pairs w)]
    (ends : (w : W) → Pairs w × Bool → Fin (2 * m))
    (hinj : ∀ w, Function.Injective (ends w)) :
    (∑ w, (Fintype.card (Pairs w) : ℝ)) - (∑ w, ((F w).card : ℝ)) / η -
      (1 + Δ / η) * (∑ w, ((Z w).card : ℝ)) ≤
        ∑ w, ((connectedSurvivingPairs (G w) (F w) (Z w) (ends w)).card : ℝ) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
    damaged_pairs_loss_bound (G w) m Δ (by simp) η hη (hexp w) (hdeg w)
      (F w) (Z w) (ends w) (hinj w))
  simpa only [Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum] using hsum

end DirectedRecovery.DamagedExpanders
