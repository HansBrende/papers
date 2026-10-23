import TransposeFollowup.AdaptiveForestLevels

/-! Distinct cut children are charged to actual query occurrences. Constants,
ignored arguments and repeated pair queries remain part of the charged list. -/

namespace TransposeFollowup.AdaptiveForest

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} (G : SimpleGraph V)

noncomputable def parent (v : V) : V := (path G v).penultimate

theorem parent_adj {v : V} (hv : 0 < depth G v) : G.Adj (parent G v) v := by
  exact SimpleGraph.Walk.adj_penultimate
    ((SimpleGraph.Walk.not_nil_iff_lt_length).mpr hv)

theorem parent_depth (hG : G.IsAcyclic) {v : V} (hv : 0 < depth G v) :
    depth G v = depth G (parent G v) + 1 := by
  have ha := parent_adj G hv
  let q : G.Walk (root G (parent G v)) v :=
    (path G v).copy (root_eq_of_reachable G ha.reachable).symm rfl
  have hq : q.IsPath := by simpa [q] using path_isPath G v
  have hm : parent G v ∈ q.support := by
    dsimp only [q]
    rw [SimpleGraph.Walk.support_copy]
    exact (path G v).getVert_mem_support ((path G v).length - 1)
  have he := hG.path_concat (path_isPath G (parent G v)) hq ha hm
  have hl := congrArg SimpleGraph.Walk.length he
  simpa [q, SimpleGraph.Walk.length_concat, depth] using hl

noncomputable def deeperVertices [DecidableEq V] (s : Finset V) : Finset V :=
  s.filter (fun v => ∃ w ∈ s, depth G w < depth G v)

theorem deeperVertices_card_le [DecidableEq V] (s : Finset V) (hs : s.card ≤ 2) :
    (deeperVertices G s).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  obtain ⟨hv, u, hu, huv⟩ := Finset.mem_filter.mp hv
  obtain ⟨hw, z, hz, hzw⟩ := Finset.mem_filter.mp hw
  by_contra hn
  have hp : ({v, w} : Finset V) ⊆ s := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hv
    · exact (Finset.mem_singleton.mp ha) ▸ hw
  have he : ({v, w} : Finset V) = s :=
    Finset.eq_of_subset_of_card_le hp (by simpa [hn] using hs)
  rw [← he] at hu hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hz
  rcases hu with rfl | rfl <;> rcases hz with rfl | rfl <;> omega

noncomputable def nonroots [Fintype V] : Finset V :=
  Finset.univ.filter (fun v => 0 < depth G v)

theorem nonroots_card_le_queries [Fintype V] [DecidableEq V]
    (p : PublicProtocol V (fun _ => Bool)) (m : List Bool)
    (hG : (p.interactionGraph m).IsAcyclic)
    (hpair : p.Along (fun s => s.card ≤ 2) m) :
    (nonroots (p.interactionGraph m)).card ≤ m.length := by
  let H := p.interactionGraph m
  have hsub : nonroots H ⊆ (p.querySupports m).toFinset.biUnion (deeperVertices H) := by
    intro v hv
    have hd : 0 < depth H v := (Finset.mem_filter.mp hv).2
    obtain ⟨_, s, hs, hpar, hv⟩ := parent_adj H hd
    apply Finset.mem_biUnion.mpr
    refine ⟨s, List.mem_toFinset.mpr hs, Finset.mem_filter.mpr ⟨hv, ?_⟩⟩
    exact ⟨parent H v, hpar, by have hh := parent_depth H hG hd; omega⟩
  have harity : ∀ s ∈ (p.querySupports m).toFinset, s.card ≤ 2 := by
    intro s hs
    exact (p.along_iff_querySupports _ m).mp hpair s (List.mem_toFinset.mp hs)
  calc
    _ ≤ ((p.querySupports m).toFinset.biUnion (deeperVertices H)).card := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ (p.querySupports m).toFinset, (deeperVertices H s).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ (p.querySupports m).toFinset, 1 :=
      Finset.sum_le_sum (fun s hs => deeperVertices_card_le H s (harity s hs))
    _ = (p.querySupports m).toFinset.card := by simp
    _ ≤ (p.querySupports m).length := List.toFinset_card_le _
    _ ≤ m.length := p.querySupports_length_le m

theorem sum_pins_card [Fintype V] {R : ℕ} (hR : 0 < R) :
    (∑ r : Fin R, (pins G R r.val).card) = (nonroots G).card := by
  let label (v : V) : Fin R := ⟨depth G v % R, Nat.mod_lt _ hR⟩
  simpa [pins, nonroots, label, Finset.filter_filter, Fin.ext_iff] using
    Finset.sum_card_fiberwise_eq_card_filter (nonroots G) Finset.univ label

theorem exists_pins_card_mul_le [Fintype V] {R : ℕ} (hR : 0 < R) :
    ∃ r : Fin R, R * (pins G R r.val).card ≤ (nonroots G).card := by
  obtain ⟨r, _, hr⟩ := Finset.exists_min_image Finset.univ
    (fun r : Fin R => (pins G R r.val).card) ⟨⟨0, hR⟩, Finset.mem_univ _⟩
  refine ⟨r, ?_⟩
  calc
    _ = ∑ _a : Fin R, (pins G R r.val).card := by simp
    _ ≤ ∑ a : Fin R, (pins G R a.val).card :=
      Finset.sum_le_sum (fun a ha => hr a ha)
    _ = _ := sum_pins_card G hR

/-- A publicly chosen residue has at most one pin for every R original
answer occurrences. No common forest between different leaves is needed. -/
theorem exists_charged_pins [Fintype V] [DecidableEq V]
    (p : PublicProtocol V (fun _ => Bool)) (m : List Bool)
    (hG : (p.interactionGraph m).IsAcyclic)
    (hpair : p.Along (fun s => s.card ≤ 2) m)
    {R : ℕ} (hR : 0 < R) :
    ∃ r : Fin R, R * (pins (p.interactionGraph m) R r.val).card ≤ m.length := by
  obtain ⟨r, hr⟩ := exists_pins_card_mul_le (p.interactionGraph m) hR
  exact ⟨r, hr.trans (nonroots_card_le_queries p m hG hpair)⟩

end TransposeFollowup.AdaptiveForest
