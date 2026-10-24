import LeanMachine.TutteBerge.Berge

/-!
# The matching number and the barrier form of the Tutte–Berge formula

Additions of lean-machine on top of the external file `LeanMachine.TutteBerge.Berge`.

* `SimpleGraph.matchingNumber`: `ν(G)`, the largest number of edges of a matching of `G`.
* `SimpleGraph.two_mul_matchingNumber_add_oddCount_le` and
  `SimpleGraph.exists_two_mul_matchingNumber_add_oddCount_eq`: the Tutte–Berge formula for `ν(G)`,
  `2 ν(G) + odd(G − U) ≤ |V| + |U|` for every `U`, with equality for some `U`.
* `SimpleGraph.componentBlocks G U`: the vertex sets of the connected components of `G − U`. They
  partition the vertices outside `U` into blocks with no edges between them
  (`biUnion_componentBlocks`, `pairwiseDisjoint_componentBlocks`, `not_adj_of_mem_componentBlocks`),
  and `2 ∑_B ⌊|B|/2⌋ + odd(G − U) = |V| − |U|` (`two_mul_sum_card_div_two_add_oddCount`).
* `SimpleGraph.matchingNumber_le_card_add_sum_card_div_two` and
  `SimpleGraph.exists_card_add_sum_card_div_two_eq_matchingNumber`: the barrier form, used by bounds
  of the shape `|U| + ∑_B ⌊|B|/2⌋`: every `U` gives at least `ν(G)`, and some `U` attains it.
* `SimpleGraph.Subgraph.IsMatching.exists_fin_enum`: the edges of a matching listed as pairs
  `(u i, w i)` with `Sum.elim u w` injective.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The matching number `ν(G)`: the largest number of edges of a matching of `G`. -/
noncomputable def matchingNumber : ℕ :=
  sSup {n | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = n}

section MatchingNumber

variable [Finite V]

omit [Finite V] in
private lemma matchingSizes_nonempty :
    {n | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = n}.Nonempty :=
  ⟨0, ⊥, fun _ hv => absurd hv (by simp), by simp⟩

private lemma matchingSizes_bddAbove :
    BddAbove {n | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = n} := by
  refine ⟨Nat.card V, ?_⟩
  rintro _ ⟨M, hM, rfl⟩
  have := BergeMatching.two_mul_card_add_le hM (∅ : Set V)
  rw [Set.ncard_empty] at this
  omega

theorem le_matchingNumber {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ G.matchingNumber :=
  le_csSup (matchingSizes_bddAbove G) ⟨M, hM, rfl⟩

theorem exists_isMatching_ncard_eq_matchingNumber :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = G.matchingNumber :=
  Nat.sSup_mem (matchingSizes_nonempty G) (matchingSizes_bddAbove G)

/-- The weak Tutte–Berge inequality for the matching number. -/
theorem two_mul_matchingNumber_add_oddCount_le (U : Set V) :
    2 * G.matchingNumber + BergeMatching.oddCount G U ≤ Nat.card V + U.ncard := by
  obtain ⟨M, hM, hcard⟩ := G.exists_isMatching_ncard_eq_matchingNumber
  rw [← hcard]
  exact BergeMatching.two_mul_card_add_le hM U

/-- **The Tutte–Berge formula** for the matching number: some `U` attains the bound. -/
theorem exists_two_mul_matchingNumber_add_oddCount_eq :
    ∃ U : Set V, 2 * G.matchingNumber + BergeMatching.oddCount G U = Nat.card V + U.ncard := by
  obtain ⟨M, U, hM, h⟩ := BergeMatching.exists_tutte_berge G
  refine ⟨U, le_antisymm (G.two_mul_matchingNumber_add_oddCount_le U) ?_⟩
  have := G.le_matchingNumber hM
  omega

end MatchingNumber

section Blocks

variable [Fintype V] [DecidableEq V]

open Classical in
/-- The vertex set, as a finset of vertices of `G`, of a connected component of `G − U`. -/
private noncomputable def block (U : Finset V)
    (c : ((⊤ : G.Subgraph).deleteVerts (U : Set V)).coe.ConnectedComponent) : Finset V :=
  (univ.filter fun w => ((⊤ : G.Subgraph).deleteVerts (U : Set V)).coe.connectedComponentMk w = c).map
    (Function.Embedding.subtype _)

omit [DecidableEq V] in
private lemma mem_block {U : Finset V}
    {c : ((⊤ : G.Subgraph).deleteVerts (U : Set V)).coe.ConnectedComponent} {v : V} :
    v ∈ block G U c ↔ ∃ h : v ∈ ((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts,
      ((⊤ : G.Subgraph).deleteVerts (U : Set V)).coe.connectedComponentMk ⟨v, h⟩ = c := by
  classical
  simp only [block, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨v, h⟩, hc, rfl⟩

omit [DecidableEq V] in
private lemma block_nonempty (U : Finset V)
    (c : ((⊤ : G.Subgraph).deleteVerts (U : Set V)).coe.ConnectedComponent) :
    (block G U c).Nonempty := by
  induction c using ConnectedComponent.ind with
  | h w => exact ⟨w.1, (mem_block G).2 ⟨w.2, rfl⟩⟩

omit [DecidableEq V] in
private lemma eq_of_mem_block {U : Finset V}
    {c c' : ((⊤ : G.Subgraph).deleteVerts (U : Set V)).coe.ConnectedComponent} {v : V}
    (hc : v ∈ block G U c) (hc' : v ∈ block G U c') : c = c' := by
  obtain ⟨h, rfl⟩ := (mem_block G).1 hc
  obtain ⟨h', rfl⟩ := (mem_block G).1 hc'
  rfl

omit [DecidableEq V] in
private lemma block_injective (U : Finset V) : Function.Injective (block G U) := by
  intro c c' h
  obtain ⟨v, hv⟩ := block_nonempty G U c
  exact eq_of_mem_block G hv (h ▸ hv)

omit [DecidableEq V] in
private lemma card_block (U : Finset V)
    (c : ((⊤ : G.Subgraph).deleteVerts (U : Set V)).coe.ConnectedComponent) :
    (block G U c).card = c.supp.ncard := by
  classical
  rw [block, card_map, ← Set.ncard_coe_finset]
  congr 1
  ext w
  simp [ConnectedComponent.mem_supp_iff]

open Classical in
private lemma sum_card_block (U : Finset V) :
    ∑ c, (block G U c).card + U.card = Fintype.card V := by
  classical
  have h1 : ∑ c, (block G U c).card =
      Fintype.card ((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts := by
    rw [← card_univ, card_eq_sum_card_fiberwise
      (f := ((⊤ : G.Subgraph).deleteVerts (U : Set V)).coe.connectedComponentMk)
      (t := univ) (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun c _ => ?_
    rw [block, card_map]
  rw [h1, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := V)]
  have : ((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts = (U : Set V)ᶜ := by ext; simp
  rw [this, Nat.card_coe_set_eq, ← Set.ncard_coe_finset U, add_comm, Set.ncard_add_ncard_compl]

open Classical in
/-- The vertex sets of the connected components of `G − U`, as finsets of vertices of `G`. -/
noncomputable def componentBlocks (U : Finset V) : Finset (Finset V) :=
  univ.image (block G U)

private lemma mem_componentBlocks {U : Finset V} {B : Finset V} :
    B ∈ G.componentBlocks U ↔ ∃ c, block G U c = B := by
  classical
  simp [componentBlocks]

/-- The blocks cover exactly the vertices outside `U`. -/
theorem biUnion_componentBlocks (U : Finset V) : (G.componentBlocks U).biUnion id = univ \ U := by
  ext v
  simp only [mem_biUnion, id, mem_sdiff, mem_univ, true_and]
  constructor
  · rintro ⟨B, hB, hv⟩
    obtain ⟨c, rfl⟩ := (mem_componentBlocks G).1 hB
    obtain ⟨h, -⟩ := (mem_block G).1 hv
    simpa using h
  · intro hv
    have h : v ∈ ((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts := by simpa using hv
    exact ⟨_, (mem_componentBlocks G).2 ⟨_, rfl⟩, (mem_block G).2 ⟨h, rfl⟩⟩

/-- Distinct blocks are disjoint. -/
theorem pairwiseDisjoint_componentBlocks (U : Finset V) :
    ((G.componentBlocks U : Set (Finset V))).PairwiseDisjoint id := by
  rintro B hB B' hB' hne
  obtain ⟨c, rfl⟩ := (mem_componentBlocks G).1 hB
  obtain ⟨c', rfl⟩ := (mem_componentBlocks G).1 hB'
  refine Finset.disjoint_left.2 fun v hv hv' => hne ?_
  rw [eq_of_mem_block G hv hv']

/-- No edge of `G` joins two distinct blocks. -/
theorem not_adj_of_mem_componentBlocks (U : Finset V) :
    ∀ B ∈ G.componentBlocks U, ∀ B' ∈ G.componentBlocks U, B ≠ B' →
      ∀ a ∈ B, ∀ b ∈ B', ¬ G.Adj a b := by
  intro B hB B' hB' hne a ha b hb hab
  obtain ⟨c, rfl⟩ := (mem_componentBlocks G).1 hB
  obtain ⟨c', rfl⟩ := (mem_componentBlocks G).1 hB'
  obtain ⟨h, rfl⟩ := (mem_block G).1 ha
  obtain ⟨h', rfl⟩ := (mem_block G).1 hb
  refine hne (congrArg (block G U) (ConnectedComponent.connectedComponentMk_eq_of_adj ?_))
  simp only [Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.verts_top, Set.mem_univ,
    true_and, Subgraph.top_adj]
  exact ⟨by simpa using h, by simpa using h', hab⟩

/-- Counting: `2 ∑_B ⌊|B|/2⌋ + odd(G − U) = |V| − |U|`. -/
theorem two_mul_sum_card_div_two_add_oddCount (U : Finset V) :
    2 * ∑ B ∈ G.componentBlocks U, B.card / 2 + BergeMatching.oddCount G (U : Set V) =
      Fintype.card V - U.card := by
  classical
  have hsum : ∑ B ∈ G.componentBlocks U, B.card / 2 = ∑ c, (block G U c).card / 2 := by
    rw [componentBlocks, sum_image fun c _ c' _ h => block_injective G U h]
  have hodd : BergeMatching.oddCount G (U : Set V) =
      (univ.filter fun c => Odd (block G U c).card).card := by
    rw [BergeMatching.oddCount, oddComponents, ← Set.ncard_coe_finset]
    congr 1
    ext c
    simp [card_block]
  have hpt : ∀ n : ℕ, 2 * (n / 2) + (if Odd n then 1 else 0) = n := by
    intro n
    split_ifs with h
    · have := Nat.odd_iff.1 h
      omega
    · have := Nat.even_iff.1 (Nat.not_odd_iff_even.1 h)
      omega
  have htot : 2 * ∑ c, (block G U c).card / 2 + (univ.filter fun c => Odd (block G U c).card).card =
      ∑ c, (block G U c).card := by
    rw [mul_sum, card_filter, ← sum_add_distrib]
    exact sum_congr rfl fun c _ => hpt _
  have := sum_card_block G U
  rw [hsum, hodd]
  omega

/-- Every `U` bounds the matching number: `ν(G) ≤ |U| + ∑_B ⌊|B|/2⌋`, the sum running over the
components of `G − U`. -/
theorem matchingNumber_le_card_add_sum_card_div_two (U : Finset V) :
    G.matchingNumber ≤ U.card + ∑ B ∈ G.componentBlocks U, B.card / 2 := by
  have h1 := G.two_mul_sum_card_div_two_add_oddCount U
  have h2 := G.two_mul_matchingNumber_add_oddCount_le (U : Set V)
  rw [Set.ncard_coe_finset, Nat.card_eq_fintype_card] at h2
  have h3 : U.card ≤ Fintype.card V := card_le_univ _
  omega

/-- **The barrier form of the Tutte–Berge formula.** Some `U` has
`|U| + ∑_B ⌊|B|/2⌋ = ν(G)`, the sum running over the components of `G − U`. -/
theorem exists_card_add_sum_card_div_two_eq_matchingNumber :
    ∃ U : Finset V, U.card + ∑ B ∈ G.componentBlocks U, B.card / 2 = G.matchingNumber := by
  classical
  obtain ⟨U₀, hU₀⟩ := G.exists_two_mul_matchingNumber_add_oddCount_eq
  refine ⟨U₀.toFinset, ?_⟩
  have h1 := G.two_mul_sum_card_div_two_add_oddCount U₀.toFinset
  rw [Set.coe_toFinset] at h1
  have h2 : U₀.ncard = U₀.toFinset.card := Set.ncard_eq_toFinset_card' U₀
  have h3 : U₀.toFinset.card ≤ Fintype.card V := card_le_univ _
  rw [Nat.card_eq_fintype_card, h2] at hU₀
  omega

end Blocks

/-- The edges of a matching of a finite graph, listed as pairs `(u i, w i)` whose endpoints are
all distinct. -/
theorem Subgraph.IsMatching.exists_fin_enum [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) :
    ∃ u w : Fin M.edgeSet.ncard → V, (∀ i, M.Adj (u i) (w i)) ∧ Function.Injective (Sum.elim u w) := by
  have hcard : Nat.card M.edgeSet = M.edgeSet.ncard := Nat.card_coe_set_eq _
  let e : Fin M.edgeSet.ncard ≃ M.edgeSet :=
    (finCongr hcard.symm).trans (Finite.equivFin M.edgeSet).symm
  let u : Fin M.edgeSet.ncard → V := fun i => (e i).1.out.1
  let w : Fin M.edgeSet.ncard → V := fun i => (e i).1.out.2
  have hmk : ∀ i, s(u i, w i) = (e i).1 := fun i => Quot.out_eq _
  have hadj : ∀ i, M.Adj (u i) (w i) := fun i => by
    rw [← Subgraph.mem_edgeSet, hmk]
    exact (e i).2
  have hedge : ∀ i j, s(u i, w i) = s(u j, w j) → i = j := fun i j h => by
    rw [hmk, hmk] at h
    exact e.injective (Subtype.ext h)
  refine ⟨u, w, hadj, Function.Injective.sumElim ?_ ?_ ?_⟩
  · intro i j h
    exact hedge i j (by rw [h, hM.eq_of_adj_left (hadj i) (h ▸ hadj j)])
  · intro i j h
    exact hedge i j (by rw [h, hM.eq_of_adj_right (hadj i) (h ▸ hadj j)])
  · intro i j h
    have h1 : w i = u j := hM.eq_of_adj_left (hadj i) (h ▸ (hadj j).symm)
    have hij : i = j := hedge i j (by rw [h, h1, Sym2.eq_swap])
    subst hij
    exact (M.adj_sub (hadj i)).ne h

end SimpleGraph
