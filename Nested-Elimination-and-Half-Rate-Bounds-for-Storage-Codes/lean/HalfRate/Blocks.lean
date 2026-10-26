import HalfRate.TheoremT

/-!
# Theorem PC: blocks with private outside parents

Partition the vertices into blocks. If every vertex has at most one in-neighbour outside its
block and every vertex is an in-neighbour of at most one vertex of each other block (private
outside parents), the blocks can be taken as pieces in any order. A block then needs only an
internal certificate:
* `ElimOn`: an elimination certificate of the relation induced on the block; `ElimOn.piece`
  turns it into a piece in any context;
* `ChordlessSubcubic`: every arc inside the block is reciprocated, every vertex of the block
  has at most three in-neighbours, and there is no transitive triangle inside; such a block is
  decomposed by the shortest-cycle decomposition of its local graph
  (`chordless_block_decomp`).
`rateBound_pc_ac` handles these two kinds; `PathCert.lean` adds chorded paths (Theorem PC).
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] [Fintype V] {N : V → Finset V}

/-- An elimination certificate of the relation induced on `K`: an elimination order of `K`,
records partitioning `K`, own and supplying records, such that at every step the in-neighbours of
the eliminated vertex inside `K` are already eliminated or lie in its supplying record. -/
structure ElimOn (N : V → Finset V) (K : Finset V) where
  l : List V
  nodup : l.Nodup
  hl : l.toFinset = K
  m : ℕ
  P : Fin m → Finset V
  disj : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  cover : (univ : Finset (Fin m)).biUnion P = K
  a : V → Fin m
  b : V → Fin m
  own : ∀ v ∈ K, v ∈ P (a v)
  ab : ∀ v ∈ K, a v ≠ b v
  step : ∀ j (hj : j < l.length), N l[j] ∩ K ⊆ rev ∅ l j ∪ P (b l[j])

/-- **Internal certificates give pieces.** An elimination certificate of the relation induced on
`K ⊆ R`, together with at most one in-neighbour in `R \ K` per vertex of `K` and private outside
parents, is a piece in the context `univ \ R`. -/
theorem ElimOn.piece {K : Finset V} (c : ElimOn N K) {R : Finset V}
    (h1 : ∀ v ∈ K, ∀ u ∈ N v, ∀ u' ∈ N v, u ∈ R → u' ∈ R → u ∉ K → u' ∉ K → u = u')
    (h2 : ∀ w, w ∉ K → ∀ v ∈ K, ∀ v' ∈ K, w ∈ N v → w ∈ N v' → v = v') :
    Nonempty (PieceCert N (univ \ R) K) := by
  have hmemK : ∀ v ∈ c.l, v ∈ K := fun v hv => c.hl ▸ List.mem_toFinset.mpr hv
  refine ⟨{
    m := c.m
    P := c.P
    disj := c.disj
    cover := c.cover
    l := c.l
    hl := c.hl
    a := c.a
    b := c.b
    par := outPar N R K
    own := fun v hv => c.own v (hmemK v hv)
    ab := fun v hv => c.ab v (hmemK v hv)
    charged := ?_ }⟩
  apply relCharged_of_cosupply
  · intro j hj hp u hu
    by_cases huR : u ∈ R
    · by_cases huK : u ∈ K
      · exact mem_union_right _ (c.step j hj (mem_inter.mpr ⟨hu, huK⟩))
      · exact absurd (outPar_none hp hu huR) huK
    · exact mem_union_left _ (by simp [huR])
  · intro j hj w hp
    obtain ⟨hw, hwR, hwK⟩ := outPar_some hp
    refine ⟨by simp [hwR, hwK], fun u hu => ?_, by simp⟩
    by_cases huR : u ∈ R
    · by_cases huK : u ∈ K
      · exact mem_union_right _ (mem_insert_of_mem (c.step j hj (mem_inter.mpr ⟨hu, huK⟩)))
      · rw [h1 _ (hmemK _ (List.getElem_mem hj)) u hu w hw huR hwR huK hwK]
        exact mem_union_right _ (mem_insert_self _ _)
    · exact mem_union_left _ (by simp [huR])
  · intro j j' hjj hj' w h1' h2'
    obtain ⟨hw1, -, hwK⟩ := outPar_some h1'
    obtain ⟨hw2, -, -⟩ := outPar_some h2'
    have := h2 w hwK _ (hmemK _ (List.getElem_mem (by omega))) _
      (hmemK _ (List.getElem_mem hj')) hw1 hw2
    have := (List.Nodup.getElem_inj_iff c.nodup).mp this
    omega

/-- Blocks of the first kind: every arc inside `K` is reciprocated, every vertex of `K` has at
most three in-neighbours, and there is no transitive triangle inside `K`. -/
def ChordlessSubcubic (N : V → Finset V) (K : Finset V) : Prop :=
  (∀ v ∈ K, ∀ u ∈ N v, u ∈ K → v ∈ N u) ∧ (∀ v ∈ K, (N v).card ≤ 3) ∧ TTFreeOn N K

/-- The local graph of a block `K`: `u ~ v` iff one of them lies in `K` and the other is one of
its in-neighbours. -/
def localGraph (N : V → Finset V) (K : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => v ∈ K ∧ u ∈ N v)

instance (N : V → Finset V) (K : Finset V) : DecidableRel (localGraph N K).Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ ((v ∈ K ∧ u ∈ N v) ∨ (u ∈ K ∧ v ∈ N u))) (by simp [localGraph])

omit [DecidableEq V] [Fintype V] in
theorem localGraph_adj {K : Finset V} {u v : V} :
    (localGraph N K).Adj u v ↔ u ≠ v ∧ ((v ∈ K ∧ u ∈ N v) ∨ (u ∈ K ∧ v ∈ N u)) := by
  simp [localGraph]

theorem mem_nbhd_localGraph {K : Finset V} {u v : V} :
    u ∈ nbhd (localGraph N K) v ↔ v ≠ u ∧ ((u ∈ K ∧ v ∈ N u) ∨ (v ∈ K ∧ u ∈ N v)) := by
  simp [nbhd, localGraph_adj]

/-- **Chordless subcubic blocks** decompose: the shortest-cycle decomposition of the local
graph, in which vertices outside the block are pendant because outside parents are private. -/
theorem chordless_block_decomp (hloop : ∀ v, v ∉ N v) {K L : Finset V} (hKL : Disjoint K L)
    (hK : ChordlessSubcubic N K)
    (hout : ∀ v ∈ K, ∀ u ∈ N v, ∀ u' ∈ N v, u ∉ K → u' ∉ K → u = u')
    (hpriv : ∀ w, w ∉ K → ∀ v ∈ K, ∀ v' ∈ K, w ∈ N v → w ∈ N v' → v = v')
    {q : List (Finset V)} (hq : Decomp N (univ \ L) q) :
    ∃ pcs, Decomp N (univ \ (K ∪ L)) pcs := by
  obtain ⟨hchord, hdegK, hTT⟩ := hK
  -- inside `K` the local graph is the reciprocated part of `N`
  have hsubK : ∀ v ∈ K, nbhd (localGraph N K) v ⊆ N v := by
    intro v hv u hu
    rcases (mem_nbhd_localGraph.mp hu).2 with ⟨huK, hvu⟩ | ⟨-, hu'⟩
    · exact hchord u huK v hvu hv
    · exact hu'
  -- outside `K` a vertex is adjacent only to its children in `K`
  have hpend : ∀ w, w ∉ K → (nbhd (localGraph N K) w).card ≤ 1 := by
    intro w hw
    rw [card_le_one]
    intro x hx y hy
    rcases (mem_nbhd_localGraph.mp hx).2 with ⟨hxK, hwx⟩ | ⟨hwK, -⟩
    · rcases (mem_nbhd_localGraph.mp hy).2 with ⟨hyK, hwy⟩ | ⟨hwK, -⟩
      · exact hpriv w hw x hxK y hyK hwx hwy
      · exact absurd hwK hw
    · exact absurd hwK hw
  refine block_decomp_of_cycles (G := localGraph N K) N hKL ?_ ?_ hpend hout ?_ hq K
    (subset_refl K)
  · intro v hv u hu
    rw [mem_nbhd_localGraph]
    exact ⟨fun e => by subst e; exact hloop v hu, Or.inr ⟨hv, hu⟩⟩
  · intro v
    by_cases hv : v ∈ K
    · exact (card_le_card (hsubK v hv)).trans (hdegK v hv)
    · exact (hpend v hv).trans (by norm_num)
  · -- a triangle inside `K` would consist of digons, hence contain a transitive triangle
    intro R hRK c
    exfalso
    have hK' : ∀ i, c.f i ∈ K := fun i => hRK (c.mem i)
    have harc : ∀ i j : Fin 3, i ≠ j → c.f i ∈ N (c.f j) := by
      intro i j hij
      have hadj := c.adj j i (by rw [SimpleGraph.cycleGraph_three_eq_top]; exact hij.symm)
      have hmem : c.f i ∈ nbhd (localGraph N K) (c.f j) := by simpa [nbhd] using hadj
      exact hsubK _ (hK' j) hmem
    have hne : ∀ i j : Fin 3, i ≠ j → c.f i ≠ c.f j := fun i j hij e => hij (c.inj e)
    exact hTT _ (hK' 0) _ (hK' 1) _ (hK' 2) (hne 0 1 (by decide)) (hne 1 2 (by decide))
      (hne 0 2 (by decide)) (harc 0 1 (by decide)) (harc 1 2 (by decide))
      (harc 0 2 (by decide))

/-- **Theorem PC for the first and third kinds of blocks.** Let the blocks be the fibres of `κ`. Suppose every vertex has at
most one in-neighbour outside its block, every vertex is an in-neighbour of at most one vertex of
each other block, and every block is chordless subcubic or has an elimination certificate of its
induced relation. Then every valid polymatroid satisfies `2 h(V) ≤ Σ_v h({v})`. Out-degrees are
unbounded. -/
theorem rateBound_pc_ac {ι : Type*} [Fintype ι] [DecidableEq ι] (hloop : ∀ v, v ∉ N v)
    (κ : V → ι)
    (h1 : ∀ v, ∀ u ∈ N v, ∀ u' ∈ N v, κ u ≠ κ v → κ u' ≠ κ v → u = u')
    (h2 : ∀ w v v', κ v = κ v' → κ w ≠ κ v → w ∈ N v → w ∈ N v' → v = v')
    (hK : ∀ i, ChordlessSubcubic N (univ.filter (κ · = i)) ∨
      Nonempty (ElimOn N (univ.filter (κ · = i)))) :
    RateBound N (1 / 2) := by
  have key : ∀ is : List ι, is.Nodup →
      ∃ q, Decomp N (univ \ univ.filter (fun v => κ v ∈ is)) q := by
    intro is
    induction is with
    | nil => intro _; exact ⟨[], by simp [Decomp]⟩
    | cons i rest ih =>
      intro hnd
      obtain ⟨q, hq⟩ := ih (List.nodup_cons.mp hnd).2
      have hi : i ∉ rest := (List.nodup_cons.mp hnd).1
      have hKL : Disjoint (univ.filter (κ · = i)) (univ.filter (fun v => κ v ∈ rest)) := by
        rw [Finset.disjoint_left]; intro x hx hx'
        simp only [mem_filter, mem_univ, true_and] at hx hx'
        exact hi (hx ▸ hx')
      have hset : univ.filter (fun v => κ v ∈ i :: rest) =
          univ.filter (κ · = i) ∪ univ.filter (fun v => κ v ∈ rest) := by
        ext x; simp
      rw [hset]
      have hout : ∀ v ∈ univ.filter (κ · = i), ∀ u ∈ N v, ∀ u' ∈ N v,
          u ∉ univ.filter (κ · = i) → u' ∉ univ.filter (κ · = i) → u = u' := by
        intro v hv u hu u' hu' huK hu'K
        simp only [mem_filter, mem_univ, true_and] at hv huK hu'K
        exact h1 v u hu u' hu' (hv ▸ huK) (hv ▸ hu'K)
      have hpriv : ∀ w, w ∉ univ.filter (κ · = i) → ∀ v ∈ univ.filter (κ · = i),
          ∀ v' ∈ univ.filter (κ · = i), w ∈ N v → w ∈ N v' → v = v' := by
        intro w hw v hv v' hv' hwv hwv'
        simp only [mem_filter, mem_univ, true_and] at hw hv hv'
        exact h2 w v v' (hv.trans hv'.symm) (hv ▸ hw) hwv hwv'
      rcases hK i with ha | hc
      · exact chordless_block_decomp hloop hKL ha hout hpriv hq
      · obtain ⟨c⟩ := hc
        obtain ⟨p⟩ := c.piece (R := univ.filter (κ · = i) ∪ univ.filter (fun v => κ v ∈ rest))
          (fun v hv u hu u' hu' _ _ huK hu'K => hout v hv u hu u' hu' huK hu'K) hpriv
        refine ⟨univ.filter (κ · = i) :: q, ?_⟩
        simp only [Decomp]
        have he : (univ \ (univ.filter (κ · = i) ∪ univ.filter (fun v => κ v ∈ rest))) ∪
            univ.filter (κ · = i) = univ \ univ.filter (fun v => κ v ∈ rest) := by
          ext x
          have h0 : x ∈ univ.filter (κ · = i) → x ∉ univ.filter (fun v => κ v ∈ rest) :=
            fun h h' => Finset.disjoint_left.mp hKL h h'
          simp only [mem_union, mem_sdiff, mem_univ, true_and] at h0 ⊢
          tauto
        refine ⟨Finset.disjoint_left.mpr fun x hx hx' => by simp [hx'] at hx, ⟨p⟩, ?_⟩
        rw [he]; exact hq
  obtain ⟨q, hq⟩ := key univ.toList (nodup_toList _)
  have huniv : univ.filter (fun v => κ v ∈ (univ : Finset ι).toList) = univ := by
    ext x; simp
  rw [huniv, sdiff_self] at hq
  exact rateBound_of_decomp hq

end HalfRate
