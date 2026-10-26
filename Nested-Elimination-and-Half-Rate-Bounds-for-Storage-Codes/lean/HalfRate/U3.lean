import HalfRate.N3

/-!
# U3: no transitive triangle, subcubic underlying graph

If a loopless recovery relation has no transitive triangle and its underlying simple graph has
maximum degree at most three, it satisfies the weighted half bound (Theorem U3 of the
paper). The proof is N3's
shortest-cycle decomposition of the underlying graph: cycle pieces of length at least four and
the acyclic remainder transfer to the relation because it has fewer arcs (`PieceCert.mono`);
triangles of the underlying graph are directed 3-cycles, which are relative 2-dicolourings
(`bdirPiece`) with private outside parents.
-/

namespace HalfRate

open Finset MotionDepthCodes SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {N : V → Finset V}

/-- The underlying simple graph: `u ~ v` iff `u ≠ v` and `u → v` or `v → u`. -/
def und (N : V → Finset V) : SimpleGraph V := SimpleGraph.fromRel (fun u v => u ∈ N v)

instance (N : V → Finset V) : DecidableRel (und N).Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ (u ∈ N v ∨ v ∈ N u)) (by simp [und])

omit [DecidableEq V] [Fintype V] in
theorem und_adj {u v : V} : (und N).Adj u v ↔ u ≠ v ∧ (u ∈ N v ∨ v ∈ N u) := by simp [und]

theorem mem_nbhd_und {u v : V} : u ∈ nbhd (und N) v ↔ v ≠ u ∧ (v ∈ N u ∨ u ∈ N v) := by
  simp [nbhd, und_adj]

theorem sub_nbhd_und (hloop : ∀ v, v ∉ N v) (v : V) : N v ⊆ nbhd (und N) v := by
  intro u hu
  rw [mem_nbhd_und]
  exact ⟨fun h => by subst h; exact hloop v hu, Or.inr hu⟩

theorem mem_nbhd_und' (hloop : ∀ v, v ∉ N v) {u v : V} (h : u ∈ N v) : v ∈ nbhd (und N) u := by
  rw [mem_nbhd_und]
  exact ⟨fun e => by subst e; exact hloop u h, Or.inl h⟩

omit [DecidableEq V] [Fintype V] in
/-- In a relation without transitive triangles, a triangle of the underlying graph with the arc
`x₀ → x₁` is the directed 3-cycle `x₀ → x₁ → x₂ → x₀`, with no reverse arcs. -/
theorem dtri_orient (hTT : TTFree N) {x₀ x₁ x₂ : V} (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂)
    (h12 : x₁ ≠ x₂) (u02 : x₀ ∈ N x₂ ∨ x₂ ∈ N x₀) (u12 : x₁ ∈ N x₂ ∨ x₂ ∈ N x₁)
    (a01 : x₀ ∈ N x₁) :
    x₁ ∈ N x₂ ∧ x₂ ∈ N x₀ ∧ x₁ ∉ N x₀ ∧ x₂ ∉ N x₁ ∧ x₀ ∉ N x₂ := by
  have a12 : x₁ ∈ N x₂ := by
    rcases u12 with h | h
    · exact h
    · exfalso
      rcases u02 with h' | h'
      · exact hTT x₀ x₂ x₁ h02 h12.symm h01 h' h a01
      · exact hTT x₂ x₀ x₁ h02.symm h01 h12.symm h' a01 h
  have n02 : x₀ ∉ N x₂ := fun h => hTT x₀ x₁ x₂ h01 h12 h02 a01 a12 h
  have a20 : x₂ ∈ N x₀ := u02.resolve_left n02
  exact ⟨a12, a20, fun h => hTT x₁ x₂ x₀ h12 h02.symm h01.symm a12 a20 h,
    fun h => hTT x₂ x₀ x₁ h02.symm h01 h12.symm a20 a01 h, n02⟩

omit [Fintype V] in
/-- A vertex of degree at most three with two neighbours in `H` has at most one outside. -/
theorem no_two_outside {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {v x y w u : V}
    {H : Finset V} (hdeg : (nbhd G v).card ≤ 3) (hx : x ∈ nbhd G v) (hy : y ∈ nbhd G v)
    (hw : w ∈ nbhd G v) (hu : u ∈ nbhd G v) (hxy : x ≠ y) (hxH : x ∈ H) (hyH : y ∈ H)
    (hwH : w ∉ H) (huH : u ∉ H) : w = u := by
  by_contra hwu
  have := four_le_card hx hy hw hu hxy (by rintro rfl; exact hwH hxH)
    (by rintro rfl; exact huH hxH) (by rintro rfl; exact hwH hyH) (by rintro rfl; exact huH hyH)
    hwu
  omega

/-- **Directed triangles** `c₀ → c₁ → c₂ → c₀` (no reverse arcs) are pieces: parts `{c₀, c₂}`
(one arc) and `{c₁}`; outside parents are private because the relation has no transitive
triangle, and unique because the underlying graph is subcubic. -/
theorem dtriPiece (hloop : ∀ v, v ∉ N v) (hTT : TTFree N)
    (hdeg : ∀ v, (nbhd (und N) v).card ≤ 3) {R : Finset V} {c₀ c₁ c₂ : V}
    (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂)
    (a01 : c₀ ∈ N c₁) (a12 : c₁ ∈ N c₂) (a20 : c₂ ∈ N c₀)
    (n10 : c₁ ∉ N c₀) (n02 : c₀ ∉ N c₂) :
    Nonempty (PieceCert N (univ \ R) {c₀, c₁, c₂}) := by
  have hmem : ∀ x, x ∈ ({c₀, c₁, c₂} : Finset V) ↔ x = c₀ ∨ x = c₁ ∨ x = c₂ := fun x => by simp
  have one : ∀ v ∈ ({c₀, c₁, c₂} : Finset V), ∀ u ∈ N v, u ∈ R → u ∉ ({c₀, c₁, c₂} : Finset V) →
      outPar N R {c₀, c₁, c₂} v = some u := by
    intro v hv u hu huR huH
    obtain ⟨x, y, hx, hy, hxy, hxH, hyH⟩ : ∃ x y, x ∈ nbhd (und N) v ∧ y ∈ nbhd (und N) v ∧
        x ≠ y ∧ x ∈ ({c₀, c₁, c₂} : Finset V) ∧ y ∈ ({c₀, c₁, c₂} : Finset V) := by
      rcases (hmem v).mp hv with rfl | rfl | rfl
      · exact ⟨c₁, c₂, mem_nbhd_und' hloop a01, sub_nbhd_und hloop _ a20, h12, by simp, by simp⟩
      · exact ⟨c₀, c₂, sub_nbhd_und hloop _ a01, mem_nbhd_und' hloop a12, h02, by simp, by simp⟩
      · exact ⟨c₀, c₁, mem_nbhd_und' hloop a20, sub_nbhd_und hloop _ a12, h01, by simp, by simp⟩
    cases hp : outPar N R {c₀, c₁, c₂} v with
    | none => exact absurd (outPar_none hp hu huR) huH
    | some w =>
      obtain ⟨hw, -, hwH⟩ := outPar_some hp
      rw [no_two_outside (hdeg v) hx hy (sub_nbhd_und hloop _ hw) (sub_nbhd_und hloop _ hu) hxy
        hxH hyH hwH huH]
  refine bdirPiece N (univ \ R) {c₀, c₁, c₂} {c₀, c₂} {c₁} ?_ ?_ ?_
    (isAcyclicIn_singleton (hloop c₁)) (outPar N R {c₀, c₁, c₂}) ?_ ?_ ?_
  · refine Finset.disjoint_singleton_right.mpr ?_
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun h => h01 h.symm, h12⟩
  · ext x; simp only [mem_union, mem_insert, mem_singleton]; tauto
  · -- `{c₀, c₂}` is acyclic: its only arc is `c₂ → c₀`
    intro T hT hne
    by_cases h2 : c₂ ∈ T
    · refine ⟨c₂, h2, fun u hu huT => ?_⟩
      rcases mem_insert.mp (hT huT) with rfl | h
      · exact n02 hu
      · rw [mem_singleton.mp h] at hu; exact hloop _ hu
    · obtain ⟨x, hx⟩ := hne
      have hx0 : x = c₀ := by
        rcases mem_insert.mp (hT hx) with h | h
        · exact h
        · rw [mem_singleton.mp h] at hx; exact absurd hx h2
      subst hx0
      refine ⟨x, hx, fun u hu huT => ?_⟩
      rcases mem_insert.mp (hT huT) with rfl | h
      · exact hloop _ hu
      · rw [mem_singleton.mp h] at huT; exact h2 huT
  · intro v hv u hu
    by_cases huR : u ∈ R
    · by_cases huH : u ∈ ({c₀, c₁, c₂} : Finset V)
      · exact Or.inr (Or.inl huH)
      · exact Or.inr (Or.inr (one v hv u hu huR huH))
    · exact Or.inl (by simp [huR])
  · intro v _ w hp
    obtain ⟨-, hwR, hwH⟩ := outPar_some hp
    exact ⟨by simp [hwR], hwH⟩
  · intro v hv v' hv' w h1 h2
    obtain ⟨hw1, -, hwH⟩ := outPar_some h1
    obtain ⟨hw2, -, -⟩ := outPar_some h2
    have hne : ∀ x ∈ ({c₀, c₁, c₂} : Finset V), w ≠ x := fun x hx e => hwH (e ▸ hx)
    by_cases hvv : v = v'
    · subst hvv; exact Iff.rfl
    exfalso
    -- two distinct triangle vertices with a common parent close a transitive triangle
    have harc : v ∈ N v' ∨ v' ∈ N v := by
      rcases (hmem v).mp hv with rfl | rfl | rfl <;> rcases (hmem v').mp hv' with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl hvv
        | exact Or.inl ‹_›
        | exact Or.inr ‹_›
    rcases harc with h | h
    · exact hTT w v v' (hne v hv) hvv (hne v' hv') hw1 h hw2
    · exact hTT w v' v (hne v' hv') (Ne.symm hvv) (hne v hv) hw2 h hw1

/-- Triangles of the underlying graph are pieces. -/
theorem triPiece (hloop : ∀ v, v ∉ N v) (hTT : TTFree N)
    (hdeg : ∀ v, (nbhd (und N) v).card ≤ 3) {R : Finset V} (c : CycIn (und N) R 3) :
    Nonempty (PieceCert N (univ \ R) (univ.image c.f)) := by
  have hu : ∀ i j : Fin 3, i ≠ j → (c.f i ∈ N (c.f j) ∨ c.f j ∈ N (c.f i)) := fun i j hij =>
    (und_adj.mp (c.adj i j (by rw [cycleGraph_three_eq_top]; exact hij))).2
  have hne : ∀ i j : Fin 3, i ≠ j → c.f i ≠ c.f j := fun i j hij h => hij (c.inj h)
  have himg : univ.image c.f = {c.f 0, c.f 1, c.f 2} := by
    ext x; simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  rw [himg]
  by_cases a01 : c.f 0 ∈ N (c.f 1)
  · obtain ⟨a12, a20, n10, -, n02⟩ := dtri_orient hTT (hne 0 1 (by decide))
      (hne 0 2 (by decide)) (hne 1 2 (by decide)) (hu 0 2 (by decide)) (hu 1 2 (by decide)) a01
    exact dtriPiece hloop hTT hdeg (hne 0 1 (by decide)) (hne 0 2 (by decide))
      (hne 1 2 (by decide)) a01 a12 a20 n10 n02
  · have a10 : c.f 1 ∈ N (c.f 0) := (hu 0 1 (by decide)).resolve_left a01
    obtain ⟨a02, a21, n01, -, n12⟩ := dtri_orient hTT (hne 1 0 (by decide))
      (hne 1 2 (by decide)) (hne 0 2 (by decide)) (hu 1 2 (by decide)) (hu 0 2 (by decide)) a10
    have e : ({c.f 0, c.f 1, c.f 2} : Finset V) = {c.f 1, c.f 0, c.f 2} := by
      ext x; simp only [mem_insert, mem_singleton]; tauto
    rw [e]
    exact dtriPiece hloop hTT hdeg (hne 1 0 (by decide)) (hne 1 2 (by decide))
      (hne 0 2 (by decide)) a10 a02 a21 n01 n12

/-- **U3.** A loopless recovery relation without transitive triangles whose underlying simple
graph has maximum degree at most three satisfies the weighted half bound. -/
theorem rateBound_u3 (hloop : ∀ v, v ∉ N v) (hTT : TTFree N)
    (hdeg : ∀ v, (und N).degree v ≤ 3) : RateBound N (1 / 2) := by
  have hdeg' : ∀ v, (nbhd (und N) v).card ≤ 3 := fun v => by
    have h := hdeg v
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter] at h
    exact h
  obtain ⟨pcs, h⟩ := decomp_of_cycles N (sub_nbhd_und hloop) hdeg'
    (fun _ c => triPiece hloop hTT hdeg' c) univ
  rw [sdiff_self] at h
  exact rateBound_of_decomp h

/-- Storage codes under the hypotheses of U3 have `|C|² ≤ |α|^|V|`. -/
theorem card_sq_le_u3 {α : Type*} [Fintype α] [Nonempty α] (hloop : ∀ v, v ∉ N v)
    (hTT : TTFree N) (hdeg : ∀ v, (und N).degree v ≤ 3) {C : Finset (V → α)}
    (hC : IsStorageCode N C) : C.card ^ 2 ≤ Fintype.card α ^ Fintype.card V :=
  card_sq_le_of_rateBound_half (rateBound_u3 hloop hTT hdeg) hC

end HalfRate
