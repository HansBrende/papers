import TransposeFollowup.RecodedXor
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Quantitative graph locality of a variable-component flip. Nearness is
defined by a walk of length below the threshold, so disconnected vertices
are never accidentally near (the ordinary natural-valued `dist` is zero
between disconnected vertices in Mathlib). -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false
universe u v

def GraphNear {V : Type u} (G : SimpleGraph V) (ell : ℕ) (x y : V) : Prop :=
  ∃ p : G.Walk x y, p.length < ell

theorem mem_componentSet_empty {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x y : V) :
    y ∈ componentSet G ∅ x ↔ G.Reachable x y := by
  rw [mem_componentSet]
  constructor
  · rintro ⟨hx, hy, h⟩
    let f : G.induce {v | v ∉ (∅ : Finset V)} →g G :=
      { toFun := Subtype.val, map_rel' := fun h => h }
    exact h.map f
  · intro h
    let f : G →g G.induce {v | v ∉ (∅ : Finset V)} :=
      { toFun := fun v => ⟨v, Finset.notMem_empty v⟩, map_rel' := fun h => h }
    exact ⟨Finset.notMem_empty x, Finset.notMem_empty y, h.map f⟩

/-- A map that either collapses an edge or sends it to an edge cannot increase
the length of the shortest available walk. -/
theorem project_walk {A : Type u} {V : Type v} {G : SimpleGraph A} {H : SimpleGraph V}
    (f : A → V) (hf : ∀ {a b}, G.Adj a b → f a = f b ∨ H.Adj (f a) (f b))
    {a b : A} (p : G.Walk a b) : ∃ q : H.Walk (f a) (f b), q.length ≤ p.length := by
  induction p with
  | nil => exact ⟨.nil, le_rfl⟩
  | @cons a c b hac p ih =>
    obtain ⟨q, hq⟩ := ih
    rcases hf hac with he | ha
    · rw [he]
      exact ⟨q, hq.trans (by simp)⟩
    · exact ⟨q.cons ha, by simpa using Nat.add_le_add_right hq 1⟩

theorem component_short_walk {V : Type u} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hy : y ∈ componentSet G ∅ x) :
    ∃ p : G.Walk x y, p.length < (componentSet G ∅ x).card := by
  obtain ⟨p, hp⟩ := ((mem_componentSet_empty G x y).mp hy).exists_isPath
  have hsub : p.support.toFinset ⊆ componentSet G ∅ x := by
    intro z hz
    exact (mem_componentSet_empty G x z).mpr
      (p.takeUntil z (List.mem_toFinset.mp hz)).reachable
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support] at hc
  exact ⟨p, by omega⟩

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

theorem local_variable_edge (G : SimpleGraph (Fin n)) (hG : C.LocalTo G)
    {v w : MatrixBit n b} (h : C.system.graph.Adj v w) : v.1 = w.1 ∨ G.Adj v.1 w.1 := by
  obtain ⟨_, k, hk | hk⟩ := h
  · exact hG k v w hk
  · rcases hG k w v hk with he | ha
    · exact Or.inl he.symm
    · exact Or.inr ha.symm

/-- Two rows represented in a variable component of size at most ell are
joined in the row graph by a walk of length strictly below ell. -/
theorem component_rows_near (G : SimpleGraph (Fin n)) (hG : C.LocalTo G)
    {S : Finset (MatrixBit n b)} (hS : S ∈ C.system.components)
    (ell : ℕ) (hsize : S.card ≤ ell) {i j : Fin n}
    (hi : i ∈ rowsOf S) (hj : j ∈ rowsOf S) : GraphNear G ell i j := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
  have hvS := (C.system.mem_component_iff hS v).mp hv
  have hwC : w ∈ C.system.component v := by rw [hvS]; exact hw
  obtain ⟨p, hp⟩ := component_short_walk C.system.graph hwC
  obtain ⟨q, hq⟩ := project_walk Prod.fst (C.local_variable_edge G hG) p
  refine ⟨q, hq.trans_lt ?_⟩
  change p.length < (C.system.component v).card at hp
  rw [hvS] at hp
  exact hp.trans_le hsize

noncomputable def nearBits (G : SimpleGraph (Fin n)) (ell : ℕ) : Finset (MatrixBit n b) :=
  Finset.univ.filter (fun v => GraphNear G ell v.1 v.2.1)

theorem small_flip_preserves_far (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) {S : Finset (MatrixBit n b)} (hS : S ∈ C.system.unanchored)
    (ell : ℕ) (hsize : S.card ≤ ell) (x : FiniteMatrix n b) (v : MatrixBit n b)
    (hv : v ∉ nearBits (b := b) G ell) : matrixBits (C.flip S x) v = matrixBits x v := by
  apply C.flip_outside_square hc hS x v
  by_contra h
  push Not at h
  exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    C.component_rows_near G hG ((C.system.mem_unanchored S).mp hS).1 ell hsize h.1 h.2⟩)

end RecodedXorCode
end TransposeFollowup
