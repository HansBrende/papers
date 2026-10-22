import TransposeFollowup.ResidueMatching

/-! Turn the explicitly colored bipartite edge set into a simple graph on
the order A_0,...,A_(m-1),B_(m-1),...,B_0. Reversing the second class makes
each monotone matching a nested page. No graph edges are lost in conversion. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace OrderedBipartite

def left {m : ℕ} (i : Fin m) : Fin (2 * m) := ⟨i.val, by have := i.isLt; omega⟩

def right {m : ℕ} (j : Fin m) : Fin (2 * m) := ⟨2 * m - 1 - j.val, by have := j.isLt; omega⟩

theorem left_lt_right {m : ℕ} (i j : Fin m) : (left i).val < (right j).val := by
  have := i.isLt
  have := j.isLt
  dsimp [left, right]
  omega

theorem left_ne_right {m : ℕ} (i j : Fin m) : left i ≠ right j := by
  intro h
  have := left_lt_right i j
  have := congrArg Fin.val h
  omega

theorem left_injective {m : ℕ} : Function.Injective (@left m) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (2 * m) => x.val) h)

theorem right_injective {m : ℕ} : Function.Injective (@right m) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg Fin.val h
  dsimp [right] at hv
  apply Fin.ext
  omega

def address {m : ℕ} (e : Fin m × Fin m) : Sym2 (Fin (2 * m)) := s(left e.1, right e.2)

theorem address_injective {m : ℕ} : Function.Injective (@address m) := by
  intro e f h
  obtain h | h := Sym2.eq_iff.mp h
  · exact Prod.ext (left_injective h.1) (right_injective h.2)
  · exact False.elim (left_ne_right e.1 f.2 h.1)

theorem address_not_diag {m : ℕ} (e : Fin m × Fin m) : ¬(address e).IsDiag := by
  exact fun h => left_ne_right e.1 e.2 (Sym2.mk_isDiag_iff.mp h)

def graph {m : ℕ} (edges : Finset (Fin m × Fin m)) : SimpleGraph (Fin (2 * m)) :=
  SimpleGraph.fromEdgeSet (Set.range (fun e : edges => address e.val))

theorem mem_graph_edge {m : ℕ} (edges : Finset (Fin m × Fin m)) (z : Sym2 (Fin (2 * m))) :
    z ∈ (graph edges).edgeFinset ↔ ∃ e : edges, address e.val = z := by
  rw [SimpleGraph.mem_edgeFinset]
  change z ∈ (SimpleGraph.fromEdgeSet (Set.range (fun e : edges => address e.val))).edgeSet ↔ _
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · exact fun h => h.1
  · rintro ⟨e, rfl⟩
    exact ⟨⟨e, rfl⟩, address_not_diag e.val⟩

noncomputable def edgeEquiv {m : ℕ} (edges : Finset (Fin m × Fin m)) :
    edges ≃ (graph edges).edgeFinset :=
  Equiv.ofBijective (fun e => ⟨address e.val, (mem_graph_edge edges _).mpr ⟨e, rfl⟩⟩)
    ⟨by
      intro e f h
      exact Subtype.ext (address_injective (congrArg Subtype.val h)), by
      intro z
      obtain ⟨e, he⟩ := (mem_graph_edge edges z.val).mp z.property
      exact ⟨e, Subtype.ext he⟩⟩

theorem edgeEquiv_address {m : ℕ} (edges : Finset (Fin m × Fin m))
    (z : (graph edges).edgeFinset) : address ((edgeEquiv edges).symm z).val = z.val :=
  congrArg Subtype.val ((edgeEquiv edges).apply_symm_apply z)

end OrderedBipartite

namespace ResidueMatchingInput

variable {m c M : ℕ} {edges : Finset (Fin m × Fin m)} (D : ResidueMatchingInput edges c M)

noncomputable def nestedPages : NestedMatchingPages (OrderedBipartite.graph edges) (c * (M * M)) where
  src e := OrderedBipartite.left ((OrderedBipartite.edgeEquiv edges).symm e).val.1
  dst e := OrderedBipartite.right ((OrderedBipartite.edgeEquiv edges).symm e).val.2
  edge_eq := OrderedBipartite.edgeEquiv_address edges
  page e := D.color ((OrderedBipartite.edgeEquiv edges).symm e)
  forward e := OrderedBipartite.left_lt_right _ _
  nested e f hne hp := by
    have hne' : (OrderedBipartite.edgeEquiv edges).symm e ≠
        (OrderedBipartite.edgeEquiv edges).symm f :=
      fun h => hne ((OrderedBipartite.edgeEquiv edges).symm.injective h)
    have horder := D.same_color_order hne' hp
    have he := ((OrderedBipartite.edgeEquiv edges).symm e).val.2.isLt
    have hf := ((OrderedBipartite.edgeEquiv edges).symm f).val.2.isLt
    dsimp [OrderedBipartite.left, OrderedBipartite.right]
    rcases horder with ho | ho
    · exact Or.inl ⟨ho.1, by omega⟩
    · exact Or.inr ⟨ho.1, by omega⟩

end ResidueMatchingInput
end TransposeFollowup
