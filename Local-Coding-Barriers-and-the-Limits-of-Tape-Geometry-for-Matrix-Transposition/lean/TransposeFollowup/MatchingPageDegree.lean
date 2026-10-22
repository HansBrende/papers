import TransposeFollowup.OrderedBipartitePages

/-! A nested matching-page representation itself bounds vertex degree;
the explicit residue construction therefore needs no separate degree premise. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace NestedMatchingPages

variable {v k : ℕ} {G : SimpleGraph (Fin v)} [DecidableRel G.Adj]
    (D : NestedMatchingPages G k)

theorem shared_vertex_same_page {e f : G.edgeFinset} (hp : D.page e = D.page f)
    (u : Fin v) (he : u ∈ e.val) (hf : u ∈ f.val) : e = f := by
  by_contra hne
  rw [← D.edge_eq e] at he
  rw [← D.edge_eq f] at hf
  simp only [Sym2.mem_iff] at he hf
  have hfe := D.forward e
  have hff := D.forward f
  rcases D.nested e f hne hp with ho | ho <;>
    rcases he with he | he <;> rcases hf with hf | hf
  all_goals
    have heval := congrArg Fin.val he
    have hfval := congrArg Fin.val hf
    omega

include D in
theorem degree_le_pages (u : Fin v) : G.degree u ≤ k := by
  let edge (e : G.incidenceFinset u) : G.edgeFinset :=
    ⟨e.val, G.incidenceFinset_subset u e.property⟩
  let color (e : G.incidenceFinset u) : Fin k := D.page (edge e)
  have hc : Function.Injective color := by
    intro e f heq
    have he : u ∈ e.val := (SimpleGraph.mem_incidenceFinset.mp e.property).2
    have hf : u ∈ f.val := (SimpleGraph.mem_incidenceFinset.mp f.property).2
    have hef : edge e = edge f := D.shared_vertex_same_page heq u he hf
    exact Subtype.ext (congrArg (fun z : G.edgeFinset => z.val) hef)
  have hcard := Fintype.card_le_of_injective color hc
  simpa only [Fintype.card_coe, Fintype.card_fin, G.card_incidenceFinset_eq_degree] using hcard

end NestedMatchingPages

theorem ResidueMatchingInput.degree_le {m c M : ℕ} {edges : Finset (Fin m × Fin m)}
    (D : ResidueMatchingInput edges c M) (u : Fin (2 * m)) :
    (OrderedBipartite.graph edges).degree u ≤ c * (M * M) := D.nestedPages.degree_le_pages u

end TransposeFollowup
