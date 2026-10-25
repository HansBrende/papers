import SubcubicMemo.SquareConnected

/-! Every finite triangle-free subcubic graph whose edges lie in four-cycles
maps to the circular clique K_(8/3), and satisfies the weighted half bound. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem component_hyp (h : Hyp G) (C : G.ConnectedComponent) : Hyp C.toSimpleGraph where
  triangle := (G.cliqueFree_induce_iff C.supp 3).mpr (fun {_} _ => h.triangle _)
  degree v := by
    have he : C.toSimpleGraph.degree v = (G.induce C.supp).degree v := by
      rw [← SimpleGraph.ncard_neighborSet,← SimpleGraph.ncard_neighborSet]
      rfl
    rw [he,G.degree_induce_of_neighborSet_subset (fun w hw => C.mem_supp_of_adj_mem_supp v.property hw)]
    exact h.degree v
  covered u v huv := by
    obtain ⟨a,b,s⟩ := h.covered u v huv
    have ha := C.mem_supp_of_adj_mem_supp v.property s.2.1
    have hb := C.mem_supp_of_adj_mem_supp u.property s.2.2.2.1.symm
    exact ⟨⟨a,ha⟩,⟨b,hb⟩,s.1,s.2.1,s.2.2.1,s.2.2.2.1,
      fun he => s.2.2.2.2.1 (congrArg Subtype.val he),
      fun he => s.2.2.2.2.2 (congrArg Subtype.val he)⟩

theorem target (h : Hyp G) : Nonempty (G →g circularClique 8 3) := by
  let f (C : G.ConnectedComponent) : C.toSimpleGraph →g circularClique 8 3 :=
    (connected_target (component_hyp h C) C.connected_toSimpleGraph.preconnected).some
  refine ⟨{ toFun := fun v => f (G.connectedComponentMk v) ⟨v,rfl⟩, map_rel' := ?_ }⟩
  intro u v huv
  have he : G.connectedComponentMk v = G.connectedComponentMk u :=
    SimpleGraph.ConnectedComponent.sound huv.symm.reachable
  have hh := (f (G.connectedComponentMk u)).map_adj
    (v := ⟨u,rfl⟩) (w := ⟨v,he⟩) huv
  convert hh using 1
  have transport (C D : G.ConnectedComponent) (he : C=D) (hv : v ∈ C) :
      f C ⟨v,hv⟩ = f D ⟨v,he ▸ hv⟩ := by subst D; rfl
  exact transport _ _ he rfl

theorem good (h : Hyp G) : IsGood G :=
  IsGood.of_hom (rateBound_circularClique_of_le (p := 8) (q := 3) (by norm_num))
    (target h).some

end SubcubicMemo.Squares

namespace SubcubicMemo

open MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem squareCore_good (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    RateBound (nbhd (squareCore G)) (1/2) := by
  apply Squares.good
  exact { triangle := SimpleGraph.CliqueFree.anti (squareCore_le G) htri
          degree := fun v => (SimpleGraph.degree_le_of_le (squareCore_le G)).trans (hdeg v)
          covered := fun _ _ h => squareCore_covered G h }

end SubcubicMemo
