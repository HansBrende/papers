import LeanMachine.FlowPaths
import Mathlib.Combinatorics.Quiver.Covering
import Mathlib.Data.List.Count

/-! Incidence-preserving path maps and lifting through a forward-closed
subnetwork. Edge identities and traversal multiplicities are retained. -/

namespace LeanMachine.FiniteFlow.Network

open scoped Classical
noncomputable section

variable {V E V' E' : Type*} (G : Network V E) (H : Network V' E')

/-- A map of vertices and edges preserving incidence. Capacities need not
be related; their comparison is a separate obligation. -/
structure Map where
  node : V → V'
  edge : E → E'
  source : ∀ e, H.source (edge e) = node (G.source e)
  target : ∀ e, H.target (edge e) = node (G.target e)

namespace Map

variable {G H} (M : G.Map H)

def prefunctor : @Prefunctor V G.quiver V' H.quiver := by
  letI := G.quiver
  letI := H.quiver
  exact { obj := M.node
          map := fun e => ⟨M.edge e.val,
            (M.source e.val).trans (congrArg M.node e.property.1),
            (M.target e.val).trans (congrArg M.node e.property.2)⟩ }

def path {s t : V} (p : G.Path s t) : H.Path (M.node s) (M.node t) := by
  letI := G.quiver
  letI := H.quiver
  exact M.prefunctor.mapPath p

theorem pathEdges_map {s t : V} (p : G.Path s t) :
    H.pathEdges (M.path p) = (G.pathEdges p).map M.edge := by
  let := G.quiver
  let := H.quiver
  induction p with
  | nil => rfl
  | cons p e ih =>
    change H.pathEdges ((M.prefunctor.mapPath p).cons (M.prefunctor.map e)) = _
    rw [H.pathEdges_cons, G.pathEdges_cons, List.map_append]
    simpa [path, prefunctor] using congrArg (fun l => l ++ [M.edge e.val]) ih

theorem pathFlow_map_of_injective (hinj : Function.Injective M.edge)
    {s t : V} (p : G.Path s t) (e : E) :
    H.pathFlow (M.path p) (M.edge e) = G.pathFlow p e := by
  rw [H.pathFlow_eq_count, G.pathFlow_eq_count, M.pathEdges_map,
    List.count_map_of_injective _ _ hinj]

theorem pathFlow_map_outside {s t : V} (p : G.Path s t) (e : E')
    (he : e ∉ Set.range M.edge) : H.pathFlow (M.path p) e = 0 := by
  rw [H.pathFlow_eq_count, M.pathEdges_map]
  have hn : e ∉ (G.pathEdges p).map M.edge := by
    rintro h
    obtain ⟨e', _, he'⟩ := List.mem_map.mp h
    exact he ⟨e', he'⟩
  simp [List.count_eq_zero_of_not_mem hn]

/-- Surjectivity on outgoing stars suffices to lift paths. Unlike a full
quiver covering, no condition on incoming arrows is required. -/
theorem lift_path (hinj : Function.Injective M.node)
    (hout : ∀ u e', H.source e' = M.node u →
      ∃ e, G.source e = u ∧ M.edge e = e')
    {s t : V} (p : H.Path (M.node s) (M.node t)) :
    ∃ q : G.Path s t, M.path q = p := by
  let := G.quiver
  let := H.quiver
  have hstar : ∀ u, Function.Surjective (M.prefunctor.star u) := by
    intro u ⟨v, e'⟩
    rcases e' with ⟨e', hs', ht'⟩
    obtain ⟨e, hs, he⟩ := hout u e' hs'
    subst e'
    have hv : M.node (G.target e) = v := (M.target e).symm.trans ht'
    cases hv
    exact ⟨⟨G.target e, ⟨e, hs, rfl⟩⟩, rfl⟩
  obtain ⟨⟨v, q⟩, he⟩ := M.prefunctor.pathStar_surjective hstar s ⟨M.node t, p⟩
  have hv : M.node v = M.node t := congrArg Sigma.fst he
  obtain rfl := hinj hv
  exact ⟨q, (Sigma.mk.inj_iff.mp he).2.eq⟩

end Map

variable {G} {s u t : V}

abbrev pathComp (p : G.Path s u) (q : G.Path u t) : G.Path s t :=
  @Quiver.Path.comp _ G.quiver s u t p q

theorem pathEdges_comp (p : G.Path s u) (q : G.Path u t) :
    G.pathEdges (pathComp p q) = G.pathEdges p ++ G.pathEdges q := by
  induction q with
  | nil => simp [pathEdges]
  | cons q e ih => simp only [Quiver.Path.comp_cons, pathEdges_cons, ih, List.append_assoc]

theorem pathFlow_comp (p : G.Path s u) (q : G.Path u t) :
    G.pathFlow (pathComp p q) = G.pathFlow p + G.pathFlow q := by
  induction q with
  | nil => simp [pathFlow]
  | cons q e ih => simp only [Quiver.Path.comp_cons, pathFlow_cons, ih, add_assoc]

end
end LeanMachine.FiniteFlow.Network
