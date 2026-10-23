import TransposeFollowup.AdaptiveBankRefinement
import TransposeFollowup.ComponentDistance
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Canonical rooted paths in an actual coordinate forest. Roots and paths
are analytical functions of the public leaf graph, never private advice. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace AdaptiveForest

variable {V : Type*} (G : SimpleGraph V)

noncomputable def componentRoot (c : G.ConnectedComponent) : V := c.exists_rep.choose

noncomputable def root (v : V) : V := componentRoot G (G.connectedComponentMk v)

theorem root_reachable (v : V) : G.Reachable (root G v) v := by
  apply SimpleGraph.ConnectedComponent.exact
  exact (G.connectedComponentMk v).exists_rep.choose_spec

theorem root_eq_of_reachable {v w : V} (h : G.Reachable v w) : root G v = root G w := by
  exact congrArg (componentRoot G) (SimpleGraph.ConnectedComponent.sound h)

noncomputable def path (v : V) : G.Walk (root G v) v :=
  (root_reachable G v).exists_path_of_dist.choose

theorem path_isPath (v : V) : (path G v).IsPath :=
  (root_reachable G v).exists_path_of_dist.choose_spec.1

theorem path_length (v : V) : (path G v).length = G.dist (root G v) v :=
  (root_reachable G v).exists_path_of_dist.choose_spec.2

noncomputable def depth (v : V) : ℕ := (path G v).length

/-- On a forest edge, one rooted path is precisely the other with the new
endpoint appended. This is stronger than merely differing depths. -/
theorem support_extend_of_adj (hG : G.IsAcyclic) {v w : V} (hvw : G.Adj v w) :
    (path G w).support = (path G v).support ++ [w] ∨
      (path G v).support = (path G w).support ++ [v] := by
  let q : G.Walk (root G v) w :=
    (path G w).copy (root_eq_of_reachable G hvw.reachable).symm rfl
  have hq : q.IsPath := by simpa [q] using path_isPath G w
  by_cases hv : v ∈ q.support
  · have he := hG.path_concat (path_isPath G v) hq hvw hv
    left
    have hs := congrArg SimpleGraph.Walk.support he
    simpa [q, SimpleGraph.Walk.support_concat] using hs
  · have hw := hG.mem_support_of_ne_mem_support_of_adj_of_isPath
      (path_isPath G v) hq hvw hv
    have he := hG.path_concat hq (path_isPath G v) hvw.symm hw
    right
    have hs := congrArg SimpleGraph.Walk.support he
    simpa [q, SimpleGraph.Walk.support_concat] using hs

theorem depth_step_of_adj (hG : G.IsAcyclic) {v w : V} (hvw : G.Adj v w) :
    depth G w = depth G v + 1 ∨ depth G v = depth G w + 1 := by
  rcases support_extend_of_adj G hG hvw with h | h
  · left
    have hl := congrArg List.length h
    simp only [SimpleGraph.Walk.length_support, List.length_append,
      List.length_singleton] at hl
    dsimp [depth]
    omega
  · right
    have hl := congrArg List.length h
    simp only [SimpleGraph.Walk.length_support, List.length_append,
      List.length_singleton] at hl
    dsimp [depth]
    omega

theorem depth_eq_zero_iff (v : V) : depth G v = 0 ↔ root G v = v := by
  rw [depth, path_length]
  exact (root_reachable G v).dist_eq_zero_iff

end AdaptiveForest

end TransposeFollowup
