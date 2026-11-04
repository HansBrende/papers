import BoundedNesting.Stacks

/-!
# The main statement and its corollary for stack DAGs

The paper's main theorem is `TCP k` for every `k`: the walk DAG of any `k` walks, pauses allowed, can be
cut by an `ε`-fraction of its edges to a depth bounded independently of the length. This file states it
as a proposition and derives, from the earlier paper's formal reductions (`tcpnp_of_tcp`,
`sr_of_tcpnp`), depth reduction for `s`-stack DAGs with a spine, `SR s`.

The main theorem is proved in `Main.lean`: `tcpAt_direct` gives the explicit depth, and `main`,
`tcp` and `sr` follow.
-/

namespace BoundedStackDepth

open BoundedNesting

/-- The main theorem of the paper, as a proposition: TCP for every number of walks. -/
def MainStatement : Prop := ∀ k : ℕ, TCP k

/-- The main theorem gives depth reduction for `s`-stack DAGs with a spine, for every `s`. -/
theorem sr_of_main (h : MainStatement) (s : ℕ) : SR s :=
  sr_of_tcpnp (tcpnp_of_tcp (h s))

end BoundedStackDepth
