import Transpose.Tape.DefsP

/-!
# Definitions: Theorem P′ (data-dependent heads)

For a machine whose head motion, output schedule and running time depend on the input, every input
`w` has its own pass partition and its own dependency forest (`forest`, built from `w`'s run). The
proof of P′ conditions on a **structure code** of the forest of a column group and on its
**side information**:
* `nodeCode M w J`: for a nonempty node `J` (an interval of steps), its first and last steps, the
  positions of the input head and of every work head at the first step, and the output length at the
  first step; `none` for an empty node. (A richer per-node structure, with the pass index, the head
  positions at both endpoints and the last-visit profile, is not needed.)
* `sideCode M w J`: the state and the `k` symbols under the work heads at the first step of `J`
  (the side information, `σ` bits).
* `structCount k T = (2T+1)^{k+4}`: an upper bound on the number of node codes when every step
  is `< T`. In bits this is `(k+4)⌈log₂(2T+1)⌉`, at most `γ = ⌈log₂ r⌉ + 2(k+2)⌈log₂(2T+3)⌉`
  (`structBits_le`), the structure cost of `theoremPprime_gamma`.
-/

namespace Transpose.Tape

open Transpose

/-- The data of a forest node recorded by the structure code. -/
abbrev NodeCode (k : ℕ) := Option (ℕ × ℕ × ℤ × (Fin k → ℤ) × ℕ)

/-- The structure code of a step set `J` on input `w`: `none` if `J` is empty; otherwise its first
and last steps, the positions of the input head and of the work heads at the first step, and the
output length at the first step. -/
noncomputable def nodeCode (M : TM) (w : List Bool) (J : Finset ℕ) : NodeCode M.k :=
  if h : J.Nonempty then
    some (J.min' h, J.max' h, (run M w (J.min' h)).inPos, (run M w (J.min' h)).workPos,
      (run M w (J.min' h)).outRev.length)
  else none

/-- The side information of a step set `J` on input `w`: the state and the symbols under the `k`
work heads at its first step. -/
noncomputable def sideCode (M : TM) (w : List Bool) (J : Finset ℕ) :
    Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1)) :=
  ((run M w (firstStep J)).state, headSym M w (firstStep J))

/-- An upper bound on the number of node codes when every step is `< T`. The first and last steps
and the output length at the first step lie in `[0, T)`, and the head positions at the first step
in `[-T, T]`, so there are at most `1 + T³ (2T+1)^{k+1} ≤ (2T+1)^{k+4}` codes. -/
def structCount (k T : ℕ) : ℕ := (2 * T + 1) ^ (k + 4)

end Transpose.Tape
