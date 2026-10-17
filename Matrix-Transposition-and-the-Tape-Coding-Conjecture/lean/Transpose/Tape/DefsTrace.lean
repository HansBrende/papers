import Transpose.Tape.DefsM

/-!
# Definitions: block-level traces (the Block Locality Lemma, adaptive machines)

* `blockTrace M n b r T w y`: the block-level trace of the run on `w` at slot `y` (slot length `r`,
  time `T`). It records the resident blocks of every work tape (pair residency `pairRes`), the input
  rows touched (`srcRows` of the slot) and the output length at the slot's first step, which fixes
  the output positions appended in each slot.
* `SameTrace M n b r T w w'`: the traces agree at every slot `y ≤ ⌈T/r⌉`.
* `TraceClass M n b r T F w₀`: `F` is a set of matrix inputs containing `w₀`, all halting after
  exactly `T` steps with the trace of `w₀`. For an oblivious machine, all matrix inputs form one
  class.
* `rescaledTrajOf M n w t`: the rescaled trajectory `P_t^{(n)}` of work head `t` on input `w`.
  `rescaledTraj` is the case `w = zeroInput n`.
* `traceCount k n N T`: an explicit bound on the number of pairs (halting time `≤ T`, trace on the
  slots `y ≤ N`), used to find a popular trace class.
* `traceConst M c`: the explicit constant `C` of `⌈log₂ traceCount⌉ ≤ C n b` for `T ≤ c L`.
-/

namespace Transpose.Tape

open Transpose

/-- The block-level trace at slot `y`: the resident blocks of every work tape, the input rows
touched, and the output length at the slot's first step `y r`. -/
noncomputable def blockTrace (M : TM) (n b r T : ℕ) (w : List Bool) (y : ℕ) :
    (Fin M.k → Finset ℤ) × Finset ℕ × ℕ :=
  (fun t => pairRes r (fun τ => workTraj M w τ t) T y, srcRows M w n b (slotOf r T y),
    (run M w (y * r)).outRev.length)

/-- `w` and `w'` have the same block-level trace at every slot `y ≤ ⌈T/r⌉`. -/
def SameTrace (M : TM) (n b r T : ℕ) (w w' : List Bool) : Prop :=
  ∀ y ≤ numSlots r T, blockTrace M n b r T w y = blockTrace M n b r T w' y

/-- A **trace class**: a set `F` of matrix inputs that contains `w₀`, all halting after exactly `T`
steps with the block-level trace of `w₀`. -/
def TraceClass (M : TM) (n b r T : ℕ) (F : Set (List Bool)) (w₀ : List Bool) : Prop :=
  w₀ ∈ F ∧ ∀ w ∈ F, w ∈ matrixInputs n b ∧ HaltsAt M w T ∧ SameTrace M n b r T w w₀

/-- The rescaled trajectory `P_t^{(n)}(u)` on input `w`: the block of work head `t` at the first
step of slot `⌊u n⌋`, divided by `n`. -/
noncomputable def rescaledTrajOf (M : TM) (n : ℕ) (w : List Bool) (t : Fin M.k) (u : ℝ) : ℝ :=
  (curBlock (slotLen M n) (fun τ => workTraj M w τ t) (⌊u * n⌋₊ * slotLen M n) : ℝ) / n

/-- An explicit bound on the number of pairs (halting time `≤ T`, trace on the slots `y ≤ N`),
when every block index lies in `[-N, N]`, every residency has at most `3` blocks, every slot
touches at most `2` of the `n` input rows, and every output length is at most `T`. -/
def traceCount (k n N T : ℕ) : ℕ :=
  (T + 1) * ((2 * N + 2) ^ (3 * k) * (n + 1) ^ 2 * (T + 1)) ^ (N + 1)

/-- The constant `C` of the bound `⌈log₂ traceCount⌉ ≤ C n b` (for `T ≤ c L` and slot length
`slotLen M n`). -/
noncomputable def traceConst (M : TM) (c : ℝ) : ℕ :=
  (Nat.clog 2 (2 * ⌈c⌉₊ + 1) + 3) + (⌈horizon M c⌉₊ + 1) *
    (3 * M.k * Nat.clog 2 (2 * ⌈horizon M c⌉₊ + 2) + 3 * M.k + 7 + Nat.clog 2 (2 * ⌈c⌉₊ + 1))

end Transpose.Tape
