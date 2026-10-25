import CircularMemo.Circular
import MotionDepthCodes.RateHalf

/-! # Storage codes on the extended circular range

The entropy and integer-cardinality machinery is imported unchanged from
the fourth paper. This module only supplies its stronger graph premise.
-/

namespace CircularMemo

open MotionDepthCodes

/-- Arbitrary finite-alphabet storage codes on a graph mapping to a
circular clique of ratio below three satisfy the integer half bound. -/
theorem card_sq_le_of_circularHom {V α : Type*}
    [Fintype V] [DecidableEq V] [Fintype α] [Nonempty α]
    {G : SimpleGraph V} [DecidableRel G.Adj] {p q : ℕ}
    (hq : 0 < q) (hpq : p < 3 * q) (φ : G →g circularClique p q)
    {C : Finset (V → α)} (hC : IsStorageCode (nbhd G) C) :
    C.card ^ 2 ≤ Fintype.card α ^ Fintype.card V :=
  card_sq_le_of_rateBound_half (rateBound_of_circularHom hq hpq φ) hC

end CircularMemo
