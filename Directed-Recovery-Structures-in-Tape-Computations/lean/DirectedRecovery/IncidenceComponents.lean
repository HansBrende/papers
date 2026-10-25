import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.EquivFin
import LeanMachine.ColorOrder
import MotionDepthCodes.StorageCode

/-!
# Codes with separated paired incidence components

The two copies of each coordinate are distinct ports.  Only the incidence
`inl p -- inr q` represents membership `p ∈ N q`; there is no undirected
closure on the coordinate set.  Component colors then permit the ordered
decoding theorem, for arbitrary finite-alphabet storage codes.
-/

namespace DirectedRecovery

open MotionDepthCodes
set_option autoImplicit false

variable {V α : Type*}

/-- The paired incidence graph of a directed recovery relation.  Left ports
are `Sum.inl` and right ports are `Sum.inr`. -/
def pairedIncidenceGraph (N : V → Finset V) : SimpleGraph (V ⊕ V) where
  Adj u v := match u, v with
    | Sum.inl p, Sum.inr q => p ∈ N q
    | Sum.inr q, Sum.inl p => p ∈ N q
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact id⟩

@[simp] theorem pairedIncidenceGraph_adj_left_right (N : V → Finset V) (p q : V) :
    (pairedIncidenceGraph N).Adj (Sum.inl p) (Sum.inr q) ↔ p ∈ N q := Iff.rfl

@[simp] theorem pairedIncidenceGraph_adj_right_left (N : V → Finset V) (p q : V) :
    (pairedIncidenceGraph N).Adj (Sum.inr q) (Sum.inl p) ↔ p ∈ N q := Iff.rfl

@[simp] theorem pairedIncidenceGraph_not_adj_left_left (N : V → Finset V) (p q : V) :
    ¬(pairedIncidenceGraph N).Adj (Sum.inl p) (Sum.inl q) := id

@[simp] theorem pairedIncidenceGraph_not_adj_right_right (N : V → Finset V) (p q : V) :
    ¬(pairedIncidenceGraph N).Adj (Sum.inr p) (Sum.inr q) := id

/-- An incidence edge identifies the component of its input port with the
component of its receiver port. -/
theorem incidence_components_eq {N : V → Finset V} {p q : V} (hp : p ∈ N q) :
    (pairedIncidenceGraph N).connectedComponentMk (Sum.inl p) =
      (pairedIncidenceGraph N).connectedComponentMk (Sum.inr q) :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hp

variable [Fintype V] [DecidableEq V] [Fintype α] [Nonempty α]

/-- The separated-component lemma, with the exact integral half exponent.
The code can be empty and its recovery maps need not be linear. -/
theorem storageCode_card_le_of_separated_components
    (N : V → Finset V)
    (hsep : ∀ p, (pairedIncidenceGraph N).connectedComponentMk (Sum.inl p) ≠
      (pairedIncidenceGraph N).connectedComponentMk (Sum.inr p))
    (C : Finset (V → α)) (hC : IsStorageCode N C) :
    C.card ≤ Fintype.card α ^ (Fintype.card V / 2) := by
  classical
  let κ := (pairedIncidenceGraph N).ConnectedComponent
  let : Fintype κ := Fintype.ofFinite κ
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let left : V → Fin (Fintype.card κ) :=
    fun p => e ((pairedIncidenceGraph N).connectedComponentMk (Sum.inl p))
  let right : V → Fin (Fintype.card κ) :=
    fun q => e ((pairedIncidenceGraph N).connectedComponentMk (Sum.inr q))
  apply LeanMachine.ColorOrder.card_le_pow_half N left right
  · intro p hp
    exact hsep p (e.injective hp)
  · intro q p hp
    exact congrArg e (incidence_components_eq hp)
  · exact hC

/-- The same exact bound with disconnectedness stated as nonreachability. -/
theorem storageCode_card_le_of_unreachable_pairs
    (N : V → Finset V)
    (hsep : ∀ p, ¬(pairedIncidenceGraph N).Reachable (Sum.inl p) (Sum.inr p))
    (C : Finset (V → α)) (hC : IsStorageCode N C) :
    C.card ≤ Fintype.card α ^ (Fintype.card V / 2) := by
  apply storageCode_card_le_of_separated_components N _ C hC
  intro p hp
  exact hsep p (SimpleGraph.ConnectedComponent.exact hp)

end DirectedRecovery
