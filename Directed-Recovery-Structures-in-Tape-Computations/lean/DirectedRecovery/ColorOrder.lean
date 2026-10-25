import LeanMachine.ColorOrder
import MotionDepthCodes.StorageCode

/-!
# The port-color half bound

Only colors used by the finite coordinate set are ordered. The storage-code
predicate is the one from the fourth paper, without modification.
-/

namespace DirectedRecovery

open Finset MotionDepthCodes

/-- A monochromatic port coloring that separates every demand pair bounds every
storage code by half the coordinates. The color type need not be finite. -/
theorem color_order_half_bound {V α κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [Nonempty α] (N : V → Finset V) (left right : V → κ)
    (hcolors : ∀ q, left q ≠ right q)
    (hedge : ∀ q p, p ∈ N q → left p = right q)
    {C : Finset (V → α)} (hC : IsStorageCode N C) :
    C.card ≤ Fintype.card α ^ (Fintype.card V / 2) := by
  classical
  let U : Finset κ := univ.image left ∪ univ.image right
  let left' : V → U := fun q => ⟨left q, by simp [U]⟩
  let right' : V → U := fun q => ⟨right q, by simp [U]⟩
  let e := Fintype.equivFin U
  apply LeanMachine.ColorOrder.card_le_pow_half N
    (fun q => e (left' q)) (fun q => e (right' q)) ?_ ?_ C hC
  · intro q heq
    exact hcolors q (congrArg Subtype.val (e.injective heq))
  · intro q p hp
    apply congrArg e
    apply Subtype.ext
    exact hedge q p hp

end DirectedRecovery
