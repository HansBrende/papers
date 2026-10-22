import TransposeFollowup.LocalProtocol
import TransposeFollowup.MatrixView

/-!
# Interface for the adaptive original-row coding theorem

The helper may be any deterministic function of the input. Once it is fixed,
all support choices and stopping are determined by the public transcript.
Query supports may have any finite size; their interaction graph completes each
support to a clique. Every receiver has only its own original row, the helper, and that transcript.
Correctness can be restricted to an arbitrary, possibly correlated family.
-/

namespace TransposeFollowup

set_option autoImplicit false

structure RowCode (n b : ℕ) (H : Type*) where
  helper : FiniteMatrix n b → H
  protocol : H → PublicProtocol (Fin n) (fun _ => Row n b)
  decode : H → Fin n → Row n b → List Bool → Row n b

namespace RowCode

variable {n b : ℕ} {H : Type*}

def transcript (C : RowCode n b H) (x : FiniteMatrix n b) : List Bool :=
  (C.protocol (C.helper x)).run x

def CorrectOn (C : RowCode n b H) (F : Set (FiniteMatrix n b)) : Prop :=
  ∀ x ∈ F, ∀ j, C.decode (C.helper x) j (x j) (C.transcript x) = transposed x j

/-- The full virtual fiber fixes the helper as a public parameter, without
requiring inputs in that fiber to have that actual helper value. -/
def leafFiber (C : RowCode n b H) (z : H) (m : List Bool) :
    Set (FiniteMatrix n b) := {x | (C.protocol z).run x = m}

/-- Correctness is used only on the actual helper-consistent subfamily. -/
def correctFiber (C : RowCode n b H) (F : Set (FiniteMatrix n b))
    (z : H) (m : List Bool) : Set (FiniteMatrix n b) :=
  {x | x ∈ F ∧ C.helper x = z ∧ C.transcript x = m}

theorem correctFiber_subset_leafFiber (C : RowCode n b H)
    (F : Set (FiniteMatrix n b)) (z : H) (m : List Bool) :
    C.correctFiber F z m ⊆ C.leafFiber z m := by
  rintro x ⟨_, hz, hm⟩
  simpa [leafFiber, transcript, hz] using hm

/-- Individual receivers, rather than a joint decoder, determine each column
inside a correct fiber from that receiver's original row. -/
theorem column_eq_of_same_view (C : RowCode n b H)
    {F : Set (FiniteMatrix n b)} (hc : C.CorrectOn F)
    {x y : FiniteMatrix n b} (hx : x ∈ F) (hy : y ∈ F)
    (hz : C.helper x = C.helper y) (hm : C.transcript x = C.transcript y)
    (j : Fin n) (hr : x j = y j) :
    transposed x j = transposed y j := by
  rw [← hc x hx j, ← hc y hy j, hz, hm, hr]

end RowCode
end TransposeFollowup
