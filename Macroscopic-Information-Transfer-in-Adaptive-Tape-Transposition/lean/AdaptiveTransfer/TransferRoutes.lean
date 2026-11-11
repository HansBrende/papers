import AdaptiveTransfer.TransferBandPaths

/-! Endpoint-inclusive native dependency routes and exact concatenation.
The empty tail represents a singleton route, so cuts at either endpoint are
never silently exempted. -/
namespace AdaptiveTransfer.TransferGuards
open Finset MergeDepth

def Route {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (B : Finset ℕ) (u v : ℕ) : Prop :=
  ∃ ρ : List ℕ, IsDepPath xs T (u :: ρ) ∧ (u :: ρ).getLastD u = v ∧
    ∀ r ∈ u :: ρ, r ∉ B

namespace Route
variable {k T u v w : ℕ} {xs : Fin k → ℕ → ℤ} {B : Finset ℕ}

theorem refl (hu : u ∉ B) : Route xs T B u u := by
  refine ⟨[], trivial, rfl, ?_⟩
  intro r hr
  have hr' : r = u := by simpa using hr
  exact hr' ▸ hu

theorem prepend (hu : u ∉ B) (he : DepStep xs T u v) (h : Route xs T B v w) :
    Route xs T B u w := by
  obtain ⟨ρ, hρ, heq, hB⟩ := h
  refine ⟨v :: ρ, ⟨he, hρ⟩, ?_, ?_⟩
  · simpa only [List.getLastD_cons] using heq
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hu
    · exact hB r hr

theorem trans (huv : Route xs T B u v) (hvw : Route xs T B v w) : Route xs T B u w := by
  obtain ⟨ρ, hρ, hlast, hB⟩ := huv
  induction ρ generalizing u with
  | nil =>
    have he : u = v := hlast
    exact he ▸ hvw
  | cons p ρ ih =>
    apply prepend (hB u (by simp)) hρ.1
    apply ih hρ.2
    · simpa only [List.getLastD_cons] using hlast
    · exact fun r hr => hB r (List.mem_cons_of_mem _ hr)

end Route

/-- The entire closed source-spine interval supplies a route, including
when its two endpoints agree. -/
theorem spine_route {k T a u : ℕ} {xs : Fin k → ℕ → ℤ} {B : Finset ℕ}
    (hau : a ≤ u) (huT : u < T) (hB : ∀ r, a ≤ r → r ≤ u → r ∉ B) :
    Route xs T B u a := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    by_cases he : a = u
    · subst a
      exact Route.refl (hB u le_rfl le_rfl)
    · apply Route.prepend (hB u hau le_rfl) (Or.inl ⟨show u - 1 + 1 = u by omega, huT⟩)
      exact ih (u - 1) (by omega) (by omega) (by omega)
        (fun r har hru => hB r har (by omega))

end AdaptiveTransfer.TransferGuards
