import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic

/-!
# Recovery along a well-founded dependency relation

Local recovery on a selected coordinate set extends to recovery of the whole
input from one helper and the coordinate complement. The alphabet and the
sample family are arbitrary. An increasing natural rank on dependencies is
sufficient on a finite coordinate type; injectivity of the rank is unnecessary.
-/

namespace LeanMachine.OrderedRecovery

variable {Ω V α H : Type*}

/-- The same helper and the unselected coordinates determine every coordinate
when the selected dependencies are well founded. -/
theorem eq_of_wellFounded (X : Ω → V → α) (Z : Ω → H)
    (A : Set V) (N : V → Set V) (r : V → V → Prop) (hr : WellFounded r)
    (hforward : ∀ v ∈ A, ∀ u ∈ N v, u ∈ A → r u v)
    (hlocal : ∀ v ∈ A, ∀ x y, Z x = Z y →
      Set.EqOn (X x) (X y) (N v) → X x v = X y v)
    {x y : Ω} (hZ : Z x = Z y) (hout : Set.EqOn (X x) (X y) Aᶜ) :
    X x = X y := by
  funext v
  exact hr.induction v fun v ih => by
    classical
    by_cases hv : v ∈ A
    · apply hlocal v hv x y hZ
      intro u hu
      by_cases hA : u ∈ A
      · exact ih u (hforward v hv u hu hA)
      · exact hout hA
    · exact hout hv

/-- Strictly increasing dependency ranks permit reverse recovery on a finite
coordinate type. Equal ranks at unrelated coordinates cause no difficulty. -/
theorem eq_of_rank [Fintype V] (X : Ω → V → α) (Z : Ω → H)
    (A : Set V) (N : V → Set V) (rank : V → ℕ)
    (hforward : ∀ v ∈ A, ∀ u ∈ N v, u ∈ A → rank v < rank u)
    (hlocal : ∀ v ∈ A, ∀ x y, Z x = Z y →
      Set.EqOn (X x) (X y) (N v) → X x v = X y v)
    {x y : Ω} (hZ : Z x = Z y) (hout : Set.EqOn (X x) (X y) Aᶜ) :
    X x = X y := by
  classical
  let M := Finset.univ.sup rank
  have hM (v : V) : rank v ≤ M := Finset.le_sup (Finset.mem_univ v)
  apply eq_of_wellFounded X Z A N _ (measure (fun v => M - rank v)).wf
    (fun v hv u hu hA => ?_) hlocal hZ hout
  change M - rank u < M - rank v
  have hf := hforward v hv u hu hA
  have hmu := hM u
  omega

end LeanMachine.OrderedRecovery
