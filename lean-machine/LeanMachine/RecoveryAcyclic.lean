import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-!
# Finite induced recovery acyclicity

Arcs are oriented from helper to target. Acyclic means no nonempty directed
closed walk in the induced set, so loops count as cycles. Counting strict
predecessors proves equivalence with a natural-number rank; no finiteness of
the ambient coordinate type is required.
-/

namespace LeanMachine.RecoveryAcyclic

open Finset
open scoped Classical

variable {V : Type*}

/-- Internal helper-to-target arcs, including possible loops. -/
def arc (H : V → Finset V) (A : Finset V) (x y : V) : Prop :=
  x ∈ A ∧ y ∈ A ∧ x ∈ H y

/-- No nonempty closed walk of internal helper arcs. -/
def Acyclic (H : V → Finset V) (A : Finset V) : Prop :=
  ∀ x, ¬ Relation.TransGen (arc H A) x x

/-- A natural-number rank strictly increases from every internal helper to its target. -/
def RankAcyclic (H : V → Finset V) (A : Finset V) : Prop :=
  ∃ rank : V → ℕ, ∀ x ∈ A, ∀ y ∈ A, y ∈ H x → rank y < rank x

/-- On a finite induced set, the rank certificate is exactly directed acyclicity. -/
theorem rank_iff_acyclic (H : V → Finset V) (A : Finset V) :
    RankAcyclic H A ↔ Acyclic H A := by
  constructor
  · rintro ⟨rank, hr⟩ x hx
    have hpath : ∀ {u v}, Relation.TransGen (arc H A) u v → rank u < rank v := by
      intro u v h
      induction h with
      | single h => exact hr _ h.2.1 _ h.1 h.2.2
      | tail _ h ih => exact lt_trans ih (hr _ h.2.1 _ h.1 h.2.2)
    exact (Nat.lt_irrefl _) (hpath hx)
  · intro h
    let P := fun x => A.filter (fun y => Relation.TransGen (arc H A) y x)
    refine ⟨fun x => (P x).card, ?_⟩
    intro x hx y hy hyx
    have he : arc H A y x := ⟨hy, hx, hyx⟩
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz
      exact mem_filter.mpr ⟨(mem_filter.mp hz).1,
        Relation.TransGen.tail (mem_filter.mp hz).2 he⟩
    · intro hp
      have hyP : y ∈ P x := mem_filter.mpr ⟨hy, Relation.TransGen.single he⟩
      rw [← hp] at hyP
      exact h y (mem_filter.mp hyP).2

end LeanMachine.RecoveryAcyclic
