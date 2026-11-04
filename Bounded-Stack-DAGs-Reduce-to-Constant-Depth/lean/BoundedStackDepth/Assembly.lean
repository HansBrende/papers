import BoundedStackDepth.Basic
import BoundedNesting.WalkDag

/-!
# The probabilistic method for label cuts

The paper builds, for every `k` walks, a *random* label: a finite family of labels `Ψ ω` indexed by the
random choices `ω` (grid offset, digit offsets, break bits), all with values below a bound `q` that depends
only on `k` and `ε`. Its cut (`labelCutSize`: the descents of `Ψ ω` plus its violated hop pairs) is small
on average.

* `exists_cut_of_avg`: if the average cut size over a nonempty family is at most `εT`, some member gives
  a cut of at most `εT` edges, and every label cut with values below `q` has depth at most `q − 1`
  (`labelCut_depth_walkDag` of the earlier paper).
-/

namespace BoundedStackDepth

open BoundedNesting Finset

variable {k : ℕ}

/-- The size of the cut of a label `Ψ` on the walk DAG of `xs` before `T`: its descents and its violated
hop pairs. -/
def labelCutSize (xs : Fin k → ℕ → ℤ) (T : ℕ) (Ψ : ℕ → ℕ) : ℕ :=
  (descentsOf Ψ T).card + (violatedOf Ψ (hopPairs (allHops xs T))).card

/-- **The probabilistic method for label cuts.** If a nonempty finite family of labels with values below
`q` has average cut size at most `εT`, then the walk DAG has a cut of at most `εT` edges and depth at most
`q − 1`. -/
theorem exists_cut_of_avg {α : Type*} {xs : Fin k → ℕ → ℤ} {T q : ℕ} {ε : ℝ}
    (Ω : Finset α) (hΩ : Ω.Nonempty) (Ψ : α → ℕ → ℕ) (hΨ : ∀ ω t, Ψ ω t < q)
    (havg : (∑ ω ∈ Ω, (labelCutSize xs T (Ψ ω) : ℝ)) ≤ Ω.card * (ε * T)) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hopPairs (allHops xs T) ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ f n, AvoidPath T (hopPairs (allHops xs T)) cutH cutS f n →
        arcCount (hopPairs (allHops xs T)) f n ≤ q - 1 := by
  obtain ⟨ω, -, hω⟩ := exists_le_of_sum_le hΩ
    (f := fun ω => (labelCutSize xs T (Ψ ω) : ℝ)) (g := fun _ => ε * T)
    (by rw [sum_const, nsmul_eq_mul]; exact havg)
  refine ⟨descentsOf (Ψ ω) T, violatedOf (Ψ ω) (hopPairs (allHops xs T)), filter_subset _ _,
    filter_subset _ _, ?_, fun f n hpath => labelCut_depth_walkDag xs (hΨ ω) f n hpath⟩
  exact_mod_cast hω

end BoundedStackDepth
