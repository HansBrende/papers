import Mathlib

/-!
# Cuts are labels

A label `Ψ` with values in `[0, q)` defines a cut of a walk DAG: delete the hop edges along which
`Ψ` does not decrease and the state edges along which it increases. Along a path of the remaining
DAG the label never increases and decreases strictly at every hop edge, so a path carries at most
`q − 1` hop edges (`depth_le_of_label`). This is the lemma "cuts are labels" of the series' fourth
paper, stated for an arbitrary path `f 0, f 1, …, f n` with marked (hop) steps.
-/

namespace BoundedNesting

open Finset

/-- Along a label-non-increasing path, the number of strictly decreasing marked steps is at most
the total decrease. -/
theorem card_marked_add_le {α : Type*} (Ψ : α → ℕ) (f : ℕ → α) (marked : ℕ → Prop)
    [DecidablePred marked] :
    ∀ n, (∀ i < n, Ψ (f (i + 1)) ≤ Ψ (f i)) → (∀ i < n, marked i → Ψ (f (i + 1)) < Ψ (f i)) →
      ((range n).filter marked).card + Ψ (f n) ≤ Ψ (f 0) := by
  intro n
  induction n with
  | zero => intro _ _; simp
  | succ n ih =>
    intro hmono hstrict
    have h := ih (fun i hi => hmono i (by omega)) (fun i hi => hstrict i (by omega))
    have hm := hmono n (by omega)
    rw [range_add_one, filter_insert]
    split_ifs with hmk
    · have hs := hstrict n (by omega) hmk
      rw [card_insert_of_notMem (by simp)]
      omega
    · omega

/-- **Cuts are labels.** Along a path on which a label with values in `[0, q)` never increases
and strictly decreases at every marked step, at most `q − 1` steps are marked. -/
theorem depth_le_of_label {α : Type*} {q : ℕ} (Ψ : α → ℕ) (hΨ : ∀ a, Ψ a < q) (f : ℕ → α)
    (n : ℕ) (marked : ℕ → Prop) [DecidablePred marked]
    (hmono : ∀ i < n, Ψ (f (i + 1)) ≤ Ψ (f i))
    (hstrict : ∀ i < n, marked i → Ψ (f (i + 1)) < Ψ (f i)) :
    ((range n).filter marked).card ≤ q - 1 := by
  have h := card_marked_add_le Ψ f marked n hmono hstrict
  have := hΨ (f 0)
  omega

end BoundedNesting
