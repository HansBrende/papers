import BoundedNesting.TheoremF

/-!
# Walk DAGs and the depth of label cuts

The walk DAG of walks `xs h`, `h < k`, on the times `[0, T)` has the state edges `t → t - 1` and a hop
edge `u → p` for every long hop `(p, u)` of any head (`allHops`, `hopPairs`). A sub-DAG `G(H')`
keeps the state edges and the hop edges of a set `H'` of long hops.

`labelCut_depth`: for a label `Ψ` with values in `[0, q)` and any set of hop pairs, the cut made of
the state edges at descents (`descentsOf`) and of the violated hop edges (`violatedOf`) has depth
at most `q - 1`. This is the consequence for walk DAGs of the lemma that cuts are labels.
-/

namespace BoundedNesting

open Finset

variable {k : ℕ}

/-- All long hops of the walks `xs h` before `T`, as triples `(h, p, u)`. -/
def allHops (xs : Fin k → ℕ → ℤ) (T : ℕ) : Finset (Fin k × ℕ × ℕ) :=
  (univ ×ˢ ((range T) ×ˢ (range T))).filter (fun η => IsHop (xs η.1) T η.2.1 η.2.2)

theorem mem_allHops {xs : Fin k → ℕ → ℤ} {T : ℕ} {η : Fin k × ℕ × ℕ} :
    η ∈ allHops xs T ↔ IsHop (xs η.1) T η.2.1 η.2.2 := by
  simp only [allHops, mem_filter, mem_product, mem_univ, mem_range, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by have := h.1; have := h.2.1; omega, h.2.1⟩, h⟩

/-- The descents of a label: the times `t ∈ [1, T)` with `Ψ t < Ψ (t - 1)`. -/
def descentsOf (Ψ : ℕ → ℕ) (T : ℕ) : Finset ℕ := (Ico 1 T).filter (fun t => Ψ t < Ψ (t - 1))

/-- The violated hop pairs `(p, u)` of a label: those with `Ψ u ≤ Ψ p`. -/
def violatedOf (Ψ : ℕ → ℕ) (E : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  E.filter (fun e => Ψ e.2 ≤ Ψ e.1)

/-- **Cuts are labels, walk-DAG form.** Let `E` be a set of hop pairs `(p, u)` with `u ≥ p + 2`
and `Ψ` a label with values in `[0, q)`. Along a path `f 0, f 1, …, f n` of the DAG with the state
edges `t → t - 1` and the hop edges `u → p` for `(p, u) ∈ E` that avoids the descents and the
violated hop pairs of `Ψ`, at most `q - 1` steps are hop edges. -/
theorem labelCut_depth {T q : ℕ} {E : Finset (ℕ × ℕ)} (hE : ∀ e ∈ E, e.1 + 2 ≤ e.2)
    {Ψ : ℕ → ℕ} (hΨ : ∀ t, Ψ t < q) (f : ℕ → ℕ) (n : ℕ)
    (hpath : ∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ descentsOf Ψ T) ∨
      ((f (i + 1), f i) ∈ E ∧ (f (i + 1), f i) ∉ violatedOf Ψ E)) :
    ((range n).filter (fun i => (f (i + 1), f i) ∈ E)).card ≤ q - 1 := by
  refine depth_le_of_label Ψ hΨ f n _ (fun i hi => ?_) (fun i hi hm => ?_)
  · rcases hpath i hi with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · have : ¬ Ψ (f i) < Ψ (f i - 1) := fun hlt =>
        h4 (mem_filter.mpr ⟨mem_Ico.mpr ⟨h2, h3⟩, hlt⟩)
      rw [show f (i + 1) = f i - 1 by omega]
      exact not_lt.mp this
    · have : ¬ Ψ (f i) ≤ Ψ (f (i + 1)) := fun hle => h2 (mem_filter.mpr ⟨h1, hle⟩)
      exact (not_le.mp this).le
  · rcases hpath i hi with ⟨h1, -, -, -⟩ | ⟨h1, h2⟩
    · have := hE _ hm
      simp only at this
      omega
    · have : ¬ Ψ (f i) ≤ Ψ (f (i + 1)) := fun hle => h2 (mem_filter.mpr ⟨h1, hle⟩)
      exact not_le.mp this

/-- The walk-DAG form for the walk DAG itself: the hop pairs of all long hops. -/
theorem labelCut_depth_walkDag {T q : ℕ} (xs : Fin k → ℕ → ℤ) {Ψ : ℕ → ℕ} (hΨ : ∀ t, Ψ t < q)
    (f : ℕ → ℕ) (n : ℕ)
    (hpath : ∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ descentsOf Ψ T) ∨
      ((f (i + 1), f i) ∈ hopPairs (allHops xs T) ∧
        (f (i + 1), f i) ∉ violatedOf Ψ (hopPairs (allHops xs T)))) :
    ((range n).filter (fun i => (f (i + 1), f i) ∈ hopPairs (allHops xs T))).card ≤ q - 1 := by
  refine labelCut_depth (fun e he => ?_) hΨ f n hpath
  obtain ⟨η, hη, rfl⟩ := mem_image.mp he
  exact (mem_allHops.mp hη).1

end BoundedNesting
