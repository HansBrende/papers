import BoundedNesting.Stacks
import MergeDepth.ColdGenie

/-!
# Noncrossing pages survive chronological window contraction

The fine walk graph already has `2k` stack pages (`walkDag_isStack`). This
file reuses that theorem: identifying consecutive times cannot create a
strict crossing. The resulting pages may have arbitrarily many edges at a
vertex. They are NOT asserted to satisfy `StackDag`'s endpoint uniqueness.

`timeWindow_dependency_pages` covers the quotient of the exact native
`DepStep` relation: consecutive-window edges form the spine, and every other
edge belongs to one of `2k` noncrossing pages. Pauses and visits at the first
step of a window are included. For the last-pre-window-label description in
the note, choose the first visit to the witnessing cell in the later window;
the identification of that label description with this quotient is written,
not separately formalized here.

Check from `High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean/`:
`lake env lean ../../lean-backlog/WindowPages.lean`.
-/

namespace LeanBacklog.WindowPages

open Finset BoundedNesting MergeDepth

/-- A page can share endpoints; only strict interleaving is forbidden. -/
def Noncrossing (E : Finset (ℕ × ℕ)) : Prop :=
  ∀ e ∈ E, ∀ e' ∈ E, ¬ (e.1 < e'.1 ∧ e'.1 < e.2 ∧ e.2 < e'.2)

/-- Contract time intervals, remove loops, and merge repeated edges. -/
def contractPage (f : ℕ → ℕ) (E : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (E.image fun e => (f e.1, f e.2)).filter fun e => e.1 < e.2

private theorem lt_of_image_lt {f : ℕ → ℕ} (hf : Monotone f)
    {a b : ℕ} (h : f a < f b) : a < b := by
  by_contra hn
  have := hf (show b ≤ a by omega)
  omega

/-- A nondecreasing quotient of one page is still noncrossing. -/
theorem contractPage_noncrossing {f : ℕ → ℕ} (hf : Monotone f)
    {E : Finset (ℕ × ℕ)} (hE : Noncrossing E) :
    Noncrossing (contractPage f E) := by
  intro e he e' he' hcross
  obtain ⟨a, ha, rfl⟩ := mem_image.mp (mem_filter.mp he).1
  obtain ⟨b, hb, rfl⟩ := mem_image.mp (mem_filter.mp he').1
  exact hE a ha b hb ⟨lt_of_image_lt hf hcross.1,
    lt_of_image_lt hf hcross.2.1, lt_of_image_lt hf hcross.2.2⟩

/-- The fine walk's existing stack decomposition supplies quotient pages.
No matching/endpoint-uniqueness condition is claimed for these pages. -/
theorem walk_contracted_pages {k T : ℕ} (xs : Fin k → ℕ → ℤ)
    (hx : ∀ j, IsWalk (xs j)) {f : ℕ → ℕ} (hf : Monotone f) :
    ∃ pages : Fin (2 * k) → Finset (ℕ × ℕ),
      (∀ c, Noncrossing (pages c)) ∧
      ∀ p u, (p, u) ∈ hopPairs (allHops xs T) → f p < f u →
        ∃ c, (f p, f u) ∈ pages c := by
  obtain ⟨H, hH⟩ := walkDag_isStack xs hx T
  refine ⟨fun c => contractPage f (H.arcs c),
    fun c => contractPage_noncrossing hf (H.noCross c), ?_⟩
  intro p u hpu hlt
  have hmem : (p, u) ∈ H.arcSet := by simpa [hH] using hpu
  obtain ⟨c, -, hc⟩ := mem_biUnion.mp hmem
  exact ⟨c, mem_filter.mpr ⟨mem_image.mpr ⟨(p, u), hc, rfl⟩, hlt⟩⟩

/-- Contracting the exact dependency relation adds only the coarse spine
when the chronological quotient increases by at most one each step. -/
theorem contracted_dependency_pages {k T : ℕ} (xs : Fin k → ℕ → ℤ)
    (hx : ∀ j, IsWalk (xs j)) {f : ℕ → ℕ} (hf : Monotone f)
    (hstep : ∀ t, f (t + 1) ≤ f t + 1) :
    ∃ pages : Fin (2 * k) → Finset (ℕ × ℕ),
      (∀ c, Noncrossing (pages c)) ∧
      ∀ p u, DepStep xs T u p → f p < f u →
        f u = f p + 1 ∨ ∃ c, (f p, f u) ∈ pages c := by
  obtain ⟨pages, hp, hcover⟩ := walk_contracted_pages xs hx hf
  refine ⟨pages, hp, ?_⟩
  intro p u hdep hlt
  rcases hdep with ⟨rfl, -⟩ | hhop
  · left
    have := hstep p
    omega
  · exact Or.inr (hcover p u hhop hlt)

/-- Time windows preserve the two noncrossing pages per work head,
including last visits at the window's first step. -/
theorem timeWindow_dependency_pages {k T : ℕ} (xs : Fin k → ℕ → ℤ)
    (hx : ∀ j, IsWalk (xs j)) (h : ℕ) :
    ∃ pages : Fin (2 * k) → Finset (ℕ × ℕ),
      (∀ c, Noncrossing (pages c)) ∧
      ∀ p u, DepStep xs T u p → p / h < u / h →
        u / h = p / h + 1 ∨ ∃ c, (p / h, u / h) ∈ pages c := by
  apply contracted_dependency_pages xs hx
  · exact fun _ _ hab => Nat.div_le_div_right hab
  · intro t
    rw [Nat.succ_div]
    split_ifs <;> omega

end LeanBacklog.WindowPages

#print axioms LeanBacklog.WindowPages.contractPage_noncrossing
#print axioms LeanBacklog.WindowPages.timeWindow_dependency_pages
