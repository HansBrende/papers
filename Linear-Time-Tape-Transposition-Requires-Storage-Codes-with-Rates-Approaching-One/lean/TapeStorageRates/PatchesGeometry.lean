import DirectedRecovery.IncidenceSeparator

/-!
# Long paired distances inside a recovery patch

The local decoder may use any subset of the permitted helpers contained in
its patch. Conditioning on the other patch coordinates gives a relation on
the long targets alone. Every incidence there maps back to the ambient graph.
-/

namespace TapeStorageRates

open Finset DirectedRecovery

set_option autoImplicit false

/-- A color shared across each helper incidence and separating every
matched pair rules out a paired path of any finite length. -/
theorem shortPairedCoordinates_eq_empty_of_colors {V κ : Type*} [Fintype V] [DecidableEq V]
    (N : V → Finset V) (left right : V → κ) (hsep : ∀ q, left q ≠ right q)
    (hcolor : ∀ q u, u ∈ N q → left u = right q) (t : ℕ) :
    shortPairedCoordinates N t = ∅ := by
  classical
  let color : V ⊕ V → κ := Sum.elim left right
  have hedge {u v} (h : (pairedIncidenceGraph N).Adj u v) : color u = color v := by
    cases u <;> cases v with
    | inl v => first | exact h.elim | exact (hcolor _ _ h).symm
    | inr v => first | exact hcolor _ _ h | exact h.elim
  have hwalk {u v} (p : (pairedIncidenceGraph N).Walk u v) : color u = color v := by
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hedge h).trans ih
  have hd (q : V) : (pairedIncidenceGraph N).edist (.inl q) (.inr q) = ⊤ := by
    apply SimpleGraph.edist_eq_top_of_not_reachable
    rintro ⟨p⟩
    exact hsep q (hwalk p)
  ext q
  simp [shortPairedCoordinates, hd]

/-- A reachable local pair has an ambient path of length at most twice the
number of local coordinates minus one. The coordinate map need not be injective. -/
theorem reachable_pair_short {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (N : V → Finset V) (M : W → Finset W)
    (e : W → V) (hsub : ∀ q u, u ∈ M q → e u ∈ N (e q)) (q : W) {w : ℕ}
    (hsize : Fintype.card W ≤ w)
    (hr : (pairedIncidenceGraph M).Reachable (Sum.inl q) (Sum.inr q)) :
    e q ∈ shortPairedCoordinates N (2 * w - 1) := by
  classical
  let f : pairedIncidenceGraph M →g pairedIncidenceGraph N :=
    { toFun := Sum.map e e
      map_rel' := by
        rintro (a | a) (b | b) hab
        · exact hab.elim
        · exact hsub b a hab
        · exact hsub a b hab
        · exact hab.elim }
  obtain ⟨p, hp⟩ := hr.exists_isPath
  have hlen := hp.length_lt
  rw [Fintype.card_sum] at hlen
  have hdist : (pairedIncidenceGraph N).edist (f (Sum.inl q)) (f (Sum.inr q)) ≤
      (2 * w - 1 : ℕ) := calc
    _ ≤ ((p.map f).length : ℕ∞) := (pairedIncidenceGraph N).edist_le (p.map f)
    _ = (p.length : ℕ∞) := by rw [SimpleGraph.Walk.length_map]
    _ ≤ _ := by exact_mod_cast (by omega : p.length ≤ 2 * w - 1)
  exact mem_filter.mpr ⟨mem_univ _, hdist⟩

end TapeStorageRates
