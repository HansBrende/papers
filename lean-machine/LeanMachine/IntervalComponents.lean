import LeanMachine.ThinIntervals

/-! The hulls of connected components of a finite interval overlap graph
are exactly their interval unions, and distinct component hulls are disjoint.
No thinness or coloring assumption is needed.
-/

namespace LeanMachine.ThinIntervals.Model

open Classical Finset SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] (I : Model V)

abbrev Component := I.graph.ConnectedComponent

instance : Fintype I.Component := Fintype.ofFinite _

def componentVertices (c : I.Component) : Finset V :=
  univ.filter (fun v => I.graph.connectedComponentMk v = c)

theorem mem_componentVertices {c : I.Component} {v : V} :
    v ∈ I.componentVertices c ↔ I.graph.connectedComponentMk v = c := by
  simp [componentVertices]

theorem componentVertices_nonempty (c : I.Component) : (I.componentVertices c).Nonempty := by
  obtain ⟨v, hv⟩ := c.nonempty_supp
  exact ⟨v, (I.mem_componentVertices).mpr hv⟩

def componentLeft (c : I.Component) : ℕ :=
  (I.componentVertices c).inf' (I.componentVertices_nonempty c) I.left

def componentRight (c : I.Component) : ℕ :=
  (I.componentVertices c).sup' (I.componentVertices_nonempty c) I.right

theorem component_span_contains {c : I.Component} {v : V}
    (hv : v ∈ I.componentVertices c) :
    Set.Ioc (I.left v) (I.right v) ⊆ Set.Ioc (I.componentLeft c) (I.componentRight c) := by
  intro t ht
  exact ⟨(inf'_le _ hv).trans_lt ht.1, ht.2.trans (le_sup' _ hv)⟩

theorem component_span_exact (c : I.Component) (t : ℕ) :
    t ∈ Set.Ioc (I.componentLeft c) (I.componentRight c) ↔
      ∃ v ∈ I.componentVertices c, t ∈ Set.Ioc (I.left v) (I.right v) := by
  constructor
  · intro ht
    by_contra hn
    have hno : ∀ v ∈ I.componentVertices c, ¬ (I.left v < t ∧ t ≤ I.right v) := by
      simpa only [not_exists, not_and, Set.mem_Ioc] using hn
    obtain ⟨a, ha, hea⟩ := exists_mem_eq_inf' (I.componentVertices_nonempty c) I.left
    obtain ⟨b, hb, heb⟩ := exists_mem_eq_sup' (I.componentVertices_nonempty c) I.right
    have ha' : I.left a < t := by simpa only [componentLeft, hea] using ht.1
    have hb' : t ≤ I.right b := by simpa only [componentRight, heb] using ht.2
    have hra : I.right a < t := by have := hno a ha; omega
    have hr : I.graph.Reachable a b := ConnectedComponent.eq.mp
      ((I.mem_componentVertices.mp ha).trans (I.mem_componentVertices.mp hb).symm)
    obtain ⟨p⟩ := hr
    have prop : ∀ {u v} (p : I.graph.Walk u v),
        I.right u < t → v ∈ I.componentVertices c → I.right v < t := by
      intro u v p
      induction p with
      | nil => intro h _; exact h
      | cons hxy p ih =>
        intro hx hz
        rename_i x y z
        have hy : y ∈ I.componentVertices c := I.mem_componentVertices.mpr
          ((ConnectedComponent.sound p.reachable).trans (I.mem_componentVertices.mp hz))
        have hh := hno y hy
        have hyn : I.right y < t := by have := hxy.2.2; omega
        exact ih hyn hz
    exact (not_lt_of_ge hb') (prop p hra hb)
  · rintro ⟨v, hv, ht⟩
    exact I.component_span_contains hv ht

theorem component_spans_disjoint {c d : I.Component} (hcd : c ≠ d) :
    Disjoint (Ico (I.componentLeft c) (I.componentRight c))
      (Ico (I.componentLeft d) (I.componentRight d)) := by
  apply Finset.disjoint_left.mpr
  intro e he hd
  have hc' : e + 1 ∈ Set.Ioc (I.componentLeft c) (I.componentRight c) := by
    have := mem_Ico.mp he; constructor <;> omega
  have hd' : e + 1 ∈ Set.Ioc (I.componentLeft d) (I.componentRight d) := by
    have := mem_Ico.mp hd; constructor <;> omega
  obtain ⟨a, ha, hta⟩ := (I.component_span_exact c _).mp hc'
  obtain ⟨b, hb, htb⟩ := (I.component_span_exact d _).mp hd'
  apply hcd
  have hr : I.graph.Reachable a b := by
    by_cases hab : a = b
    · subst b; exact .refl _
    · exact (show I.graph.Adj a b from ⟨hab, hta.1.trans_le htb.2, htb.1.trans_le hta.2⟩).reachable
  exact (I.mem_componentVertices.mp ha).symm.trans
    ((ConnectedComponent.sound hr).trans (I.mem_componentVertices.mp hb))

end
end LeanMachine.ThinIntervals.Model
