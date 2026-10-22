import TransposeFollowup.LocalProtocol
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The actual interaction graph along one public transcript and the
canonical connected-component partition after removing a separator. -/

namespace TransposeFollowup

universe u v
set_option autoImplicit false

namespace PublicProtocol

variable {ι : Type u} {V : ι → Type v}

def querySupports : PublicProtocol ι V → List Bool → List (Finset ι)
  | .halt, _ => []
  | .query _ _, [] => []
  | .query q next, a :: m => q.support :: querySupports (next a) m

theorem along_iff_querySupports (p : PublicProtocol ι V) (P : Finset ι → Prop) (m : List Bool) :
    p.Along P m ↔ ∀ s ∈ p.querySupports m, P s := by
  induction p generalizing m with
  | halt => simp [Along, querySupports]
  | query q next ih =>
      cases m with
      | nil => simp [Along, querySupports]
      | cons a m => simp [Along, querySupports, ih]

/-- An edge is present exactly when the two distinct original rows occur
together in a query on this transcript. For Pairwise protocols, these are
exactly the two-row packet edges used in the manuscript. -/
def interactionGraph (p : PublicProtocol ι V) (m : List Bool) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ ∃ s ∈ p.querySupports m, i ∈ s ∧ j ∈ s
  symm := ⟨by
    intro i j h
    obtain ⟨hne, s, hs, hi, hj⟩ := h
    exact ⟨hne.symm, s, hs, hj, hi⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- Any labels constant on nonseparator edges yield a legal support partition.
No graph containing the supports of other transcripts is required. -/
theorem along_separated_of_graph_compatible {κ : Type*}
    (p : PublicProtocol ι V) (m : List Bool) (S : Finset ι) (component : ι → κ)
    (hcompat : ∀ i, i ∉ S → ∀ j, j ∉ S →
      (p.interactionGraph m).Adj i j → component i = component j) :
    p.Along (Separated S component) m := by
  classical
  apply (p.along_iff_querySupports _ m).mpr
  intro s hs
  by_cases hsub : s ⊆ S
  · exact Or.inl hsub
  · obtain ⟨i, hi, his⟩ := Finset.not_subset.mp hsub
    apply Or.inr
    refine ⟨component i, ?_⟩
    intro j hj
    by_cases hjs : j ∈ S
    · exact Or.inl hjs
    · apply Or.inr
      by_cases hji : j = i
      · exact congrArg component hji
      · exact hcompat j hjs i his ⟨hji, s, hs, hj, hi⟩

end PublicProtocol

def OutsideConnected {ι : Type*} (G : SimpleGraph ι) (S : Finset ι) (i j : ι) : Prop :=
  ∃ hi : i ∉ S, ∃ hj : j ∉ S,
    (G.induce {v | v ∉ S}).Reachable ⟨i, hi⟩ ⟨j, hj⟩

open Classical in
noncomputable def componentSet {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S : Finset ι) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => OutsideConnected G S i j)

theorem mem_componentSet {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S : Finset ι) (i j : ι) :
    j ∈ componentSet G S i ↔ OutsideConnected G S i j := by
  classical
  simp only [componentSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem componentSet_eq_of_outsideConnected {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S : Finset ι) {i j : ι} (h : OutsideConnected G S i j) :
    componentSet G S i = componentSet G S j := by
  classical
  obtain ⟨hi, hj, hij⟩ := h
  ext k
  rw [mem_componentSet, mem_componentSet]
  constructor
  · rintro ⟨_, hk, hik⟩
    exact ⟨hj, hk, hij.symm.trans hik⟩
  · rintro ⟨_, hk, hjk⟩
    exact ⟨hi, hk, hij.trans hjk⟩

theorem componentSet_compatible {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S : Finset ι) (i : ι) (hi : i ∉ S) (j : ι) (hj : j ∉ S)
    (hij : G.Adj i j) : componentSet G S i = componentSet G S j := by
  apply componentSet_eq_of_outsideConnected G S
  exact ⟨hi, hj, (show (G.induce {v | v ∉ S}).Adj ⟨i, hi⟩ ⟨j, hj⟩ from hij).reachable⟩

theorem componentSet_self_mem {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S : Finset ι) (i : ι) (hi : i ∉ S) :
    i ∈ componentSet G S i := by
  apply (mem_componentSet G S i i).mpr
  exact ⟨hi, hi, SimpleGraph.Reachable.refl _⟩

/-- The actual components of each leaf graph always satisfy the premise of
the separator theorem, including empty complements and empty separators. -/
theorem PublicProtocol.along_componentSet {ι : Type u} {V : ι → Type v} [Fintype ι]
    (p : PublicProtocol ι V) (m : List Bool) (S : Finset ι) :
    p.Along (PublicProtocol.Separated S (componentSet (p.interactionGraph m) S)) m :=
  p.along_separated_of_graph_compatible m S _ (componentSet_compatible _ S)

end TransposeFollowup
