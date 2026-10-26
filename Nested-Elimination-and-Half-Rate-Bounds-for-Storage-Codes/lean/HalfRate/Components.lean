import HalfRate.TheoremT

/-!
# Corollary T_int in its component form

The block form `rateBound_blocks` needs blocks listed so that parents lie in the same or an
earlier block. Instead of a topological order of the strongly connected components, we number
each vertex by the number of vertices that reach it (`ancestors`, `ancFibre`): an arc `u → v` never
decreases the count, and it keeps the count only inside a strongly connected component. The
fibres of the count, in increasing order, are the blocks; arcs inside a fibre stay inside one
component, so TT-freeness and the internal in-degrees of the fibres are those of the components.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] [Fintype V] {N : V → Finset V}

/-- `u` reaches `v` along arcs (an arc `a → b` means `a ∈ N b`). -/
def Reaches (N : V → Finset V) (u v : V) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ N b) u v

open Classical in
/-- The strongly connected component of `v`. -/
noncomputable def scc (N : V → Finset V) (v : V) : Finset V :=
  univ.filter (fun w => Reaches N w v ∧ Reaches N v w)

open Classical in
/-- The vertices that reach `v`. -/
noncomputable def ancestors (N : V → Finset V) (v : V) : Finset V :=
  univ.filter (fun w => Reaches N w v)

omit [DecidableEq V] in
theorem mem_ancestors {v w : V} : w ∈ ancestors N v ↔ Reaches N w v := by
  classical
  simp [ancestors]

omit [DecidableEq V] in
theorem mem_scc {v w : V} : w ∈ scc N v ↔ Reaches N w v ∧ Reaches N v w := by
  classical
  simp [scc]

omit [DecidableEq V] in
theorem ancestors_subset {u v : V} (h : u ∈ N v) : ancestors N u ⊆ ancestors N v := fun _ hw =>
  mem_ancestors.mpr ((mem_ancestors.mp hw).tail h)

omit [DecidableEq V] in
/-- An arc that keeps the ancestor count stays inside a strongly connected component. -/
theorem reaches_of_card_eq {u v : V} (h : u ∈ N v)
    (he : (ancestors N u).card = (ancestors N v).card) : Reaches N v u := by
  have heq := eq_of_subset_of_card_le (ancestors_subset h) he.ge
  have hv : v ∈ ancestors N v := mem_ancestors.mpr Relation.ReflTransGen.refl
  rw [← heq] at hv
  exact mem_ancestors.mp hv

/-- The fibre of the ancestor count at `c`. -/
noncomputable def ancFibre (N : V → Finset V) (c : ℕ) : Finset V :=
  univ.filter (fun v => (ancestors N v).card = c)

omit [DecidableEq V] in
theorem mem_ancFibre {c : ℕ} {v : V} : v ∈ ancFibre N c ↔ (ancestors N v).card = c := by
  simp [ancFibre]

omit [DecidableEq V] in
/-- Inside a fibre, every arc joins two vertices of one strongly connected component. -/
theorem mem_scc_of_fibre {c : ℕ} {u v : V} (hu : u ∈ ancFibre N c) (hv : v ∈ ancFibre N c)
    (h : u ∈ N v) : u ∈ scc N v :=
  mem_scc.mpr ⟨Relation.ReflTransGen.single h,
    reaches_of_card_eq h ((mem_ancFibre.mp hu).trans (mem_ancFibre.mp hv).symm)⟩

omit [Fintype V] in
theorem mem_foldr_union {L : List (Finset V)} {x : V} :
    x ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ L, x ∈ S := by
  induction L with
  | nil => simp
  | cons S L ih => simp [ih]

/-- The fibres listed along an increasing list of counts form a block order. -/
theorem blockOrder_fibres (hTT : ∀ v, TTFreeOn N (scc N v))
    (hT : IsAcyclicIn N (univ.filter (fun v => 3 ≤ (N v ∩ scc N v).card))) :
    ∀ cs : List ℕ, cs.Pairwise (· < ·) → BlockOrder N (cs.map (ancFibre N)) := by
  intro cs
  induction cs with
  | nil => intro _; trivial
  | cons c cs ih =>
    intro hcs
    obtain ⟨hlt, hcs'⟩ := List.pairwise_cons.mp hcs
    have hrest : ∀ x, x ∈ (cs.map (ancFibre N)).foldr (· ∪ ·) ∅ →
        c < (ancestors N x).card := by
      intro x hx
      obtain ⟨S, hS, hxS⟩ := mem_foldr_union.mp hx
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hS
      rw [mem_ancFibre.mp hxS]
      exact hlt c' hc'
    refine ⟨?_, ?_, ?_, ?_, ih hcs'⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      have := hrest x hx'
      rw [mem_ancFibre.mp hx] at this
      exact lt_irrefl _ this
    · intro v hv u hu hur
      have h1 := hrest u hur
      have h2 := card_le_card (ancestors_subset hu)
      rw [mem_ancFibre.mp hv] at h2
      omega
    · intro x hx y hy z hz hxy hyz hxz h1 h2 h3
      have hyz' := mem_scc_of_fibre hy hz h2
      have hxz' := mem_scc_of_fibre hx hz h3
      have hzz : z ∈ scc N z :=
        mem_scc.mpr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      exact hTT z x hxz' y hyz' z hzz hxy hyz hxz h1 h2 h3
    · refine hT.mono fun v hv => ?_
      obtain ⟨hvc, h3⟩ := mem_filter.mp hv
      refine mem_filter.mpr ⟨mem_univ _, h3.trans (card_le_card fun u hu => ?_)⟩
      obtain ⟨hu1, hu2⟩ := mem_inter.mp hu
      exact mem_inter.mpr ⟨hu1, mem_scc_of_fibre hu2 hvc hu1⟩

/-- **Corollary T_int.** A loopless relation none of whose strongly connected components contains
a transitive triangle, and whose vertices with at least three parents inside their own component
form an acyclic set, satisfies the weighted half bound. Parents outside a vertex's component are
unrestricted. -/
theorem rateBound_Tint (hloop : ∀ v, v ∉ N v) (hTT : ∀ v, TTFreeOn N (scc N v))
    (hT : IsAcyclicIn N (univ.filter (fun v => 3 ≤ (N v ∩ scc N v).card))) :
    RateBound N (1 / 2) := by
  refine rateBound_blocks hloop (blockOrder_fibres hTT hT (List.range (Fintype.card V + 1))
    (List.pairwise_lt_range)) ?_
  ext v
  simp only [mem_foldr_union, List.mem_map, List.mem_range, mem_univ, iff_true]
  refine ⟨ancFibre N (ancestors N v).card, ⟨_, ?_, rfl⟩, mem_ancFibre.mpr rfl⟩
  exact Nat.lt_succ_of_le (card_le_univ _)

end HalfRate
