import SubcubicMemo.SquareBoundaryCap

/-! Three common neighbors force a closed bipartite component, by the
same boundary argument used for the cube cap. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (h : Hyp G)
  {p q : V} (hpq : p ≠ q) (R : Finset V) (hcard : R.card = 3)
  (hp : ∀ a ∈ R, G.Adj p a) (hq : ∀ a ∈ R, G.Adj q a)

include h hcard in
theorem neighbor_mem_of_three {v : V} (hv : ∀ a ∈ R, G.Adj v a)
    {w : V} (hw : G.Adj v w) : w ∈ R := by
  have hsub : R ⊆ G.neighborFinset v := by
    intro a ha
    exact (G.mem_neighborFinset v a).mpr (hv a ha)
  have heq := eq_of_subset_of_card_le hsub (by
    rw [G.card_neighborFinset_eq_degree, hcard]
    exact h.degree v)
  rw [heq]
  exact (G.mem_neighborFinset v w).mpr hw

include h hpq hcard hp hq in
theorem hom_of_three_common (hconn : G.Preconnected) :
    Nonempty (G →g circularClique 8 3) := by
  have hpn : p ∉ R := fun hpr => G.irrefl (hp p hpr)
  have hqn : q ∉ R := fun hqr => G.irrefl (hq q hqr)
  have s : BoundarySeed (G := G) R {p, q} R :=
    { boundary := Subset.rfl
      card := hcard
      disjoint := by
        simp only [disjoint_insert_right, disjoint_singleton_right]
        exact ⟨hpn, hqn⟩
      independent := fun a ha b hb => no_triangle G h.triangle (hp a ha) (hp b hb)
      right := by
        intro u hu v huv
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with hu | hu
        · subst u; exact neighbor_mem_of_three h R hcard hp huv
        · subst u; exact neighbor_mem_of_three h R hcard hq huv
      internal := fun a ha hn => False.elim (hn ha)
      pair := fun a ha => ⟨p, by simp, q, by simp, hpq, (hp a ha).symm, (hq a ha).symm⟩ }
  exact s.hom h hconn

end SubcubicMemo.Squares
