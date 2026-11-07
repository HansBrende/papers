import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Push

/-! # Odd products preserve lower bounds on odd closed walks

An edge changes an odd number of coordinates, each along an edge of the base
graph. Coordinate projections delete stationary steps. The sum of their
lengths has the parity of the original walk, so an odd closed walk has an odd
closed coordinate projection of no greater length.
-/

namespace TapeStorageRates

open Finset
open scoped BigOperators

set_option autoImplicit false

variable {V I : Type*} [Fintype I] [DecidableEq V]

/-- The odd product allows a base edge or a stationary step in each coordinate,
with an odd number of nonstationary coordinates. -/
def oddProductGraph (G : SimpleGraph V) (I : Type*) [Fintype I] : SimpleGraph (I → V) where
  Adj x y := (∀ i, x i = y i ∨ G.Adj (x i) (y i)) ∧
    Odd ((univ.filter fun i => x i ≠ y i).card)
  symm := by
    constructor
    intro x y h
    refine ⟨fun i => (h.1 i).imp Eq.symm (fun hi => hi.symm), ?_⟩
    simpa only [ne_comm] using h.2
  loopless := by
    constructor
    intro x h
    simpa using h.2

instance oddProductGraphDecidableAdj (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (oddProductGraph G I).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ Odd _))

namespace OddProductGraph

variable {G : SimpleGraph V}

/-- Project to one base coordinate, deleting every stationary step. -/
def projectWalk {x y : I → V} (w : (oddProductGraph G I).Walk x y) (i : I) :
    G.Walk (x i) (y i) :=
  match w with
  | .nil => .nil
  | .cons h w =>
    if heq : _ = _ then (projectWalk w i).copy heq.symm rfl
    else .cons ((h.1 i).resolve_left heq) (projectWalk w i)

theorem projectWalk_length_le {x y : I → V}
    (w : (oddProductGraph G I).Walk x y) (i : I) :
    (projectWalk w i).length ≤ w.length := by
  induction w with
  | nil => simp [projectWalk]
  | @cons x y z h w ih =>
    by_cases heq : x i = y i <;> simp [projectWalk, heq] <;> omega

theorem projectWalk_length_cons {x y z : I → V}
    (h : (oddProductGraph G I).Adj x y) (w : (oddProductGraph G I).Walk y z) (i : I) :
    (projectWalk (.cons h w) i).length =
      (projectWalk w i).length + if x i = y i then 0 else 1 := by
  by_cases heq : x i = y i <;> simp [projectWalk, heq]

/-- The total number of coordinate moves has the parity of the product walk. -/
theorem sum_projectWalk_length_mod_two {x y : I → V}
    (w : (oddProductGraph G I).Walk x y) :
    (∑ i, (projectWalk w i).length) % 2 = w.length % 2 := by
  induction w with
  | nil => simp [projectWalk]
  | @cons x y z h w ih =>
    have hc : ((univ.filter fun i => x i ≠ y i).card) % 2 = 1 := Nat.odd_iff.mp h.2
    have heq : (∑ i, (projectWalk (.cons h w) i).length) =
        (∑ i, (projectWalk w i).length) + (univ.filter fun i => x i ≠ y i).card := by
      simp_rw [projectWalk_length_cons]
      rw [sum_add_distrib]
      congr 1
      simp only [card_filter, ite_not]
    rw [heq, Nat.add_mod, ih, hc, SimpleGraph.Walk.length_cons, Nat.add_mod]
    omega

/-- Every odd closed product walk has an odd closed base walk, based at one of
its starting coordinates and no longer than the original walk. -/
theorem exists_odd_closed_projection {x : I → V}
    (w : (oddProductGraph G I).Walk x x) (hw : Odd w.length) :
    ∃ i : I, Odd (projectWalk w i).length ∧ (projectWalk w i).length ≤ w.length := by
  have hsum : Odd (∑ i, (projectWalk w i).length) := by
    rw [Nat.odd_iff, sum_projectWalk_length_mod_two]
    exact Nat.odd_iff.mp hw
  by_contra h
  push Not at h
  have heven : Even (∑ i, (projectWalk w i).length) :=
    Finset.even_sum _ fun i _ => Nat.not_odd_iff_even.mp
      (fun hi => (not_lt_of_ge (projectWalk_length_le w i)) (h i hi))
  exact (Nat.not_even_iff_odd.mpr hsum) heven

/-- Any common strict lower bound on lengths of base odd closed walks survives
the odd product. -/
theorem odd_closed_length_gt {K : ℕ}
    (hG : ∀ v (w : G.Walk v v), Odd w.length → K < w.length)
    {x : I → V} (w : (oddProductGraph G I).Walk x x) (hw : Odd w.length) :
    K < w.length := by
  obtain ⟨i, hi, hle⟩ := exists_odd_closed_projection w hw
  exact (hG (x i) (projectWalk w i) hi).trans_le hle

section Degree

variable [Fintype V] [DecidableEq I] [DecidableRel G.Adj]

/-- The closed product neighbourhood fits in the product of the base closed
neighbourhoods. This also handles an empty coordinate index type. -/
theorem degree_add_one_le_product (x : I → V) :
    (oddProductGraph G I).degree x + 1 ≤ ∏ i, (G.degree (x i) + 1) := by
  classical
  let H := oddProductGraph G I
  let box := Fintype.piFinset fun i => insert (x i) (G.neighborFinset (x i))
  have hsub : insert x (H.neighborFinset x) ⊆ box := by
    intro y hy
    apply Fintype.mem_piFinset.mpr
    intro i
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_insert_self _ _
    · have hadj := (SimpleGraph.mem_neighborFinset H x y).mp hy
      rcases hadj.1 i with hi | hi
      · exact mem_insert.mpr (Or.inl hi.symm)
      · exact mem_insert.mpr (Or.inr ((G.mem_neighborFinset _ _).mpr hi))
  calc
    H.degree x + 1 = (insert x (H.neighborFinset x)).card := by
      rw [card_insert_of_notMem (H.notMem_neighborFinset_self x),
        SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ box.card := card_le_card hsub
    _ = ∏ i, (G.degree (x i) + 1) := by
      simp [box, card_insert_of_notMem (G.notMem_neighborFinset_self _),
        SimpleGraph.card_neighborFinset_eq_degree]

/-- A uniform base degree cap gives a product cap, with the centre excluded. -/
theorem degree_add_one_le_pow {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (x : I → V) :
    (oddProductGraph G I).degree x + 1 ≤ (D + 1) ^ Fintype.card I := by
  apply (degree_add_one_le_product x).trans
  simpa using (Finset.prod_le_prod (s := univ)
    (f := fun i => G.degree (x i) + 1) (g := fun _ => D + 1)
    (fun i _ => Nat.add_le_add_right (hD (x i)) 1))

theorem degree_le_pow {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (x : I → V) :
    (oddProductGraph G I).degree x ≤ (D + 1) ^ Fintype.card I :=
  (Nat.le_add_right _ _).trans (degree_add_one_le_pow hD x)

end Degree

end OddProductGraph

end TapeStorageRates
