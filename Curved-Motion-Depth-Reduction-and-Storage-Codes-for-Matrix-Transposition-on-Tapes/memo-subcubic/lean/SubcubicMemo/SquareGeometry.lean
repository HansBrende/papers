import SubcubicMemo.SquareSupport
import MotionDepthCodes.CircularClique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Elementary graph inputs for square-covered subcubic components. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

structure Hyp : Prop where
  triangle : G.CliqueFree 3
  degree : ∀ v, G.degree v ≤ 3
  covered : ∀ u v, G.Adj u v → ∃ a b, Square G u v a b

theorem neighbors_eq_three (hdeg : ∀ v, G.degree v ≤ 3) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.neighborFinset v = {a, b, c} := by
  have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with h | h | h
    · subst w; exact (G.mem_neighborFinset v a).mpr ha
    · subst w; exact (G.mem_neighborFinset v b).mpr hb
    · subst w; exact (G.mem_neighborFinset v c).mpr hc
  have hn : ({a, b, c} : Finset V).card = 3 := by simp [hab, hac, hbc]
  exact (eq_of_subset_of_card_le hsub (by
    rw [hn, G.card_neighborFinset_eq_degree]
    exact hdeg v)).symm

theorem neighbor_of_three (hdeg : ∀ v, G.degree v ≤ 3) {v a b c w : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hw : G.Adj v w) :
    w = a ∨ w = b ∨ w = c := by
  have hm := (G.mem_neighborFinset v w).mpr hw
  rw [neighbors_eq_three G hdeg ha hb hc hab hac hbc] at hm
  simpa only [mem_insert, mem_singleton] using hm

theorem no_triangle (htri : G.CliqueFree 3) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) : ¬ G.Adj v w := by
  intro hvw
  exact htri {u, v, w} (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩)

theorem closed_reachable {S : Finset V}
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    {u v : V} (hu : u ∈ S) (hr : G.Reachable u v) : v ∈ S := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hu
  | @cons u w v h p ih => exact ih (hclosed u hu w h)

theorem closed_covers (hconn : G.Preconnected) {S : Finset V} (hne : S.Nonempty)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) : ∀ v, v ∈ S := by
  obtain ⟨u, hu⟩ := hne
  exact fun v => closed_reachable G hclosed hu (hconn u v)

theorem hom_of_closed_bipartition (hconn : G.Preconnected)
    (L R : Finset V) (hne : (L ∪ R).Nonempty) (hd : Disjoint L R)
    (hL : ∀ u ∈ L, ∀ v, G.Adj u v → v ∈ R)
    (hR : ∀ u ∈ R, ∀ v, G.Adj u v → v ∈ L) :
    Nonempty (G →g circularClique 8 3) := by
  have hcover : ∀ v, v ∈ L ∪ R := closed_covers G hconn hne (by
    intro u hu v huv
    rcases mem_union.mp hu with hu | hu
    · exact mem_union_right _ (hL u hu v huv)
    · exact mem_union_left _ (hR u hu v huv))
  refine ⟨{ toFun := fun v => if v ∈ L then (0 : Fin 8) else 3
            map_rel' := ?_ }⟩
  intro u v huv
  by_cases hu : u ∈ L
  · have hv : v ∉ L := fun hv => (disjoint_left.mp hd hv (hL u hu v huv))
    simp only [if_pos hu, if_neg hv]
    decide
  · have hur : u ∈ R := (mem_union.mp (hcover u)).resolve_left hu
    have hv : v ∈ L := hR u hur v huv
    simp only [if_neg hu, if_pos hv]
    decide

end SubcubicMemo.Squares
