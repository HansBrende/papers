import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite graph balls under a maximum-degree bound

The balls use extended distance, so disconnected vertices never contribute
at a finite radius. The proof counts actual shortest-walk prefixes, rather
than assuming a neighborhood-growth estimate.
-/

namespace LeanMachine.GraphBall

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The closed graph-distance ball of a natural radius. -/
noncomputable def closedBall (z : V) (r : ℕ) : Finset V :=
  Finset.univ.filter (fun v => G.edist z v ≤ (r : ℕ∞))

omit [DecidableRel G.Adj] in
@[simp] theorem closedBall_zero (z : V) : closedBall G z 0 = {z} := by
  ext v
  simp only [closedBall, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_zero,
    nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff, Finset.mem_singleton]
  exact eq_comm

/-- A positive-radius ball is covered by its center and the preceding-radius
balls centered at its neighbors. -/
theorem closedBall_succ_subset (z : V) (r : ℕ) :
    closedBall G z (r + 1) ⊆
      insert z ((G.neighborFinset z).biUnion (fun u => closedBall G u r)) := by
  intro v hv
  have hd : G.edist z v ≤ ((r + 1 : ℕ) : ℕ∞) := (Finset.mem_filter.mp hv).2
  have htop : G.edist z v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hd
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
  have hlen : p.length ≤ r + 1 := by
    rw [← hp] at hd
    exact_mod_cast hd
  cases p with
  | nil => exact Finset.mem_insert_self _ _
  | @cons z u v hzu p =>
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨u, (G.mem_neighborFinset z u).mpr hzu, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hpLen : p.length ≤ r := by
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega
    exact p.edist_le.trans (by exact_mod_cast hpLen)

private theorem geometric_recurrence (D r : ℕ) :
    D * (∑ j ∈ Finset.range (r + 1), D ^ j) + 1 =
      ∑ j ∈ Finset.range (r + 2), D ^ j := by
  conv_rhs => rw [show r + 2 = (r + 1) + 1 by omega, Finset.sum_range_succ']
  simp_rw [pow_succ', ← Finset.mul_sum]
  simp

/-- The exact elementary degree bound, also valid for degree zero. -/
theorem card_closedBall_le (Δ : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ) (z : V) (r : ℕ) :
    (closedBall G z r).card ≤ ∑ j ∈ Finset.range (r + 1), Δ ^ j := by
  induction r generalizing z with
  | zero => simp
  | succ r ih =>
    calc
      (closedBall G z (r + 1)).card ≤
          (insert z ((G.neighborFinset z).biUnion (fun u => closedBall G u r))).card :=
        Finset.card_le_card (closedBall_succ_subset G z r)
      _ ≤ ((G.neighborFinset z).biUnion (fun u => closedBall G u r)).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (∑ u ∈ G.neighborFinset z, (closedBall G u r).card) + 1 :=
        Nat.add_le_add_right Finset.card_biUnion_le 1
      _ ≤ (∑ _u ∈ G.neighborFinset z, ∑ j ∈ Finset.range (r + 1), Δ ^ j) + 1 :=
        Nat.add_le_add_right (Finset.sum_le_sum (fun u _ => ih u)) 1
      _ = G.degree z * (∑ j ∈ Finset.range (r + 1), Δ ^ j) + 1 := by simp
      _ ≤ Δ * (∑ j ∈ Finset.range (r + 1), Δ ^ j) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ (hdegree z)) 1
      _ = ∑ j ∈ Finset.range (r + 2), Δ ^ j := geometric_recurrence Δ r

/-- The radius-ball bound in the exact form used by short-path packing.
The center-to-vertex distance is Mathlib's extended distance. -/
theorem card_edist_le (Δ : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ) (z : V) (r : ℕ) :
    (Finset.univ.filter (fun v => G.edist z v ≤ (r : ℕ∞))).card ≤
      ∑ j ∈ Finset.range (r + 1), (max 1 Δ) ^ j :=
  card_closedBall_le G (max 1 Δ) (fun v => (hdegree v).trans (le_max_right 1 Δ)) z r

end LeanMachine.GraphBall
