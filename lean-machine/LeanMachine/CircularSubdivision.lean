import LeanMachine.WeightedCircularGap
import Mathlib.Data.Nat.Periodic

set_option autoImplicit false

/-!
# Real lengths on a finite circular subdivision

Vertices enumerate a finite subdivision, not an integer lattice in physical
space. A lifted coordinate advances by the real circumference each circuit.
Summing elementary edge lengths along a circular arc telescopes to its actual
endpoint displacement, including the seam and a full circuit.
-/

namespace LeanMachine.CircularSubdivision

open Finset CyclicSelection
open scoped BigOperators
noncomputable section

/-- Periodic lift of one circuit of real coordinates. -/
def lift (N : ℕ) (L : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  x (i % N) + (i / N : ℕ) * L

theorem lift_eq {N i : ℕ} (L : ℝ) (x : ℕ → ℝ) (hi : i < N) :
    lift N L x i = x i := by
  simp [lift, Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]

theorem lift_period {N : ℕ} (hN : 0 < N) (L : ℝ) (x : ℕ → ℝ) (i : ℕ) :
    lift N L x (i + N) = lift N L x i + L := by
  simp only [lift, Nat.add_mod_right, Nat.add_div_right _ hN, Nat.cast_add,
    Nat.cast_one]
  ring

theorem lift_eq_of_le {N i : ℕ} {L : ℝ} {x : ℕ → ℝ} (hN : 0 < N)
    (hx : x N = x 0 + L) (hi : i ≤ N) : lift N L x i = x i := by
  rcases lt_or_eq_of_le hi with hi | rfl
  · exact lift_eq L x hi
  · have h := lift_period hN L x 0
    simpa only [Nat.zero_add, lift_eq L x hN, hx] using h

def edgeLength (p : ℕ → ℝ) (i : ℕ) : ℝ := p (i + 1) - p i

/-- Any ordered finite real subdivision supplies nonnegative weights. -/
theorem edgeLength_lift_nonneg {N i : ℕ} {L : ℝ} {x : ℕ → ℝ} (hN : 0 < N)
    (hclose : x N = x 0 + L) (hx : ∀ j < N, x j ≤ x (j + 1)) (hi : i < N) :
    0 ≤ edgeLength (lift N L x) i := by
  rw [edgeLength, lift_eq_of_le hN hclose (show i + 1 ≤ N by omega), lift_eq L x hi]
  exact sub_nonneg.mpr (hx i hi)

theorem edgeLength_periodic {N : ℕ} {L : ℝ} {p : ℕ → ℝ}
    (hp : ∀ i, p (i + N) = p i + L) : Function.Periodic (edgeLength p) N := by
  intro i
  unfold edgeLength
  rw [show i + N + 1 = (i + 1) + N by omega, hp, hp]
  ring

/-- Summation on a circular arc uses each elementary edge exactly once. -/
theorem sum_arc {N a ell : ℕ} (hell : ell ≤ N) (w : ℕ → ℝ) :
    ∑ e ∈ arc N a ell, w e = ∑ k ∈ range ell, w ((a + k) % N) := by
  apply sum_image
  intro i hi j hj heq
  have hi' : a + i ∈ Ico a (a + N) := by
    have := mem_range.mp hi
    simp only [mem_Ico]
    omega
  have hj' : a + j ∈ Ico a (a + N) := by
    have := mem_range.mp hj
    simp only [mem_Ico]
    omega
  have := Nat.mod_injOn_Ico a N hi' hj' heq
  omega

/-- Real arc length is endpoint displacement in the lifted coordinates. -/
theorem arc_length {N a ell : ℕ} {L : ℝ} {p : ℕ → ℝ}
    (hp : ∀ i, p (i + N) = p i + L) (hell : ell ≤ N) :
    ∑ e ∈ arc N a ell, edgeLength p e = p (a + ell) - p a := by
  rw [sum_arc hell]
  simp_rw [(edgeLength_periodic hp).map_mod_nat]
  simpa only [edgeLength, Nat.add_assoc, Nat.add_zero] using
    sum_range_sub (fun k => p (a + k)) ell

theorem total_length {N : ℕ} {L : ℝ} {p : ℕ → ℝ}
    (hp : ∀ i, p (i + N) = p i + L) :
    ∑ e ∈ range N, edgeLength p e = L := by
  simp only [edgeLength, sum_range_sub]
  have := hp 0
  simpa only [Nat.zero_add, add_sub_cancel_left] using congrArg (fun a => a - p 0) this

/-- Weighted gaps are exactly the differences of successive lifted anchors. -/
theorem weightedGap_eq_displacement {N : ℕ} {L : ℝ} {p : ℕ → ℝ}
    (hp : ∀ i, p (i + N) = p i + L) {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) {i : ℕ} (hi : i < S.card) :
    WeightedCircularGap.weightedGap N S hS (edgeLength p) i =
      p (point N S hS (i + 1)) - p (point N S hS i) := by
  rw [WeightedCircularGap.weightedGap, WeightedCircularGap.edges,
    arc_length hp (gap_le hS hSN hi)]
  have hmono := point_mono hS hSN (Nat.le_succ i)
  rw [gap, Nat.add_sub_of_le hmono]

/-- The weighted model agrees with the usual sum of squared real gap lengths. -/
theorem area_eq_displacements {N : ℕ} {L : ℝ} {p : ℕ → ℝ}
    (hp : ∀ i, p (i + N) = p i + L) {S : Finset ℕ} (hS : S.Nonempty)
    (hSN : S ⊆ range N) :
    WeightedCircularGap.area N S hS (edgeLength p) =
      (∑ i ∈ range S.card,
        (p (point N S hS (i + 1)) - p (point N S hS i)) ^ 2) / (2 * L ^ 2) := by
  unfold WeightedCircularGap.area WeightedCircularGap.energy WeightedCircularGap.circumference
  rw [total_length hp]
  congr 1
  exact sum_congr rfl fun i hi =>
    congrArg (fun x : ℝ => x ^ 2) (weightedGap_eq_displacement hp hS hSN (mem_range.mp hi))

end
end LeanMachine.CircularSubdivision
