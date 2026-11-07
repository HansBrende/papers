import MotionDepthCodes.Polymatroid
import TransposeFollowup.WeightedSubmodularCover

/-! # Packing the deficits of overlapping coordinate sets -/

namespace TapeStorageRates

open Finset MotionDepthCodes TransposeFollowup
open scoped BigOperators

set_option autoImplicit false

/-- The weighted deficits of a fractional packing cost at most its maximum load
times the global deficit. Each coordinate may use its own singleton capacity. -/
theorem patch_deficit_packing {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (cap : V → ℝ) (hcap : ∀ v, h {v} ≤ cap v)
    (P : J → Finset V) (weight : J → ℝ) (hw : ∀ j, 0 ≤ weight j) (r : ℝ)
    (hload : ∀ v, (∑ j, if v ∈ P j then weight j else 0) ≤ r) :
    ∑ j, weight j * ((∑ v ∈ P j, cap v) - h (P j)) ≤ r * ((∑ v, cap v) - h univ) := by
  classical
  let load (v : V) := ∑ j, if v ∈ P j then weight j else 0
  let slack (v : V) := r - load v
  let sets : J ⊕ V → Finset V := Sum.elim P fun v => {v}
  let weights : J ⊕ V → ℝ := Sum.elim weight slack
  have hs (v : V) : 0 ≤ slack v := sub_nonneg.mpr (hload v)
  have hc := weighted_submodular_cover univ h hh.empty hh.mono hh.submod sets
    (fun _ => subset_univ _) weights (fun a => by cases a <;> first | apply hw | apply hs)
    r (fun v _ => by
      rw [Fintype.sum_sum_type]
      change r ≤ load v + ∑ u : V, if v ∈ ({u} : Finset V) then slack u else 0
      simp [slack])
  simp only [sets, weights, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hc
  have hslack := sum_le_sum (s := (univ : Finset V)) fun v _ =>
    mul_le_mul_of_nonneg_left (hcap v) (hs v)
  have hsum : ∑ v, load v * cap v = ∑ j, weight j * ∑ v ∈ P j, cap v := by
    simp only [load, sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    simp [mul_sum]
  simp only [slack, sub_mul, sum_sub_distrib, ← mul_sum, hsum] at hslack hc
  simp only [mul_sub, sum_sub_distrib]
  linarith

end TapeStorageRates
