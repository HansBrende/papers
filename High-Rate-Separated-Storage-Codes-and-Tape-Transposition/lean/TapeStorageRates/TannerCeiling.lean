import MotionDepthCodes.StorageCode
import TransposeFollowup.UniformEntropy
import TransposeFollowup.SubmodularCover
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A finite ceiling for two-sheet local-code peeling

Edges are distinct coordinates with two distinct endpoints; parallel edges
are allowed. The code must satisfy the local projection bounds. A storage
code on the support of some selected checks need not satisfy this premise.
-/

namespace TapeStorageRates

open Finset MotionDepthCodes TransposeFollowup
open scoped BigOperators

set_option autoImplicit false
noncomputable section

variable {E V α : Type*} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

/-- Edges incident to a vertex, keeping parallel edges as distinct coordinates. -/
def endpointStar (left right : E → V) (v : V) : Finset E :=
  univ.filter fun e => left e = v ∨ right e = v

private theorem endpointStar_cover (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (e : E) :
    (∑ v, if e ∈ endpointStar left right v then (1 : ℝ) else 0) = 2 := by
  classical
  have h : univ.filter (fun v => e ∈ endpointStar left right v) =
      {left e, right e} := by
    ext v
    simp [endpointStar, eq_comm]
  rw [← sum_filter, h]
  simp [hne e]

private theorem sum_endpointStar_card (left right : E → V)
    (hne : ∀ e, left e ≠ right e) :
    (∑ v, ((endpointStar left right v).card : ℝ)) = 2 * Fintype.card E := by
  have h (v : V) : ((endpointStar left right v).card : ℝ) =
      ∑ e, if e ∈ endpointStar left right v then (1 : ℝ) else 0 := by
    rw [← sum_filter]
    simp
  simp_rw [h]
  rw [sum_comm]
  simp [endpointStar_cover left right hne, mul_comm]

variable [Fintype α] [Nontrivial α]

omit [Nontrivial α] in
open Classical in
/-- Shearer's bound retains the sum of actual local deficits. The local
assumption concerns the projection support of the supplied code itself. -/
theorem tanner_log_card_le_deficit (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (C : Finset (E → α)) (hC : C.Nonempty)
    (t : V → ℝ)
    (hlocal : ∀ v, Real.log ((C.image (view (endpointStar left right v))).card) ≤
      ((endpointStar left right v).card - t v) * Real.log (Fintype.card α)) :
    Real.log C.card ≤ (Fintype.card E - (∑ v, t v) / 2) *
      Real.log (Fintype.card α) := by
  classical
  let : Nonempty C := hC.to_subtype
  let p := uniformWeight C
  let X (x : C) := x.val
  have hh := codeEntropy_isPolymatroid p X (uniformWeight_nonneg C) (sum_uniformWeight C)
  have hcover := submodular_cover univ (codeEntropy p X) hh.empty hh.mono hh.submod
    (endpointStar left right) (fun _ => subset_univ _) 2
    (fun e _ => (endpointStar_cover left right hne e).ge)
  have hloc (v : V) : codeEntropy p X (endpointStar left right v) ≤
      ((endpointStar left right v).card - t v) * Real.log (Fintype.card α) := by
    apply (observationEntropy_le_log_support p (uniformWeight_nonneg C)
      (sum_uniformWeight C) (fun x => view (endpointStar left right v) (X x))
      (C.image (view (endpointStar left right v)))
      (fun x => mem_image_of_mem _ x.property)).trans
    exact hlocal v
  have hs := sum_le_sum (s := univ) fun v _ => hloc v
  have hsum : (∑ v, (((endpointStar left right v).card : ℝ) - t v) *
      Real.log (Fintype.card α)) =
      (2 * Fintype.card E - ∑ v, t v) * Real.log (Fintype.card α) := by
    rw [← sum_mul, sum_sub_distrib, sum_endpointStar_card left right hne]
  rw [hsum] at hs
  have hobs : codeEntropy p X univ = Real.log C.card := by
    change codeEntropy (fun _ : C => (Fintype.card C : ℝ)⁻¹)
      (fun x : C => x.val) univ = _
    rw [Fintype.card_coe]
    exact codeEntropy_univ_uniform C hC
  rw [hobs] at hcover
  nlinarith

open Classical in
/-- The same bound in alphabet-symbol units. -/
theorem tanner_logb_card_le_deficit (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (C : Finset (E → α)) (hC : C.Nonempty)
    (t : V → ℝ)
    (hlocal : ∀ v, Real.log ((C.image (view (endpointStar left right v))).card) ≤
      ((endpointStar left right v).card - t v) * Real.log (Fintype.card α)) :
    Real.logb (Fintype.card α) C.card ≤ Fintype.card E - (∑ v, t v) / 2 := by
  have ha : 0 < Real.log (Fintype.card α) :=
    Real.log_pos (by exact_mod_cast Fintype.one_lt_card (α := α))
  exact (div_le_iff₀ ha).mpr (tanner_log_card_le_deficit left right hne C hC t hlocal)

omit [Fintype α] [Nontrivial α] in
/-- Each edge is charged once, to a specified lifted vertex. -/
def twoSheetLoad (owner : E → V × Bool) (v : V) (i : Bool) : ℕ :=
  (univ.filter fun e => owner e = (v, i)).card

omit [Fintype α] [Nontrivial α] [DecidableEq E] in
theorem sum_twoSheetLoad (owner : E → V × Bool) :
    (∑ v, ∑ i, (twoSheetLoad owner v i : ℝ)) = Fintype.card E := by
  have h := sum_card_fiberwise_eq_card_filter
    (univ : Finset E) (univ : Finset (V × Bool)) owner
  simp only [mem_univ, filter_true, card_univ] at h
  have h' : (∑ v, ∑ i, twoSheetLoad owner v i) = Fintype.card E := by
    rw [Fintype.sum_prod_type] at h
    exact h
  exact_mod_cast h'

omit [Fintype α] [Nontrivial α] [DecidableEq E] in
/-- The actual once-per-edge load count pays at most two copies of each
vertex's local deficit. No incidence or ordering premise is needed here. -/
theorem twoSheetLoad_total_le (owner : E → V × Bool) (t : V → ℝ)
    (hload : ∀ v i, (twoSheetLoad owner v i : ℝ) ≤ t v) :
    (Fintype.card E : ℝ) ≤ 2 * ∑ v, t v := by
  rw [← sum_twoSheetLoad owner]
  calc
    _ ≤ ∑ v, ∑ i : Bool, t v :=
      sum_le_sum fun v _ => sum_le_sum fun i _ => hload v i
    _ = _ := by simp [mul_sum]

open Classical in
/-- Every edge is actually charged once. Two capacity slots per vertex and
local projection deficits therefore force the three-quarter ceiling.
Even an arbitrary assignment of edges to slots suffices for this bound. -/
theorem tanner_three_quarters_of_loads (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (C : Finset (E → α)) (hC : C.Nonempty)
    (t : V → ℝ) (owner : E → V × Bool)
    (hlocal : ∀ v, Real.log ((C.image (view (endpointStar left right v))).card) ≤
      ((endpointStar left right v).card - t v) * Real.log (Fintype.card α))
    (hload : ∀ v i, (twoSheetLoad owner v i : ℝ) ≤ t v) :
    Real.logb (Fintype.card α) C.card ≤ 3 * Fintype.card E / 4 := by
  have hcost := twoSheetLoad_total_le owner t hload
  have h := tanner_logb_card_le_deficit left right hne C hC t hlocal
  linarith

omit [Fintype α] [Nontrivial α] in
/-- Choose the earlier endpoint of each selected lifted edge. Ties select
the right endpoint; genuine strict orders have no endpoint ties. -/
def selectedEarlier (left right : E → V) (sheetLeft sheetRight : E → Bool)
    (position : V × Bool → ℝ) (e : E) : V × Bool :=
  if position (left e, sheetLeft e) < position (right e, sheetRight e)
  then (left e, sheetLeft e) else (right e, sheetRight e)

open Classical in
/-- The actual selected-edge version. The source code can be nonlinear;
only its star projections and the displayed selected-edge loads are used. -/
theorem tanner_three_quarters_of_lift (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (sheetLeft sheetRight : E → Bool)
    (position : V × Bool → ℝ) (C : Finset (E → α)) (hC : C.Nonempty)
    (t : V → ℝ)
    (hlocal : ∀ v, Real.log ((C.image (view (endpointStar left right v))).card) ≤
      ((endpointStar left right v).card - t v) * Real.log (Fintype.card α))
    (hload : ∀ v i,
      (twoSheetLoad (selectedEarlier left right sheetLeft sheetRight position) v i : ℝ) ≤ t v) :
    Real.logb (Fintype.card α) C.card ≤ 3 * Fintype.card E / 4 :=
  tanner_three_quarters_of_loads left right hne C hC t _ hlocal hload

open Classical in
/-- Actual local projection cardinalities imply the exact deficit bound.
The deficits may be real, and no linearity hypothesis is used. -/
theorem tanner_logb_card_le_of_local_sizes (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (C : Finset (E → α)) (hC : C.Nonempty)
    (t : V → ℝ)
    (hlocal : ∀ v, ((C.image (view (endpointStar left right v))).card : ℝ) ≤
      (Fintype.card α : ℝ) ^ (((endpointStar left right v).card : ℝ) - t v)) :
    Real.logb (Fintype.card α) C.card ≤ Fintype.card E - (∑ v, t v) / 2 := by
  have ha : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  apply tanner_logb_card_le_deficit left right hne C hC t
  intro v
  have hpos : (0 : ℝ) < (C.image (view (endpointStar left right v))).card := by
    exact_mod_cast (hC.image _).card_pos
  have h := Real.log_le_log hpos (hlocal v)
  rwa [Real.log_rpow ha] at h

open Classical in
/-- Actual local projection sizes and any once-per-edge two-slot assignment
suffice for the three-quarter ceiling. The assignment need not arise from
a lifted-edge order or assign an edge to one of its endpoints. -/
theorem tanner_three_quarters_of_local_sizes_and_loads (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (C : Finset (E → α)) (hC : C.Nonempty)
    (t : V → ℝ) (owner : E → V × Bool)
    (hlocal : ∀ v, ((C.image (view (endpointStar left right v))).card : ℝ) ≤
      (Fintype.card α : ℝ) ^ (((endpointStar left right v).card : ℝ) - t v))
    (hload : ∀ v i, (twoSheetLoad owner v i : ℝ) ≤ t v) :
    Real.logb (Fintype.card α) C.card ≤ 3 * Fintype.card E / 4 := by
  have h := tanner_logb_card_le_of_local_sizes left right hne C hC t hlocal
  have hcost := twoSheetLoad_total_le owner t hload
  linarith

open Classical in
/-- Nonlinear finite-code three-quarter ceiling from the actual local
projection sizes and the earlier-endpoint loads of selected lifted edges.
Neither a code dimension guarantee nor a support-only premise is substituted
for the local projection bounds. -/
theorem tanner_three_quarters_of_local_sizes (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (sheetLeft sheetRight : E → Bool)
    (position : V × Bool → ℝ) (C : Finset (E → α)) (hC : C.Nonempty)
    (t : V → ℝ)
    (hlocal : ∀ v, ((C.image (view (endpointStar left right v))).card : ℝ) ≤
      (Fintype.card α : ℝ) ^ (((endpointStar left right v).card : ℝ) - t v))
    (hload : ∀ v i,
      (twoSheetLoad (selectedEarlier left right sheetLeft sheetRight position) v i : ℝ) ≤ t v) :
    Real.logb (Fintype.card α) C.card ≤ 3 * Fintype.card E / 4 :=
  tanner_three_quarters_of_local_sizes_and_loads left right hne C hC t _ hlocal hload

end
end TapeStorageRates
