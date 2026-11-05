import TapeStorageRates.PatchesGeometry
import TapeStorageRates.PatchesEntropy
import TransposeFollowup.CoordinateEntropy
import SoftRecovery.Observations
import HalfRate.Pieces

/-!
# Partial prediction in overlapping coordinate patches

Disconnected paired ports supply a single piece for the soft decomposition
of Paper 7. Its residual terms measure what the allowed helpers in a patch
leave undetermined. All Shannon entropies below are in nats.
-/

namespace TapeStorageRates

open Finset DirectedRecovery HalfRate MotionDepthCodes SoftRecovery TransposeFollowup
open scoped BigOperators

set_option autoImplicit false

/-- Disconnected matched ports certify one elimination piece. A target owns
the record of its left component and reads the record of its right component. -/
theorem decomp_of_disconnected_pairs {V : Type*} [Fintype V] [DecidableEq V]
    (N : V → Finset V)
    (hsep : ∀ q, ¬(pairedIncidenceGraph N).Reachable (.inl q) (.inr q)) :
    Decomp N ∅ [univ] := by
  classical
  let κ := (pairedIncidenceGraph N).ConnectedComponent
  let : Fintype κ := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  let left (q : V) := e ((pairedIncidenceGraph N).connectedComponentMk (.inl q))
  let right (q : V) := e ((pairedIncidenceGraph N).connectedComponentMk (.inr q))
  let part (i : Fin (Fintype.card κ)) := univ.filter fun q => left q = i
  refine ⟨by simp, pieceCert_of_elim N ∅ univ part ?_ ?_ left right (fun _ => none)
    ?_ ?_ (by simp) ?_, by simp [Decomp]⟩
  · intro i j hij
    exact disjoint_filter.mpr fun _ _ hi hj => hij (hi.symm.trans hj)
  · ext q
    simp [part]
  · simp [part]
  · intro q _ h
    exact hsep q (SimpleGraph.ConnectedComponent.exact (e.injective h))
  · intro S _ hne
    obtain ⟨q, _, hq⟩ := not_subset.mp (fun h => hne (eq_univ_of_forall (fun x => h (mem_univ x))))
    refine ⟨q, mem_univ _, hq, ?_, by simp⟩
    intro _ u hu
    exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,
      congrArg e (incidence_components_eq hu)⟩))

/-- The local entropy bound holds for every polymatroid. Only the incidence
on the scored coordinates has to separate their paired ports. -/
theorem disconnected_patch_residual {V : Type*} [DecidableEq V]
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (P A : Finset V) (hAP : A ⊆ P)
    (B : V → Finset V) (hB : ∀ q ∈ A, B q ⊆ P)
    (hsep : ∀ q, ¬(pairedIncidenceGraph (inducedNeighborhood B A)).Reachable
      (.inl q) (.inr q)) :
    2 * (h P - h (P \ A)) ≤
      (∑ q ∈ A, increment h (P \ A) q) + ∑ q ∈ A, increment h (B q) q := by
  classical
  let f : A → V := Subtype.val
  let R := P \ A
  let M := inducedNeighborhood B A
  have him : univ.image f = A := Finset.attach_image_val
  have htot : univ.image f ∪ R = P := by rw [him]; exact union_sdiff_of_subset hAP
  have hsub (q : A) : B q ⊆ (M q).image f ∪ R := by
    intro u hu
    by_cases ha : u ∈ A
    · exact mem_union_left _ (mem_image.mpr ⟨⟨u,ha⟩,mem_subtype.mpr hu,rfl⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hB q q.2 hu,ha⟩)
  have hs := conditional_soft hh R f (decomp_of_disconnected_pairs M hsep)
  rw [htot] at hs
  have he (g : V → ℝ) : (∑ q : A, g q.val) = ∑ q ∈ A, g q :=
    (Finset.sum_subtype A (fun _ => Iff.rfl) g).symm
  have hn : (∑ q : A, increment h ((M q).image f ∪ R) (f q)) ≤
      ∑ q : A, increment h (B q.val) q.val :=
    sum_le_sum fun q _ => increment_antitone hh (hsub q) q.val
  rw [← he fun q => increment h (P \ A) q, ← he fun q => increment h (B q) q]
  exact hs.trans (add_le_add_right hn _)

/-- Fractional patch credit for any polymatroid and singleton capacities. Only
the paired ports of the scored coordinates inside each patch must be disconnected.
At capacity h{q} the left side is helper information and the right side is twice
the fractional load times the total correlation. -/
theorem weighted_patch_capacity {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (cap : V → ℝ) (hcap : ∀ q, h {q} ≤ cap q)
    (P A : J → Finset V) (B : J → V → Finset V) (weight : J → ℝ) (hw : ∀ j, 0 ≤ weight j)
    (r : ℝ) (hload : ∀ v, (∑ j, if v ∈ P j then weight j else 0) ≤ r)
    (hwithin : ∀ j, A j ⊆ P j) (hhelper : ∀ j, ∀ q ∈ A j, B j q ⊆ P j)
    (hsep : ∀ j q, ¬(pairedIncidenceGraph (inducedNeighborhood (B j) (A j))).Reachable
      (.inl q) (.inr q)) :
    ∑ j, weight j * ∑ q ∈ A j, (cap q - increment h (B j q) q) ≤
      r * (((∑ q, cap q) - h univ) + ((∑ q, h {q}) - h univ)) := by
  classical
  have localBound (j : J) : (∑ q ∈ A j, (cap q - increment h (B j q) q)) ≤
      ((∑ q ∈ P j, cap q) - h (P j)) + ((∑ q ∈ P j, h {q}) - h (P j)) := by
    have hl := disconnected_patch_residual hh (P j) (A j) (hwithin j) (B j) (hhelper j) (hsep j)
    have hout := hh.le_sum_singleton (P j \ A j)
    have hother := hout.trans (sum_le_sum fun q _ => hcap q)
    have hin := sum_le_sum (s := A j) fun q _ => increment_le_singleton hh (P j \ A j) q
    rw [sum_sub_distrib, ← sum_sdiff (f := cap) (hwithin j), ← sum_sdiff (f := fun q => h {q}) (hwithin j)]
    linarith only [hl, hout, hother, hin]
  have hs := sum_le_sum (s := (univ : Finset J)) fun j _ =>
    mul_le_mul_of_nonneg_left (localBound j) (hw j)
  simp only [mul_add, sum_add_distrib] at hs ⊢
  exact hs.trans (add_le_add (patch_deficit_packing hh cap hcap P weight hw r hload)
    (patch_deficit_packing hh (fun q => h {q}) (fun _ => le_rfl) P weight hw r hload))

/-- A distance test supplies the local disconnection certificate. Its radius only
counts the scored coordinates, so helper patches can be arbitrarily large. -/
theorem patch_capacity_of_long_targets {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (cap : V → ℝ) (hcap : ∀ q, h {q} ≤ cap q)
    (N : V → Finset V) (P A : J → Finset V) (B : J → V → Finset V) (w r : ℕ)
    (hsize : ∀ j, (A j).card ≤ w) (hload : ∀ v, (univ.filter fun j => v ∈ P j).card ≤ r)
    (hwithin : ∀ j, A j ⊆ P j) (hhelper : ∀ j, ∀ q ∈ A j, B j q ⊆ N q ∩ P j)
    (hfar : ∀ j, ∀ q ∈ A j, q ∉ shortPairedCoordinates N (2*w-1)) :
    (∑ j, ∑ q ∈ A j, (cap q - increment h (B j q) q)) ≤
      r * (((∑ q, cap q) - h univ) + ((∑ q, h {q}) - h univ)) := by
  classical
  simpa only [one_mul] using weighted_patch_capacity hh cap hcap P A B (fun _ => 1)
    (fun _ => zero_le_one) r (fun v => by simpa using hload v) hwithin
    (fun j q hq => (hhelper j q hq).trans inter_subset_right) (fun j q hr =>
      hfar j q q.2 (reachable_pair_short N _ Subtype.val (fun v u hu =>
        (mem_inter.mp (hhelper j v v.2 (mem_subtype.mp hu))).1) q (by simpa using hsize j) hr))

theorem bit_coordinate_polymatroid {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (X : Ω → V → Bool) :
    IsPolymatroid (coordinateEntropy p X) :=
  ⟨coordinateEntropy_empty p hp1 X, coordinateEntropy_mono p hp X, coordinateEntropy_submodular p hp X⟩

/-- The unit-bit bound. Each residual is the conditional entropy of its scored target
given its permitted helpers. The same bit may be scored in several patches. -/
theorem patch_prediction_entropy {Ω V J : Type*} [Fintype Ω] [Fintype V]
    [DecidableEq V] [Fintype J] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (X : Ω → V → Bool) (N : V → Finset V)
    (P A : J → Finset V) (B : J → V → Finset V) (w r : ℕ)
    (hsize : ∀ j, (A j).card ≤ w)
    (hload : ∀ v, (univ.filter fun j => v ∈ P j).card ≤ r)
    (hwithin : ∀ j, A j ⊆ P j)
    (hhelper : ∀ j, ∀ q ∈ A j, B j q ⊆ N q ∩ P j)
    (hfar : ∀ j, ∀ q ∈ A j, q ∉ shortPairedCoordinates N (2*w-1)) :
    (∑ j, ∑ q ∈ A j, (Real.log 2 -
      (coordinateEntropy p X (insert q (B j q)) - coordinateEntropy p X (B j q)))) ≤
      2 * (r : ℝ) * (Fintype.card V * Real.log 2 - observationEntropy p X) := by
  have hcap (q : V) : coordinateEntropy p X {q} ≤ Real.log 2 := by
    simpa using coordinateEntropy_le_card p hp hp1 X {q}
  have H := patch_capacity_of_long_targets (bit_coordinate_polymatroid p hp hp1 X) (fun _ => Real.log 2)
    hcap N P A B w r hsize hload hwithin hhelper hfar
  have hm := mul_le_mul_of_nonneg_left (sum_le_sum (s := univ) fun q _ => hcap q) (Nat.cast_nonneg r (α := ℝ))
  simp only [increment, coordinateEntropy_univ, sum_const, card_univ, nsmul_eq_mul] at H hm
  linarith only [H, hm]

end TapeStorageRates
